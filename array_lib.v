(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2020 monae authors, license: LGPL-2.1-or-later               *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require boolp.
Require Import monae_lib.
From HB Require Import structures.
Require Import hierarchy monad_lib fail_lib.

(******************************************************************************)
(*                Definitions and lemmas about the array monad                *)
(*                                                                            *)
(*           aswap i j == swap the cells at addresses i and j; this is a      *)
(*                        computation of type (M unit)                        *)
(*       writeList i s == write the list s at address i; this is a            *)
(*                        computation of type (M unit)                        *)
(*          writeL i s := writeList i s >> Ret (size s)                       *)
(*    write2L i (s, t) := writeList i (s ++ t) >> Ret (size s, size t)        *)
(* write3L i (s, t, u) := writeList i (s ++ t ++ u) >>                        *)
(*                        Ret (size s, size t, size u)                        *)
(*        readList i n == read the list of values of size n starting at       *)
(*                        address i; it is a computation of type (M (seq E))  *)
(*                        where E is the type of stored elements              *)
(*                                                                            *)
(******************************************************************************)

Local Open Scope monae_scope.

Section aswap.
Context {S : Type} (I : eqType) {M : arrayMonad S I}.

Definition aswap i j : M unit :=
  aget i >>= (fun x => aget j >>= (fun y => aput i y >> aput j x)).

Lemma aswapxx i : aswap i i = skip :> M unit.
Proof.
rewrite /aswap agetget.
under eq_bind do rewrite aputput.
by rewrite agetputskip.
Qed.

End aswap.
Arguments aswap {S I M}.

Section write_read.
Context {S : Type} {M : arrayMonad S nat}.
Implicit Type i j : nat.

Import Order.POrderTheory.

Fixpoint writeList i (s : seq S) : M unit :=
  if s is x :: xs then aput i x >> writeList i.+1 xs else Ret tt.
#[global] Arguments writeList : simpl never.

Lemma writeList_nil i : writeList i [::] = Ret tt.
Proof. by []. Qed.

Lemma writeList_cons i (x : S) (xs : seq S) :
  writeList i (x :: xs) = aput i x >> writeList i.+1 xs.
Proof. by []. Qed.

Definition writeListE := (writeList_nil, writeList_cons).

Lemma writeList1 i (x : S) : writeList i [:: x] = aput i x.
Proof. by rewrite writeList_cons bindmskip. Qed.

Lemma aput_writeListC i j (x : S) (xs : seq S) : i < j ->
  aput i x >> writeList j xs = writeList j xs >> aput i x.
Proof.
elim: xs i j => [|h tl ih] i j ij /=; first by rewrite bindmskip bindretf.
rewrite -bindA aputC; last by left; rewrite lt_eqF.
by rewrite !bindA; bind_ext => -[]; rewrite ih// ltnW.
Qed.

Lemma writeListC i j (ys zs : seq S) : i + size ys <= j ->
  writeList i ys >> writeList j zs = writeList j zs >> writeList i ys.
Proof.
elim: ys zs i j => [|h t ih] zs i j hyp /=; first by rewrite bindretf bindmskip.
rewrite writeList_cons aput_writeListC// bindA aput_writeListC; last first.
  by rewrite (leq_trans _ hyp)//= -addSnnS ltn_addr.
rewrite -!bindA ih// addSn.
by rewrite /= addnS in hyp.
Qed.

Lemma aput_writeListCR i j (x : S) (xs : seq S) : j + size xs <= i ->
  aput i x >> writeList j xs = writeList j xs >> aput i x.
Proof. by move=> jxsu; rewrite -writeList1 -[LHS]writeListC. Qed.

Lemma writeList_cat i (s1 s2 : seq S) :
  writeList i (s1 ++ s2) = writeList i s1 >> writeList (i + size s1) s2.
Proof.
elim: s1 i => [|h t ih] i/=; first by rewrite addn0 bindretf.
by rewrite writeList_cons ih bindA addSnnS.
Qed.

Lemma writeList_rcons i (x : S) (xs : seq S) :
  writeList i (rcons xs x) = writeList i xs >> aput (i + size xs) x.
Proof. by rewrite -cats1 writeList_cat /= -bindA bindmskip. Qed.

Definition writeL i (s : seq S) := writeList i s >> Ret (size s).

Definition write2L i '(s, t) := writeList i (s ++ t) >> Ret (size s, size t).

Lemma write2LE i a b D (f : nat * nat -> M D) :
  write2L i (a, b) >>= f = writeList i (a ++ b) >> f (size a, size b).
Proof. by rewrite /write2L bindA bindretf. Qed.

Definition write3L i '(s, t, u) :=
  writeList i (s ++ t ++ u) >> Ret (size s, size t, size u).

Lemma write3LE i x D (f : nat * nat * nat -> M D) :
  write3L i x >>= f = let '(s, t, u) := x in
    writeList i (s ++ t ++ u) >> f (size s, size t, size u).
Proof. by move: x => -[[x y] z]; rewrite /write3L bindA bindretf. Qed.

Lemma write_read i x : aput i x >> aget i = aput i x >> Ret x :> M _.
Proof. by rewrite -[RHS]aputget bindmret. Qed.

Lemma write_readC i j x : i != j ->
  aput i x >> aget j = aget j >>= (fun v => aput i x >> Ret v) :> M _.
Proof. by move => ?; rewrite -aputgetC // bindmret. Qed.

(* see postulate introduce-read in IQsort.agda *)
Lemma writeListRet i x (s : seq S) :
  writeList i (x :: s) >> Ret x = writeList i (x :: s) >> aget i.
Proof.
elim/last_ind: s x i => [|h t ih] /= x i.
  by rewrite writeList1 write_read.
rewrite writeList_cons writeList_rcons 2![in RHS]bindA.
rewrite write_readC; last by rewrite gtn_eqF// ltn_addr.
rewrite -2![RHS]bindA -ih [RHS]bindA.
rewrite !bindA; bind_ext => _.
by under [in RHS]eq_bind do rewrite bindretf.
Qed.

Lemma writeList_aswap i x h (t : seq S) :
  writeList i (rcons (h :: t) x) =
  writeList i (rcons (x :: t) h) >> aswap i (i + size (rcons t h)).
Proof.
rewrite /aswap -!bindA writeList_rcons /=.
rewrite writeList_cons aput_writeListC// bindA.
rewrite writeList_cons aput_writeListC// writeList_rcons !bindA.
bind_ext => -[].
under [RHS] eq_bind do rewrite -bindA.
rewrite aputget -bindA size_rcons addSnnS.
under [RHS] eq_bind do rewrite -!bindA.
rewrite aputgetC; last by rewrite -addSnnS ltn_eqF// ltn_addr.
rewrite -!bindA aputget aputput aputC; last by right.
by rewrite bindA aputput.
Qed.

Lemma aput_writeList_rcons i x h (t : seq S) :
  aput i x >> writeList i.+1 (rcons t h) =
  aput i h >>
      ((writeList i.+1 t >> aput (i + (size t).+1) x) >>
        aswap i (i + (size t).+1)).
Proof.
rewrite /aswap -!bindA writeList_rcons -bindA.
rewrite aput_writeListC// aput_writeListC// !bindA; bind_ext => -[].
under [RHS] eq_bind do rewrite -bindA.
rewrite aputgetC; last by rewrite gtn_eqF// -addSnnS ltn_addr.
rewrite -bindA aputget.
under [RHS] eq_bind do rewrite -!bindA.
rewrite aputget aputC; last by right.
by rewrite -!bindA aputput bindA aputput -addSnnS.
Qed.

Lemma writeList_ret_aget i x (s : seq S) (f : S -> M (nat * nat)%type):
  writeList i (x :: s) >> Ret x >> f x =
  writeList i (x :: s) >> aget i >>= f.
Proof.
rewrite writeListRet 2!bindA /= writeList_cons aput_writeListC// 2!bindA.
under [LHS] eq_bind do rewrite -bindA aputget.
by under [RHS] eq_bind do rewrite -bindA aputget.
Qed.

Fixpoint readList i (n : nat) : M (seq S) :=
  if n isn't k.+1 then Ret [::] else liftM2 cons (aget i) (readList i.+1 k).

End write_read.

Section refin_writeList_aswap.
Variable (d : unit) (E : orderType d) (M : plusArrayMonad E nat).

(* eqn 13 in mu2020flops, postulate introduce-swap in IQSort.agda *)
Lemma refin_writeList_cons_aswap (i : nat) x (s : seq E) :
  writeList i (x :: s) >> aswap (M := M) i (i + size s)
  `<=`
  qperm s >>= (fun s' => writeList i (rcons s' x)).
Proof.
elim/last_ind: s => [|t h ih] /=.
  rewrite qperm_nil writeList1 bindretf addn0 aswapxx /= bindmskip writeList1.
  exact: refin_refl.
rewrite bindA.
apply: (refin_trans _ (refin_bindr _ (qperm_refin_cons _ _ _))).
by rewrite bindretf -bindA -writeList_aswap; exact: refin_refl.
Qed.

(* eqn 11 in mu2020flops, introduce-swap in IPartl.agda *)
Lemma refin_writeList_rcons_aswap (i : nat) x (s : seq E) :
  writeList i (rcons s x) >> aswap (M := M) i (i + size s)
  `<=`
  qperm s >>= (fun s' => writeList (M := M) i (x :: s')).
Proof.
case: s => [|h t] /=.
  rewrite qperm_nil writeList1 bindretf addn0 aswapxx writeList1 bindmskip.
  exact: refin_refl.
rewrite writeList_cons bindA writeList_rcons addSnnS -aput_writeList_rcons.
apply: (refin_trans _ (refin_bindr _ (qperm_refin_rcons _ _ _))).
by rewrite bindretf; exact: refin_refl.
Qed.

(* bottom of the page 11, used in the proof of lemma 10 *)
Lemma refin_writeList_rcons_cat_aswap (i : nat) x (ys zs : seq E) :
  writeList i (rcons (ys ++ zs) x) >>
    aswap (M := M) (i + size ys) (i + size (ys ++ zs))
  `<=`
  qperm zs >>= (fun zs' => writeList i (ys ++ x :: zs')).
Proof.
under [in X in _ `<=` X]eq_bind do rewrite writeList_cat.
rewrite (plus_commute (qperm zs))//.
rewrite rcons_cat writeList_cat bindA.
apply: refin_bindl => -[]; rewrite size_cat/= addnA.
exact: refin_writeList_rcons_aswap.
Qed.

End refin_writeList_aswap.
