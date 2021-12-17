(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2020 monae authors, license: LGPL-2.1-or-later               *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require boolp.
Require Import monae_lib hierarchy monad_lib fail_lib state_lib.
Require Import array_lib example_quicksort.
From infotheo Require Import ssr_ext.

(******************************************************************************)
(*                  Quicksort with the Array Monad (WIP)                      *)
(*                                                                            *)
(*    partl p (s, t) u == partition u into (x, y) w.r.t. pivot p and returns  *)
(*                        (s ++ x, t ++ y)                                    *)
(*    tr_partl p s t u == tail-recursive version of partl; this is a          *)
(*                        computation of type M (seq E * seq E * seq E) where *)
(*                        E is the type of the values in the array monad      *)
(* ipartl p i ny nz nx == partition the array stored at i w.r.t. the pivot p, *)
(*                        the array is yz ++ zs ++ xs where the lengths of    *)
(*                        yz, zs, xs are resp. ny, nz, nx; it returns the     *)
(*                        lengths of the partitions this is a computation of  *)
(*                        of type M (nat * nat)                               *)
(*   dipartl p i y z x == same as ipartl except that it returns a dependent   *)
(*                        pair of type                                        *)
(*                        {(a, b)| a <= x + y + z && b <= x + y +z}           *)
(*       iqsort (i, n) == quicksort the list of size n stored from address i  *)
(*                                                                            *)
(*                                                                            *)
(* Reference:                                                                 *)
(* - [1] Shin-Cheng Mu, Tsung-Ju Chiang, Declarative Pearl: Deriving Monadic  *)
(*       Quicksort, FLOPS 2020                                                *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope order_scope.
Import Order.Theory.
Local Open Scope monae_scope.
Local Open Scope tuple_ext_scope.

From infotheo Require Import ssrZ.
Require Import ZArith.

(* TODO: equip Z with an ssr order *)
Lemma neq_Zlt (a b : Z) : (a != b) <-> (a < b)%Z \/ (b < a)%Z.
Proof.
split => [/eqP/not_Zeq//|[ab|ba]].
- exact/eqP/ltZ_eqF.
- exact/eqP/gtZ_eqF.
Qed.

(* TODO: move to infotheo *)
Lemma addZAC : right_commutative Zplus. Proof. by move=> ? ? ?; ring. Qed.

Lemma addZCA : left_commutative Zplus. Proof. by move=> ? ? ?; ring. Qed.

Definition apply_pair_snd (M : monad) (A B C : UU0) (f : B -> M C) (ab : A * B)
    : M (A * C)%type :=
  f ab.2 >>= (fun c => Ret (ab.1, c)).

Lemma apply_pair_snd_uncurry3 (M : monad) (A B B' C D : UU0) (f : B -> M B')
  (a : A) (b : B) (c : C) (g : A -> B' -> C -> M D) :
  apply_pair_snd f (a, b) >>= (fun x => uncurry3 g (x, c)) =
  f b >>= g a ^~ c.
Proof.
rewrite /apply_pair_snd /= bindA; bind_ext => b'.
by rewrite bindretf.
Qed.

Definition apply_triple_snd (M : monad) (A B C D : UU0) (f : B -> M D)
    (abc : A * B * C) : M (A * D * C)%type :=
  f abc.1.2 >>= (fun d => Ret (abc.1.1, d, abc.2)).

Lemma apply_triple_sndE (M : monad) (A B C D : UU0) (f : B -> M D) (a : A)
    (b : B) (c : C) :
  apply_triple_snd f (a, b, c) =
  apply_pair_snd f (a, b) >>= (fun x => Ret (x, c)).
Proof.
rewrite /apply_pair_snd /= bindA.
by under [in RHS]eq_bind do rewrite bindretf.
Qed.

Lemma apply_triple_snd_kleisli (M : monad) {A B C D F : UU0}
    (f : B -> M D) (g : D -> M F) (a : A) (b : B) (c : C) :
  apply_triple_snd (f >=> g) (a, b, c) =
    f b >>= (fun b' => apply_triple_snd g (a, b', c)).
Proof.
rewrite apply_triple_sndE.
rewrite /apply_pair_snd.
rewrite kleisliE /= !bindA; bind_ext => d'.
rewrite apply_triple_sndE.
rewrite /apply_pair_snd /=.
by rewrite bindA.
Qed.

Section dassert.
Context {M : failMonad} (N : failMonad) (A : Type) (p : pred A).

Definition dassert (a : A) : M { a | p a } :=
  if Bool.bool_dec (p a) true is left H then Ret (exist p a H) else fail.

End dassert.

Local Open Scope zarith_ext_scope.

Section partl.
Variable (d : unit) (E : orderType d) (M : plusArrayMonad E Z_eqType).

Fixpoint partl (p : E) (s : (seq E * seq E)%type) (xs : seq E)
    : (seq E * seq E)%type :=
  if xs is x :: xs then
    (if x <= p then partl p (rcons s.1 x, s.2) xs
              else partl p (s.1, rcons s.2 x) xs)
  else s.

Lemma partlE s t p u : let x := partition p u in
  partl p (s, t) u = (s ++ x.1, t ++ x.2).
Proof.
elim: u p s t => [|h tl ih] /= p a b; first by rewrite !cats0.
by case: ifPn => hp; rewrite ih /= -cats1 /= -catA.
Qed.

Lemma partition_partl p xs : partition p xs = partl p ([::], [::]) xs.
Proof. by rewrite partlE /=; case: partition. Qed.

End partl.

Section tr_partl.
Variable (d : unit) (E : orderType d) (M : plusArrayMonad E Z_eqType).

Fixpoint tr_partl (p : E) (ys zs xs : seq E) : M (seq E * seq E)%type :=
  if xs is x :: xs then
    (if x <= p then qperm zs >>= ((tr_partl p (rcons ys x))^~ xs)
              else qperm (rcons zs x) >>= ((tr_partl p ys)^~ xs))
  else Ret (ys, zs).

Lemma nondetPlus_sub_tr_partl p (s : seq E) a b :
  nondetPlus_sub (tr_partl p a b s).
Proof.
elim: s p a b => [p a b|h t ih p a b].
  by exists (ndRet (a, b)).
rewrite /=; case: ifPn => hp.
  have [syn synE] := nondetPlus_sub_qperm M b.
  exists (ndBind syn (fun zs' => sval (ih p (rcons a h) zs'))) => /=.
  rewrite synE /=.
  bind_ext => zs' /=.
  by case: ih.
have [syn synE] := nondetPlus_sub_qperm M (rcons b h).
exists (ndBind syn (fun zs' => sval (ih p a zs'))) => /=.
rewrite synE /=.
bind_ext => zs' /=.
by case: ih.
Qed.

Definition dispatch (x p : E) '(ys, zs, xs) : M (seq E * seq E * seq E)%type :=
  if x <= p then qperm zs >>= (fun zs' => Ret (rcons ys x, zs', xs))
            else qperm (rcons zs x) >>= (fun zs' => Ret (ys, zs', xs)).

Lemma tr_partl_dispatch (p x : E) (ys zs xs : seq E) :
  tr_partl p ys zs (x :: xs) =
  dispatch x p (ys, zs, xs) >>= uncurry3 (tr_partl p).
Proof.
rewrite /dispatch {1}/tr_partl.
by case: ifPn => _;
  rewrite bindA; bind_ext => s; rewrite bindretf.
Qed.

Lemma commute_dispatch_writeList i p ys zs xs x A (f : _ -> M A):
  commute (dispatch x p (ys, zs, xs))
          (writeList (i + (size ys)%:Z + (size zs)%:Z + 1) xs)
          (fun x (_ : unit) => f x).
Proof.
apply: commute_plus; rewrite /dispatch; case: ifPn => xp.
  have [syn syn_qperm] := nondetPlus_sub_qperm M zs.
  exists (ndBind syn (fun s => ndRet (rcons ys x, s, xs))).
  by rewrite /= syn_qperm.
have [syn syn_qperm] := nondetPlus_sub_qperm M (rcons zs x).
exists (ndBind syn (fun s => ndRet (ys, s, xs))).
by rewrite /= syn_qperm.
Qed.

End tr_partl.
Arguments tr_partl {d E M}.
Arguments dispatch {d E M}.

Section ipartl.
Variable (d : unit) (E : orderType d) (M : plusArrayMonad E Z_eqType).

(* Lemma lemma13 {i : Z} {ys : seq E} {p : E} :
  perm ys >>= (fun ys' => writeList i (ys' ++ [:: p])) `>=`
  writeList i (p :: ys) >> swap i (i + (size ys)%:Z).
Proof. *)

Fixpoint ipartl (p : E) (i : Z) (ny nz : nat) (nx : nat) : M (nat * nat)%type :=
  match nx with
  | 0 => Ret (ny, nz)
  | k.+1 => aget (i + (ny + nz)%:Z)%Z >>= (fun x => (* TODO *)
           if x <= p then
             aswap (i + ny%:Z) (i + ny%:Z + nz%:Z) >> ipartl p i ny.+1 nz k
           else
             ipartl p i ny nz.+1 k)
  end.

Lemma ipartl_guard (p : E) (i : Z) ny nz (nx : nat) :
  ipartl p i ny nz nx =
  ipartl p i ny nz nx >>= (fun '(a, b) =>
    (guard ((a <= nx + ny + nz) && (b <= nx + ny + nz))%nat >> Ret (a, b))) :> M _.
Proof.
elim: nx ny nz => [ny nz|n ih ny nz].
  by rewrite /= bindretf add0n leq_addr leq_addl guardT bindskipf.
rewrite /= [in RHS]bindA; bind_ext => x; case: ifPn => xp.
- rewrite [in RHS]bindA; bind_ext => -[].
  rewrite [in LHS]ih.
  by under eq_bind do rewrite -addSnnS.
- rewrite [in LHS]ih.
  by under [in RHS]eq_bind do rewrite addSnnS -addnA addSnnS addnA.
Qed.

Lemma write3L_ipartl (i : Z) (p : E) (ys zs xs : seq E) :
  (forall ys zs,
    (writeList i (ys ++ zs ++ xs) >> ipartl p i (size ys) (size zs) (size xs))
    `<=`
    (tr_partl p ys zs xs >>= write2L i)) ->
  write3L i (ys, zs, xs) >>= uncurry3 (ipartl p i)
  `<=`
  uncurry3 (tr_partl p) (ys, zs, xs) >>= write2L i.
Proof.
move=> h.
apply: refin_trans (h ys zs).
rewrite bindA bindretf.
exact: refin_refl.
Qed.

Lemma dispatch_write3L_ipartl (i : Z) (x p : E) (ys zs xs : seq E) :
  (forall ys zs,
    writeList i (ys ++ zs ++ xs) >> ipartl p i (size ys) (size zs) (size xs)
    `<=`
    (tr_partl p ys zs xs >>= write2L i)) ->
  dispatch x p (ys, zs, xs) >>= write3L i >>= uncurry3 (ipartl p i)
  `<=`
  dispatch x p (ys, zs, xs) >>= uncurry3 (tr_partl p) >>= write2L i.
Proof.
move=> h; rewrite 2!bindA /dispatch; case: ifPn => _;
  by rewrite 2!bindA /refin refin_bindl => // {}zs;
     rewrite 2!bindretf; exact: write3L_ipartl h.
Qed.

Lemma dispatch_writeList_cat (i : Z) (x p : E) (ys zs xs : seq E) :
  dispatch x p (ys, zs, xs) >>= write3L i >>= uncurry3 (ipartl p i) =
  dispatch x p (ys, zs, xs) >>= (fun '(ys', zs', xs) =>
    writeList i (ys' ++ zs') >> writeList (i + (size (ys' ++ zs'))%:Z) xs >>
    ipartl p i (size ys') (size zs') (size xs)).
Proof.
rewrite bindA.
bind_ext => [[[ys' zs']] xs'].
by rewrite /write3L !bindA catA writeList_cat bindretf bindA.
Qed.

Definition dipartlT (y z x : nat) :=
  {n : nat * nat | (n.1 <= x + y + z) && (n.2 <= x + y + z)}.

Definition dipartlT1 (y z x : nat) (a : dipartlT y z x) : nat := (sval a).1.
Definition dipartlT2 (y z x : nat) (a : dipartlT y z x) : nat := (sval a).2.

Definition dipartl (p : E) (i : Z) (y z x : nat) :
  M (dipartlT y z x) :=
  ipartl p i y z x >>=
    (dassert [pred n | (n.1 <= x + y + z) && (n.2 <= x + y + z)]).

Local Open Scope mprog.
Lemma ipartlE p i n :
  ipartl p i 0 0 n = fmap (fun x => (dipartlT1 x, dipartlT2 x)) (dipartl p i 0 0 n).
Proof.
rewrite fmapE /= /dipartl !bindA.
rewrite ipartl_guard !bindA.
bind_ext => -[a b] /=.
rewrite bindA.
apply: bind_ext_guard => /andP[na nb].
rewrite bindretf /= /dassert /=.
case: Bool.bool_dec => [nanb|].
  by rewrite bindretf.
by move/negP; rewrite negb_and => /orP[|] /negP.
Qed.
Local Close Scope mprog.

End ipartl.
Arguments ipartl {d E M}.
Arguments dipartl {d E M}.

(* TODO: move?*)
Definition preserves {M : monad} A B (f : A -> M A) (g : A -> B) :=
  forall x, (f x >>= fun y => Ret (y, g y)) = (f x >>= fun y => Ret (y, g x)).

Section ssplits.
Variable (M : plusMonad).

Definition ssplitsT A n := {x : seq A * seq A | size x.1 + size x.2 = n}.
Definition ssplitsT1 A n (a : ssplitsT A n) : seq A := (sval a).1.
Definition ssplitsT2 A n (a : ssplitsT A n) : seq A := (sval a).2.

Local Obligation Tactic := idtac.

Program Fixpoint ssplits A (s : seq A) : M (ssplitsT A (size s))%type :=
  match s with
  | [::] => Ret (exist _ ([::], [::]) _)
  | x :: xs => (ssplits xs >>= fun yz => Ret (exist _ (x :: yz.1, yz.2) _) [~]
                                    Ret (exist _ (yz.1, x :: yz.2) _))
  end.
Next Obligation. by []. Qed.
Next Obligation.
by move=> A [//|x' xs'] x xs [xx' xsxs'] [[a b] /=] <-; rewrite addSn.
Qed.
Next Obligation.
by move=> A [//|x' xs'] x xs [xx' xsxs'] [[a b] /=] <-; rewrite -addnS.
Qed.

Local Open Scope mprog.
Lemma splitsEssplits A (s : seq A) :
  splits s = fmap (fun xy => (ssplitsT1 xy, ssplitsT2 xy)) (ssplits s) :> M _.
Proof.
elim: s => [|h t ih]; first by rewrite fmapE /= bindretf.
rewrite /= fmapE bindA ih /= fmapE !bindA; bind_ext => -[[a b] ab] /=.
by rewrite bindretf /= alt_bindDl /=; congr (_ [~] _); rewrite bindretf.
Qed.
Local Close Scope mprog.

(* NB: not used *)
Lemma qperm_preserves_elements (A : eqType) (s : seq A) :
  qperm s = qperm s >>= (fun x => guard (perm_eq x s) >> Ret x) :> M _.
Proof.
have [n ns] := ubnP (size s); elim: n s ns => // n ih s ns.
move: s ns => [ns |h t].
  by rewrite qperm_nil bindretf perm_refl guardT bindskipf.
rewrite /= ltnS => ns.
rewrite qperm_cons bindA splits_guard_subseq !bindA; bind_ext => -[a b].
rewrite /= !bindA; apply: bind_ext_guard => /and3P[_ _ abt].
rewrite !bindretf /liftM2 /= !bindA ih; last first.
  by rewrite (leq_trans _ ns) // ltnS -(perm_size abt) size_cat leq_addr.
rewrite !bindA; bind_ext => a'.
rewrite !bindA; apply: bind_ext_guard => aa'.
rewrite !bindretf !bindA ih; last first.
  by rewrite (leq_trans _ ns) // ltnS -(perm_size abt) size_cat leq_addl.
rewrite !bindA; bind_ext => b'.
rewrite !bindA; apply: bind_ext_guard => bb'.
rewrite !bindretf.
rewrite -[in X in _ = X >> _]cat_rcons -cats1 -catA perm_catCA perm_cons.
by rewrite (perm_trans (perm_cat aa' bb') abt) guardT bindskipf.
Qed.

(* NB: can't use the preserves predicate because the input/output of splits
   are of different sizes *)
(* NB: not used *)
(*Lemma splits_preserves_size (A : eqType) (x : seq A) :
  (splits x >>= fun x' => Ret (x', size x'.1 + size x'.2)) =
  (splits x >>= fun x' => Ret (x', size x)) :> M _.
Proof.
rewrite splits_preserves_subseq 2!bindA; bind_ext => -[a b] /=.
rewrite 2!bindA; apply: bind_ext_guard => /and3P[_ _ abx].
by rewrite 2!bindretf /= -size_cat (perm_size abx).
Qed.*)

Lemma qperm_preserves_size A : preserves (@qperm M A) size.
Proof.
move=> s; have [n ns] := ubnP (size s); elim: n s ns => // n ih s ns.
move: s ns => [ns|p s]; first by rewrite !qperm_nil !bindretf.
rewrite /= ltnS => ns.
rewrite qpermE !bindA.
(*bind_ext => -[a b]. (* we lose the size information *)*)
rewrite !splitsEssplits !fmapE !bindA; bind_ext => -[[a b] /= ab].
rewrite !bindretf (bind_liftM2_size _ _ 1%N); last first.
  by move=> x y; rewrite size_cat /= addn1 -addnS.
rewrite {1}/liftM2 ih; last first.
  by rewrite /ssplitsT1 /= (leq_trans _ ns)// ltnS -ab leq_addr.
rewrite /liftM2 !bindA; bind_ext => xa.
rewrite bindretf ih; last first.
  by rewrite /ssplitsT2 /= (leq_trans _ ns)// ltnS -ab leq_addl.
rewrite !bindA; bind_ext => xb.
by rewrite !bindretf /= ab addn1.
Qed.

(* NB: easier to user than qperm_preserves_size? worth explaining? *)
Lemma qperm_preserves_size2 A (x : seq A) B (f : seq A -> nat -> M B) :
  (qperm x >>= f^~ (size x)) = qperm x >>= (fun x' => f x' (size x')) :> M _.
Proof.
transitivity (qperm x >>= (fun y => Ret (y, size y)) >>= (fun x' => f x'.1 x'.2)).
  by rewrite qperm_preserves_size bindA; bind_ext => s; rewrite bindretf.
by rewrite bindA; bind_ext => s; rewrite bindretf.
Qed.

Lemma bind_qperm_guard A (s : seq A) B (f : seq A -> M B) :
  qperm s >>= f = qperm s >>= (fun x => guard (size s == size x) >> f x).
Proof.
rewrite -(qperm_preserves_size2 s (fun a b => guard (size s == b) >> f a)).
rewrite eqxx guardT.
by under [in RHS]eq_bind do rewrite bindskipf.
Qed.

Lemma slowsort_preserves_size {d : unit} {E : orderType d} :
  preserves (@slowsort M _ E) size.
Proof.
move=> s; have [n ns] := ubnP (size s); elim: n s ns => // n ih s ns.
move: s ns => [ns|p s]; first by rewrite /= slowsort_nil 2!bindretf.
rewrite /= ltnS => ns.
rewrite /slowsort kleisliE !bindA.
rewrite (qperm_preserves_size2 _
  (fun a b => assert (sorted <=%O) a >>= (fun x' => Ret (x', b)))).
bind_ext => ht.
rewrite assertE 2!bindA; apply: bind_ext_guard => _.
by rewrite 2!bindretf.
Qed.

Lemma slowsort_preserves_size2 {d : unit} {E : orderType d} (x : seq E) B
    (f : seq E -> nat -> M B) :
  (slowsort x >>= fun x' => f x' (size x)) = (slowsort x >>= fun x' => f x' (size x')) :> M _.
Proof.
transitivity ((slowsort x >>= (fun y => Ret (y, size y)) >>= (fun x' => f x'.1 x'.2))).
  by rewrite slowsort_preserves_size bindA; bind_ext => s; rewrite bindretf.
by rewrite bindA; bind_ext => s; rewrite bindretf.
Qed.

Lemma bind_slowsort_guard {d : unit} {E : orderType d} (s : seq E) B (f : seq E -> M B) :
  (slowsort s >>= f) = slowsort s >>= (fun x => guard (size s == size x) >> f x).
Proof.
rewrite -(slowsort_preserves_size2 s (fun a b => guard (size s == b) >> f a)).
rewrite eqxx guardT.
by under [in RHS]eq_bind do rewrite bindskipf.
Qed.

End ssplits.

Section slowsort.
Variable M : plusMonad.
Variables (d : unit) (E : orderType d).

Lemma refin_partition_slowsort (p : E) (s : seq E) :
  Ret (partition p s) >>= (fun '(a, b) =>
  slowsort a >>= (fun a' => slowsort b >>= (fun b' => Ret (a' ++ p :: b'))))
  `<=`
  (slowsort (p :: s) : M _).
Proof.
rewrite slowsort_splits.
apply: refin_trans; first exact/refin_bindr/(partition_spec M p s).
rewrite bindA; apply: refin_bindl => -[a b].
rewrite assertE (bindA _ (fun _ => Ret (a, b))) bindretf /= bindA.
exact: refin_refl.
Qed.

End slowsort.

Section ssplits_iqsort.
Variable (d : unit) (E : orderType d) (M : plusArrayMonad E Z_eqType).

(* page 11 step 4 *)
Lemma qperm_preserves_length (i : Z) (x p : E) (ys zs xs : seq E) :
  dispatch x p (ys, zs, xs) >>= (fun '(ys', zs', xs) =>
    writeList i (ys' ++ zs') >> writeList (i + (size (ys' ++ zs'))%:Z) xs >>
    ipartl p i (size ys') (size zs') (size xs)) =
  writeList (i + (size ys)%:Z + (size zs)%:Z + 1) xs >>
    dispatch x p (ys, zs, xs) >>= (fun '(ys', zs', xs) =>
    writeList i (ys' ++ zs') >> ipartl p i (size ys') (size zs') (size xs)) :> M _.
Proof.
rewrite [in RHS]bindA.
rewrite -commute_dispatch_writeList.
rewrite /dispatch.
(* TODO: simplify this *)
case: ifPn => xp.
  rewrite !bindA.
  under eq_bind do rewrite bindretf.
  under [in RHS]eq_bind do rewrite bindretf.
  under eq_bind do rewrite -writeList_cat.
  under [in RHS]eq_bind do rewrite -bindA.
  under [in RHS]eq_bind do rewrite -2!addZA.
  rewrite [RHS](qperm_preserves_size2 zs (fun a b =>
    (writeList (i + ((size ys)%:Z + (b%:Z + 1))) xs >>
    writeList i ((rcons ys x) ++ a)) >>
    ipartl p i (size (rcons ys x)) (size a) (size xs))).
  bind_ext => zs' /=.
  rewrite (_ : (_ + (_ + 1))%Z = (size (ys ++ x :: zs'))%:Z); last first.
    by rewrite size_cat /= intRD natZS -add1Z (addZC 1%Z).
  rewrite -writeListC; last first.
    by rewrite -cats1 -catA; exact: leZZ.
  by rewrite writeList_cat -cats1 -catA.
rewrite !bindA.
under eq_bind do rewrite bindretf.
under [in RHS]eq_bind do rewrite bindretf.
under eq_bind do rewrite -writeList_cat.
under [in RHS]eq_bind do rewrite -bindA.
under [in RHS]eq_bind do rewrite -2!addZA.
rewrite -Z_S -(size_rcons zs x).
rewrite [RHS](qperm_preserves_size2 (rcons zs x) (fun a b =>
  (writeList (i + ((size ys)%:Z + b%:Z)) xs >>
  writeList i (ys ++ a)) >> ipartl p i (size ys) (size a) (size xs))).
bind_ext => zs' /=.
rewrite (_ : (_ + (_ + _))%Z = (i + (size (ys ++ zs'))%:Z)%Z); last first.
  by rewrite size_cat /= intRD.
by rewrite -writeListC ?writeList_cat//; exact: leZZ.
Qed.

(* page11 top derivation *)
Lemma tr_partl_writeList (p x : E) (ys zs xs : seq E) (i : Z) :
  (forall ys zs,
       (writeList i (ys ++ zs ++ xs) >> ipartl p i (size ys) (size zs) (size xs) : M _)
       `<=`
       (tr_partl p ys zs xs >>= write2L i)) ->
  (writeList (i + (size ys)%:Z + (size zs)%:Z + 1)%Z xs >>
   if x <= p then qperm zs >>= (fun zs' => writeList i (ys ++ x :: zs') >>
     ipartl p i (size ys + 1) (size zs') (size xs))
   else qperm (rcons zs x) >>= (fun zs' => writeList i (ys ++ zs') >>
     ipartl p i (size ys) (size zs') (size xs)) : M _)
  `<=`
  tr_partl p ys zs (x :: xs) >>= write2L i.
Proof.
move=> h; rewrite tr_partl_dispatch.
apply: refin_trans; last exact: (dispatch_write3L_ipartl _ _ _ h).
rewrite dispatch_writeList_cat.
rewrite qperm_preserves_length.
rewrite /dispatch bindA.
apply refin_bindl => -[].
case: ifPn => xp. (* TODO:  *)
- rewrite bindA /refin -alt_bindDr.
  bind_ext => s.
  by rewrite bindretf size_rcons addn1 -cat1s catA cats1 altmm.
- rewrite bindA /refin -alt_bindDr.
  bind_ext => s.
  by rewrite bindretf altmm.
Qed.

End ssplits_iqsort.

Section fsplits.
Variable (d : unit) (E : orderType d) (M : plusArrayMonad E Z_eqType).

Lemma gt0_flatten A (s : seq A) (f : A -> A) : (0 < size s)%nat ->
  (0 < size (flatten [seq [:: f y] | y <- s]))%nat.
Proof. by case: s. Qed.

Lemma perm_eq_flatten_map (A : eqType) (s : seq A) (f g : A -> A) :
  perm_eq (flatten [seq [:: f y; g y] | y <- s])
          (flatten [seq [:: f y] | y <- s] ++ flatten [seq [:: g y] | y <- s]).
Proof.
elim: s f g => // h t ih f g.
rewrite /=.
rewrite -[in X in perm_eq _ X](cat1s (f h)).
rewrite -[in X in perm_eq _ X](cat1s (g h)).
rewrite catA.
apply: (@perm_trans _ (([:: f h] ++ [:: g h]) ++
                        flatten [seq [:: f y] | y <- t] ++
                        flatten [seq [:: g y] | y <- t])); last first.
  rewrite perm_catACA.
  exact: perm_refl.
by rewrite -(cat1s (f h)) -(cat1s (g h)) catA perm_cat.
Qed.

Fixpoint fsplits (A : eqType) (s : seq A) : seq (seq A * seq A)%type :=
  if s isn't x :: xs then [:: ([::], [::])] else
  let t := fsplits xs in
  flatten (map (fun y => [:: (x :: y.1, y.2); (y.1, x :: y.2)]) t).

Lemma fsplits_subseq (A : eqType) (s : seq A) x :
  x \in fsplits s -> [/\ subseq x.1 s, subseq x.2 s & perm_eq (x.1 ++ x.2) s].
elim: s x => /= [x|h t ih /= x /flattenP[/= l]].
  by rewrite inE => /eqP ->.
move=> /mapP[/= [x1 x2]] /ih[/= x1t x2t x1x2t ->{l}].
rewrite !inE => /orP[|] /eqP -> /=.
- rewrite eqxx; split => //.
    destruct x2 as [|x21 x22] => //.
    case: ifPn => // /eqP ?; subst x21.
    exact: cons_subseq x2t.
  by rewrite perm_cons.
split.
- destruct x1 as [|x11 x12] => //.
  case: ifPn => // /eqP ?; subst x11.
  exact: cons_subseq x1t.
- by rewrite eqxx.
- rewrite -cat_rcons -cats1.
  by rewrite perm_catAC perm_catC perm_cons.
Qed.

Lemma fsplits_gt0 (A : eqType) (s : seq A) : (0 < size (fsplits s))%nat.
Proof. by elim: s => // h t ih /=; destruct (fsplits t). Qed.

(* NB: not used *)
Lemma splits_fsplits (s : seq E) : splits s = arbitrary ([::], [::]) (fsplits s) :> M _.
Proof.
elim: s => [|h t ih]; first by rewrite /= arbitrary1.
destruct t as [|t1 t2]; first by rewrite /= bindretf /= /arbitrary /= altC.
rewrite [t1 :: t2]lock /= -lock ih alt_bindDr.
have /(perm_eq_arbitrary ([::], [::])) -> : perm_eq
  (flatten [seq [:: (h :: y.1, y.2); (y.1, h :: y.2)] | y <- fsplits (t1 :: t2)])
  ((flatten [seq [:: (h :: y.1, y.2)] | y <- fsplits (t1 :: t2)]) ++
   (flatten [seq [:: (y.1, h :: y.2)] | y <- fsplits (t1 :: t2)])).
  by rewrite perm_eq_flatten_map.
rewrite arbitrary_cat; last 2 first.
  by apply: gt0_flatten; exact: fsplits_gt0.
  by apply: gt0_flatten; exact: fsplits_gt0.
by congr (_ [~] _); rewrite arbitrary_flatten //; exact: fsplits_gt0.
Qed.

(* NB: not used *)
Lemma bind_ext_splits A (s : seq E) (f : seq E -> seq E -> M A) (m : seq E -> M A) :
  (forall ys zs, subseq ys s -> subseq zs s -> perm_eq (ys ++ zs) s -> f ys zs = m s) ->
  (do x <- splits s; (let '(ys, zs) := x in f ys zs))%Do = m s.
Proof.
move=> h.
transitivity ((do x <- splits s; (let '(ys, zs) := x in m s))%Do).
  rewrite splits_guard_subseq !bindA.
  bind_ext => -[a b] /=.
  rewrite !bindA.
  apply: bind_ext_guard => /and3P[sa sb abs].
  rewrite !bindretf.
  by rewrite h.
clear h f.
transitivity (splits s >> m s).
  by bind_ext => -[].
(* TODO splits inde *)
elim: s m => /= [m|].
  by rewrite bindretf.
move=> h t ih m.
rewrite bindA.
under eq_bind do rewrite alt_bindDl.
rewrite alt_bindDr.
under eq_bind do rewrite bindretf.
under [in X in _[~]X]eq_bind do rewrite bindretf.
by rewrite (ih (fun s => m (h :: s))) altmm.
Qed.

End fsplits.

Section more_about_qperm.
Variable M : plusMonad.

(* NB: postulate return⊑perm in in Nondet.agda *)
Lemma refin_qperm_ret (A : eqType) (s : seq A) : (Ret s : M _) `<=` qperm s.
Proof. by rewrite -iperm_qperm; exact: refin_ret_iperm. Qed.

Lemma qperm_refin_rcons (A : eqType) h (t : seq A) :
  (Ret (rcons t h) : M _) `<=` qperm (h :: t).
Proof. by rewrite qperm_cons_rcons; exact: refin_qperm_ret. Qed.

Lemma qperm_refin_cons (A : eqType) h (t : seq A) :
  (Ret (h :: t) : M _) `<=` qperm (rcons t h).
Proof. by rewrite -qperm_cons_rcons; exact: refin_qperm_ret. Qed.

End more_about_qperm.

(* TODO: move to array_lib? *)
Section refin_qperm_writeList.
Variable (d : unit) (E : orderType d) (M : plusArrayMonad E Z_eqType).

(* eqn 11 in mu2020flops *)
Lemma refin_qperm_writeList_cons (i : Z) x (s : seq E) :
  writeList i (rcons s x) >> aswap (M := M) i (i + (size s)%:Z)
  `<=`
  qperm s >>= (fun s' => writeList (M := M) i (x :: s')).
Proof.
case: s => [|h t] /=.
  rewrite qperm_nil bindmskip bindretf addZ0 aswapxx bindmskip.
  exact: refin_refl.
rewrite bindA writeList_rcons -aput_writeList_rcons.
apply: (refin_trans _ (refin_bindr _ (qperm_refin_rcons _ _ _))).
by rewrite bindretf; exact: refin_refl.
Qed.

(* eqn 13 in mu2020flops, postulate introduce-swap in IQSort.agda *)
Lemma refin_qperm_writeList_rcons (i : Z) x (s : seq E) :
  writeList i (x :: s) >> aswap (M := M) i (i + (size s)%:Z)
  `<=`
  qperm s >>= (fun s' => writeList i (rcons s' x)).
Proof.
elim/last_ind: s => [|t h ih] /=.
  rewrite qperm_nil bindmskip bindretf addZ0 aswapxx /= bindmskip.
  exact: refin_refl.
rewrite bindA.
apply: (refin_trans _ (refin_bindr _ (qperm_refin_cons _ _ _))).
by rewrite bindretf -bindA -writeList_aswap; exact: refin_refl.
Qed.

End refin_qperm_writeList.

Section iqsort.
Variable (d : unit) (E : orderType d) (M : plusArrayMonad E Z_eqType).

(*Fixpoint iqsort (i : Z) (n : nat) : M unit :=
  match n with
  | 0 => Ret tt
  | n.+1 => aget i >>= (fun p =>
         ipartl p (i) 0 0 n >>= (fun '(ny, nz) =>
         aswap i (i + ny%:Z) >>
         iqsort i ny >> iqsort (ny%:Z) nz))
  end.*)

(*Function iqsort (i : Z) (n : nat) {measure n} : M unit :=
  match n with
  | 0 => Ret tt
  | k.+1 => aget i >>= (fun p =>
            ipartl p (i + 1) 0 0 (n-1) >>= (fun '(ny, nz) => aswap i (i + ny%:Z) >> iqsort i ny))
  end.*)

Local Obligation Tactic := idtac.

(*
(* fail attempt *)
Program Fixpoint iqsort' (ni : (Z * nat))
    (f : forall (n'j : (Z * nat)), (n'j.2 < ni.2)%coq_nat -> M unit) : M unit :=
  match ni.2 with
  | 0 => Ret tt
  | n.+1 => aget ni.1 >>= (fun p =>
            ipartl p (ni.1 + 1)%Z 0 0 n >>= (fun '(ny, nz) =>
              aswap ni.1 (ni.1 + ny%:Z) >>
              f (ni.1, ny) _ >> f ((ni.1 + ny%:Z + 1)%Z, nz) _))
  end.
Next Obligation.
move => [i [//|n']] /= _ n [<-] p [a b] /= a' _ [-> _] _.
*)

Program Fixpoint iqsort' ni
    (f : forall mj, (mj.2 < ni.2)%coq_nat -> M unit) : M unit :=
  match ni.2 with
  | 0 => Ret tt
  | n.+1 => aget ni.1 >>= (fun p =>
            dipartl p (ni.1 + 1) 0 0 n >>= (fun nynz =>
              let ny := nynz.1 in
              let nz := nynz.2 in
              aswap ni.1 (ni.1 + ny%:Z) >>
              f (ni.1, ny) _ >> f ((ni.1 + ny%:Z + 1)%Z, nz) _))
  end.
Next Obligation.
move => [i [//|n']] /= _ n [<-] p [[a b] /=] /andP[an _] _.
apply/ssrnat.ltP; rewrite ltnS.
by rewrite 2!addn0 in an.
Qed.
Next Obligation.
move => [i [//|n']] /= _ n [<-] p [[a b] /=] /andP[_ bn] _.
apply/ssrnat.ltP; rewrite ltnS.
by rewrite 2!addn0 in bn.
Qed.

Lemma well_founded_lt2 : well_founded (fun x y : (Z * nat) => (x.2 < y.2)%coq_nat).
Proof.
by apply: (@well_founded_lt_compat _ _) => -[x1 x2] [y1 y2]; exact.
Qed.

Definition iqsort : (Z * nat) -> M unit :=
  Fix well_founded_lt2 (fun _ => M unit) iqsort'.

Lemma iqsort'_Fix (ni : (Z * nat))
  (f g : forall (n'j : (Z * nat)), (n'j.2 < ni.2)%coq_nat -> M unit) :
  (forall (n'j : (Z * nat)) (p : (n'j.2 < ni.2)%coq_nat), f n'j p = g n'j p) ->
  iqsort' f = iqsort' g.
Proof.
  by move=> ?; congr iqsort'; apply fun_ext_dep => ?; rewrite boolp.funeqE.
Qed.

Lemma iqsort_nil (i : Z) : iqsort (i, 0) = Ret tt.
Proof. by rewrite /iqsort Fix_eq //; exact: iqsort'_Fix. Qed.

Lemma iqsort_cons (i : Z) (n : nat) : iqsort (i, n.+1) = aget i >>= (fun p =>
  dipartl p (i + 1)%Z 0 0 n >>= (fun nynz =>
    let ny := dipartlT1 nynz in
    let nz := dipartlT2 nynz in
    aswap i (i + ny%:Z) >>
    iqsort (i, ny) >> iqsort ((i + ny%:Z + 1)%Z, nz))).
Proof. by rewrite [in LHS]/iqsort Fix_eq //=; exact: iqsort'_Fix. Qed.

(* bottom of the page 11, used in the proof of lemma 10 *)
Lemma refin_ipartl_tr_partl_helper (i : Z) x (ys zs : seq E) :
  writeList i (rcons (ys ++ zs) x) >>
    aswap (M := M) (i + (size ys)%:Z) (i + (size ys)%:Z + (size zs)%:Z)
  `<=`
  qperm zs >>= (fun zs' => writeList i (ys ++ x :: zs')).
Proof.
under [in X in _ `<=` X]eq_bind do rewrite writeList_cat.
have -> : commute (qperm zs) _ _.
  by move=> *; exact/commute_plus/nondetPlus_sub_qperm.
rewrite rcons_cat writeList_cat bindA.
apply: refin_bindl => -[].
exact: refin_qperm_writeList_cons.
Qed.

(* page 12, used in the proof of lemma 10 *)
Lemma writeList_ipartl (p x : E) (i : Z) (ys zs xs : seq E) :
  writeList (i + (size ys + size zs)%:Z + 1) xs >>
  (if x <= p
    then writeList i (rcons (ys ++ zs) x) >>
      aswap (i + (size ys)%:Z) (i + (size ys + size zs)%:Z) >>
      ipartl p i (size ys + 1) (size zs) (size xs)
    else writeList i (rcons (ys ++ zs) x) >>
      ipartl p i (size ys) (size zs + 1) (size xs)) =
  writeList i (ys ++ zs ++ (x :: xs)) >>
    aget (i + (size ys + size zs)%:Z)%Z >>= (fun x =>
    (if x <= p
      then aswap (i + (size ys)%:Z) (i + (size ys + size zs)%:Z) >>
        ipartl p i (size ys + 1) (size zs) (size xs)
      else ipartl p i (size ys) (size zs + 1) (size xs))) :> M _.
Proof.
transitivity (writeList i (ys ++ zs ++ (x :: xs)) >>
   if x <= p then
     aswap (i + (size ys)%:Z) (i + (size ys + size zs)%:Z) >>
     ipartl p i (size ys + 1) (size zs) (size xs)
    else ipartl p i (size ys) (size zs + 1) (size xs) : M _).
  case: ifPn => xp.
  - rewrite catA -cat1s catA writeList_cat.
    rewrite [in RHS]writeListC; last exact: leZZ.
    rewrite {1}size_cat /= {1}[in RHS]intRD size_cat addZA [in RHS]bindA.
    bind_ext => -[].
    by rewrite cats1 bindA; bind_ext.
  - rewrite -[in RHS]cat1s 2!catA writeList_cat.
    rewrite writeListC; last exact: leZZ.
    by rewrite {1}size_cat [in RHS]intRD size_cat addZA bindA cats1.
rewrite bindA catA writeList_cat 2!bindA.
rewrite size_cat intRD addZA.
bind_ext => -[].
transitivity (
  writeList (i + (size ys)%:Z + (size zs)%:Z)%Z (x :: xs) >> Ret x >>
  (if x <= p then
    aswap (i + (size ys)%:Z) (i + (size ys)%:Z + (size zs)%:Z) >>
    ipartl p i (size ys + 1) (size zs) (size xs)
   else ipartl p i (size ys) (size zs + 1) (size xs)) : M _
).
  by rewrite bindA bindretf.
rewrite (writeList_ret_aget _ x xs (fun x0 => (
   if x0 <= p
     then aswap (i + (size ys)%:Z) (i + (size ys)%:Z + (size zs)%:Z) >>
       ipartl p i (size ys + 1) (size zs) (size xs)
     else ipartl p i (size ys) (size zs + 1) (size xs)))).
by rewrite bindA.
Qed.

(* specification of ipartl, eqn 10 p.10 of mu2020flops *)
Lemma refin_ipartl_tr_partl p (i : Z) (xs zs ys : seq E) :
  write3L i (ys, zs, xs) >>= uncurry3 (ipartl p i)
  `<=`
  tr_partl (M := M) p ys zs xs >>= write2L i.
Proof.
elim: xs i p zs ys => [|h t ih] i p zs ys.
  apply: eq_refin.
  by rewrite /= bindretf cats0 bindA bindretf.
have : (forall ys zs,
    writeList i (ys ++ zs ++ t) >> ipartl (M := M) p i (size ys) (size zs) (size t)
    `<=` tr_partl p ys zs t >>= write2L i).
  move=> {}ys {}zs.
  apply: (refin_trans _ (ih i p _ _)).
  rewrite /write3L bindA bindretf /uncurry3.
  exact: refin_refl.
move=> /(@tr_partl_writeList _ E M p h ys zs t i).
apply: refin_trans.
apply: (@refin_trans _ _ (writeList (i + (size ys)%:Z + (size zs)%:Z + 1) t >>
  (if h <= p
   then writeList i (rcons (ys ++ zs) h) >>
        aswap (i + (size ys)%:Z) (i + (size ys)%:Z + (size zs)%:Z) >>
        ipartl p i (size ys + 1) (size zs) (size t)
   else writeList i (rcons (ys ++ zs) h) >>
        ipartl p i (size ys) (size zs + 1) (size t)))); last first.
  apply: refin_bindl => -[].
  case: ifPn => hp; last first.
    apply: (@refin_trans _ _ (Ret (rcons zs h) >>= fun zs' =>
        writeList i (ys ++ zs') >> ipartl p i (size ys) (size zs') (size t))); last first.
      apply: refin_bindr.
      exact: refin_qperm_ret.
    rewrite bindretf size_rcons addn1 rcons_cat.
    exact: refin_refl.
  rewrite -[X in _ `<=` X](qperm_preserves_size2 zs (fun a b =>
    writeList i (ys ++ h :: a) >>
    ipartl p i (size ys + 1) b (size t))).
  rewrite -[in X in _ `<=` X]bindA.
  apply: refin_bindr.
  exact: refin_ipartl_tr_partl_helper.
rewrite -2!addZA !(addZA (size ys)%:Z) -intRD addZA.
rewrite -[in X in _ >> X]addZA -intRD writeList_ipartl.
rewrite /write3L.
rewrite bindA.
under eq_bind do rewrite bindretf.
rewrite /uncurry3 /=.
rewrite bindA -addZA -intRD.
rewrite (addn1 (size ys)) (addn1 (size zs)).
exact: refin_refl.
Qed.

(* Lemma ipartlspec (i : Z) (p : E) ys zs xs :
  (*write3L i >=> ipartl p i `<=` partl' p >=> write2L i.*)
  (do x <- write3L i (ys, zs, xs); uncurry3 (ipartl p i) x)%Do `<=`
  uncurry3 (partl' p) (ys, zs, xs) >>= (fun '(ys, zs) => write2L i (ys, zs)).
Proof. Abort. *)

(* not used 2021-09-24: first equation on page 10 *)
(* Lemma ipartl_spec (i : Z) (p : E) (ys zs xs : seq E)
    (ipartl : E -> Z -> (nat * nat * nat)%type -> M (nat * nat)%type) :
  writeList i (ys ++ zs ++ xs) >> ipartl p i (size ys, size zs, size xs)
  `<=` second qperm (partl p (ys, zs) xs) >>= write2L i.
Proof. Abort. *)

Lemma refin_qperm_tr_partl_qperm_partl a b p xs :
  (apply_triple_snd qperm >=> uncurry3 (tr_partl p)) (a, b, xs) `<=`
  apply_pair_snd (M := M) qperm (partl (p : E) (a, b) xs).
Proof.
elim: xs p a b => [/=|h t ih] p a b.
  rewrite kleisliE apply_triple_sndE bindA.
  under eq_bind do rewrite bindretf /=.
  rewrite -[X in _ `<=` X]bindmret.
  apply: refin_bindl => -[x y].
  exact: refin_refl.
rewrite [in X in _ `<=` X]/= -if_arg -fun_if if_pair(*if inside args*).
apply/(refin_trans _ (ih _ _ _))/eq_refin/esym.
rewrite -if_pair -[in LHS](if_same (h <= p) t) -if_pair(*if outside args*).
rewrite [in LHS]kleisliE -[X in apply_triple_snd X _]qperm_idempotent fun_if.
rewrite 2!apply_triple_snd_kleisli qperm_rcons bindA -bind_if bindA.
rewrite [RHS]kleisliE [in RHS]apply_triple_sndE [in RHS]bindA.
rewrite [in RHS]/apply_pair_snd /= [in RHS]bindA.
do 2 under [RHS]eq_bind do rewrite bindretf.
bind_ext => b'.
rewrite -apply_triple_snd_kleisli qperm_idempotent if_bind.
rewrite !bindA /=.
under eq_bind do rewrite bindretf.
by under [in X in if _ then _ else X]eq_bind do rewrite bindretf.
Qed.

(* partl'-spec *)
Lemma refin_partl_tr_qperm_partl a b p xs :
  tr_partl (M := M) p a b xs `<=` apply_pair_snd qperm (partl p (a, b) xs).
Proof.
apply: refin_trans; last exact: refin_qperm_tr_partl_qperm_partl.
rewrite kleisliE.
rewrite apply_triple_sndE.
rewrite bindA.
under [in X in _ `<=` X]eq_bind do rewrite bindretf.
rewrite apply_pair_snd_uncurry3.
rewrite -[X in X `<=` _](bindretf b ((tr_partl p a)^~ xs)).
exact/refin_bindr/refin_qperm_ret.
Qed.

(* eqn 12 *)
Lemma iqsort_slowsort (i : Z) (xs : seq E) :
  writeList i xs >> iqsort (i, size xs) `<=` slowsort xs >>= writeList i.
Proof.
have [n nxs] := ubnP (size xs); elim: n xs i => // n ih xs i in nxs *.
move: xs => [|p xs] in nxs *.
  by rewrite /= iqsort_nil slowsort_nil 2!bindretf /=; exact: refin_refl.
(* step 1: l.342 in IQSOrt.agda, corresponds to second equation on page 13 of mu2020flops *)
apply: (@refin_trans _ _ (tr_partl p [::] [::] xs >>= (fun '(ys, zs) =>
     writeList (i + (size ys)%:Z + 1)%Z zs >>
     qperm ys >>= (fun ys' => writeList i (rcons ys' p) >>
       iqsort (i, size ys) >>
       iqsort ((i + (size ys)%:Z + 1)%Z, size zs))))); last first.
  (* step 1a: refin slowsort *)
  apply: refin_trans; last by apply: refin_bindr; exact: refin_partition_slowsort.
  rewrite bindretf.
  move pxs : (partition p xs) => tmp; case: tmp => [ys zs] in pxs *.
  (* step 1b: introduce qperm's and commute *)
  rewrite -qperm_slowsort 2!kleisliE !bindA.
  rewrite [X in _ `<=` X](_ : _ =
    (do zs' <- qperm zs; do ys' <- qperm ys; do ys'' <- slowsort ys';
     do zs'' <- slowsort zs'; writeList i (ys'' ++ p :: zs''))%Do); last first.
    have -> : @commute M _ _ (qperm zs) (qperm ys) _ _.
      by move=> *; exact/commute_plus/nondetPlus_sub_qperm.
    bind_ext => ys'.
    rewrite !bindA; under eq_bind do rewrite !bindA.
    have <- : @commute M _ _ (qperm zs) (slowsort ys') _ _.
      by move=> *; exact/commute_plus/nondetPlus_sub_qperm.
    bind_ext => zs'.
    under eq_bind do rewrite bindA.
    bind_ext => ys''.
    by under eq_bind do rewrite bindretf.
  (* step 1c: refine tr_partl to partl *)
  apply: refin_trans.
    exact/refin_bindr/refin_partl_tr_qperm_partl.
  (* step 1d: execute the first qperm and record size information *)
  rewrite -partition_partl pxs bindA /=.
  under eq_bind do rewrite bindretf.
  rewrite bind_qperm_guard [in X in X `<=` _]bind_qperm_guard(*NB: interesting?*).
  apply: refin_bindl => zs'.
  apply: refin_bind_guard => /eqP zszs'.
  (* step 1e: commutation *)
  rewrite ![in X in X `<=` _]bindA.
  have <- : commute (qperm ys) (writeList (i + (size ys)%:Z + 1) zs' : M _) _.
    by move=> T f; exact/commute_plus/nondetPlus_sub_qperm.
  (* step 1f: qperm_preserves_size2, execute the second qperm and record size information *)
  rewrite (qperm_preserves_size2 ys (fun a b =>
    (writeList (i + b%:Z + 1) zs' >> (writeList i (rcons a p) >> iqsort (i, b) >>
    iqsort ((i + b%:Z + 1)%Z, size zs'))))).
  rewrite bind_qperm_guard [in X in _ `<=` X]bind_qperm_guard (*NB: interesting?*).
  apply: refin_bindl => ys'.
  apply: refin_bind_guard => /eqP ysys'.
  (* step 1g: ih *)
  rewrite -cats1 writeList_cat writeListC; last exact: leZZ.
  rewrite (bindA _ _ (fun _ => iqsort (i, size ys'))).
  apply: (@refin_trans _ _ (
      (writeList (i + (size ys')%:Z + 1) zs' >>
      (writeList (i + (size ys')%:Z) [:: p] >>
      (slowsort ys' >>= writeList i))) >>
      iqsort ((i + (size ys')%:Z + 1)%Z, size zs'))).
    rewrite !bindA.
    do 2 apply: refin_bindl => -[].
    rewrite 2!bindretf -2!bindA; apply/refin_bindr/ih.
    move: nxs; rewrite /= ltnS; apply: leq_ltn_trans.
    by rewrite -ysys' -(size_partition p xs) pxs /= leq_addr.
  (* step 1h: slowsort_preserves_size2 *)
  rewrite -[in X in X `<=` _](_ : commute (slowsort ys') _ _); last first.
    exact/commute_plus/nondetPlus_sub_slowsort.
  rewrite !bindA.
  rewrite -[in X in X `<=` _](_ : commute (slowsort ys') _ _); last first.
    exact/commute_plus/nondetPlus_sub_slowsort.
  rewrite (slowsort_preserves_size2 _
    (fun a b => writeList (i + b%:Z + 1) zs' >>
      (writeList (i + b%:Z) [:: p] >> writeList i a >> iqsort ((i + b%:Z + 1)%Z, size zs')))).
  rewrite bind_slowsort_guard [in X in _ `<=` X]bind_slowsort_guard.
  apply: refin_bindl => ys''.
  apply: refin_bind_guard => /eqP ys'ys''.
  rewrite -bindA -(writeListC _ _ ys''); last exact: leZZ.
  under [in X in _ `<=` X]eq_bind do rewrite -cat_rcons.
  under [in X in _ `<=` X]eq_bind do rewrite writeList_cat.
  rewrite (_ : commute (slowsort zs') _ _); last first.
    exact/commute_plus/nondetPlus_sub_slowsort.
  rewrite -(writeList_cat i ys'' [:: p]) -(writeListC _ _ _ zs'); last first.
    by rewrite size_cat /= intRD addZA; exact: leZZ.
  (* step 1i: ih *)
  rewrite cats1 bindA; apply: refin_bindl => -[].
  rewrite size_rcons natZS -Z.add_1_r -addZA; apply: ih.
  move: nxs; rewrite /= ltnS; apply: leq_ltn_trans.
  by rewrite -zszs' -(size_partition p xs) pxs /= leq_addl.
(* step 2: introduce_aswap_rcons *)
apply: (@refin_trans _ _ (tr_partl p [::] [::] xs >>= (fun '(ys, zs) =>
     writeList (i + (size ys)%:Z + 1) zs >>
     (writeList i (p :: ys) >> aswap i (i + (size ys)%:Z)) >>
     (iqsort (i, size ys)) >> iqsort ((i + (size ys)%:Z + 1)%Z, size zs)))); last first.
  apply: refin_bindl => -[ys sz].
  rewrite 4!bindA.
  apply: refin_bindl => -[].
  rewrite -2![in X in _ `<=` X]bindA.
  rewrite [in X in _ `<=` X](bindA _ (fun _ => iqsort _) (fun _ => iqsort _)).
  rewrite -2![in X in X `<=` _]bindA.
  rewrite (bindA _ (fun _ => iqsort _) (fun _ => iqsort _)).
  apply: refin_bindr.
  exact: refin_qperm_writeList_rcons.
(* step 3: commute *)
rewrite [X in _ `<=` X](_ : _ = tr_partl p [::] [::] xs >>= (fun '(ys, zs) =>
     aput i p >> writeList (i + 1)%Z (ys ++ zs) >>
     (aswap i (i + (size ys)%:Z)) >>
     (iqsort (i, size ys)) >> iqsort ((i + (size ys)%:Z + 1)%Z, size zs))); last first.
  bind_ext => -[ys zs].
  rewrite -bindA -writeListC; last first.
    by rewrite -addZA /= Z.add_1_r natZS; exact: leZZ.
  by rewrite /= bindA writeList_cat addZAC !bindA.
(* step 4: commute *)
rewrite [X in _ `<=` X](_ : _ = aput i p >>
   tr_partl p [::] [::] xs >>= (fun '(ys, zs) =>
   ( writeList (i + 1)%Z (ys ++ zs) >>
     (aswap i (i + (size ys)%:Z)) >>
     (iqsort (i, size ys)) >> iqsort ((i + (size ys)%:Z + 1)%Z, size zs)))); last first.
  rewrite [RHS]bindA -(_ : commute (tr_partl p [::] [::] xs) (aput i p) _); last first.
    exact/commute_plus/nondetPlus_sub_tr_partl.
  by bind_ext=> -[a b]; rewrite !bindA.
(* step 5 *)
rewrite [X in _ `<=` X](_ : _ = aput i p >>
  tr_partl p [::] [::] xs >>= (fun '(ys, zs) =>
    write2L (i + 1)%Z (ys, zs)) >>= (fun '(sys, szs) =>
     (aswap i (i + sys%:Z)) >>
     (iqsort (i, sys)) >> iqsort ((i + (sys)%:Z + 1)%Z, szs))); last first.
  rewrite [in RHS]bindA; bind_ext => -[a b].
  rewrite 2!bindA /write2L [RHS]bindA; bind_ext => -[].
  by rewrite bindretf bindA.
rewrite {nxs}.
(* step 6: refin_ipartl_tr_partl *)
rewrite [in X in _ `<=` X](bindA (aput i p)).
apply: refin_trans; last first.
  rewrite bindA.
  apply: refin_bindl => ttt.
  apply: refin_bindr.
  exact: refin_ipartl_tr_partl.
(* step 7 *)
rewrite -[in X in _ `<=` X]bindA.
rewrite (_ : aput i p >> _ = (writeList i (p :: xs) >> Ret p) >>=
    (fun p => ipartl p (i + 1)%Z 0 0 (size xs))); last first.
  rewrite /= bindA -[in LHS](bindA (aput i p)) [in RHS]bindA; bind_ext => -[].
  by rewrite 2!bindretf /uncurry3.
(* step 8 *)
rewrite writeListRet 2![in X in _ `<=` X]bindA.
apply: refin_bindl => -[].
rewrite /= iqsort_cons.
apply: refin_bindl => x.
rewrite ipartlE //= fmapE [in X in _ `<=` X]bindA.
under [in X in _ `<=` X]eq_bind do rewrite bindretf.
exact: refin_refl.
Qed.

End iqsort.
