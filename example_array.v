(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2020 monae authors, license: LGPL-2.1-or-later               *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require boolp.
Require Import monae_lib hierarchy monad_lib fail_lib state_lib example_quicksort.
From infotheo Require Import ssr_ext.

(*******************************************************************************)
(*                                   wip                                       *)
(*******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope order_scope.
Import Order.Theory.
Local Open Scope monae_scope.
Local Open Scope tuple_ext_scope.

From infotheo Require Import ssrZ.
Require Import ZArith.

Section marray.
(* Variables (E : UU0) (M : arrayMonad E Z_eqType).
Variables (d : unit) (T : porderType d). *)

Variable (d : unit) (E : porderType d) (M : plusArrayMonad E Z_eqType).

Fixpoint readList (i : Z) (n : nat) : M (seq E) :=
  if n isn't k.+1 then Ret [::] else liftM2 cons (aget i) (readList (i + 1) k).

Fixpoint writeList (i : Z) (s : seq E) : M unit :=
  if s isn't x :: xs then Ret tt else aput i x >> writeList (i + 1) xs.

Definition writeL (i : Z) (s : seq E) := writeList i s >> Ret (size s).

Definition write2L (i : Z) '(s1, s2) :=
  writeList i (s1 ++ s2) >> Ret (size s1, size s2).

Definition write3L (i : Z) '(xs, ys, zs) :=
  writeList i (xs ++ ys ++ zs) >> Ret (size xs, size ys, size zs).

Definition swap (i j : Z) : M unit := 
  aget i >>= (fun x => aget j >>= (fun y => aput i y >> aput j x)).

Fixpoint partl (p : E) (s : (seq E * seq E)%type) (xs : seq E)
    : (seq E * seq E)%type :=
  match xs with
  | [::] => s
  | x :: xs => if x <= p then partl p (s.1 ++ [:: x], s.2) xs
                         else partl p (s.1, s.2 ++ [:: x]) xs
  end.

Definition second {A B C} (f : B -> M C) (xy : (A * B)%type) := 
  f xy.2 >>= (fun y' => Ret (xy.1, y')).

(* Unset Guard Checking. *)
(* Program Fixpoint partl' (p : E) (s : (seq E * seq E * seq E)) 
    : M (seq E * seq E)%type :=
  match s with
  | (ys, zs, [::]) => Ret (ys, zs)
  | (ys, zs, x :: xs) => 
    if x <= p then (@qperm _ _ zs) >>= 
                (fun zs' => partl' p (ys ++ [:: x], zs', xs))
              else partl' p (ys, zs ++ [:: x], xs)
  end. *)

(* Definition dispatch (x p : E) '(ys, zs, xs) := 
  if x <= p then perm zs >>= (fun zs' => Ret (ys ++ [:: x], zs', xs))
            else perm (zs ++ [:: x]) >>= (fun zs' => Ret (ys, zs', zs)). *)

Lemma ipartl_spec (i : Z) (p : E) (ys zs xs : seq E) 
    (ipartl : E -> Z -> (nat * nat * nat)%type -> M (nat * nat)%type) : 
  writeList i (ys ++ zs ++ xs) >> ipartl p i (size ys, size zs, size xs)
  `<=` second perm (partl p (ys, zs) xs) >>= write2L i.
Proof. Admitted.

Local Open Scope zarith_ext_scope.

Lemma writeList_cat (i : Z) (xs ys : seq E) :
  writeList i (xs ++ ys) = writeList i xs >> writeList (i + (size xs)%:Z) ys.
Proof.
elim: xs i => [|h t ih] i /=; first by rewrite bindretf addZ0.
by rewrite ih bindA -addZA add1Z natZS.
Qed.

(*
Fixpoint ipartl (p : E) (i : Z) (ny nz : nat) (nx : nat) : M (nat * nat)%type := 
  match nx with
  | 0 => Ret (ny, nz)
  | k.+1 => aget ((* i + *) (ny + nz)%:Z) >>= (fun x => (* TODO *)
         if x <= p then swap (i + ny%:Z) (i + ny%:Z + nz%:Z) >> ipartl p i (ny + 1) nz k
                   else ipartl p i ny (nz.+1) k)
  end.

(* Program Fixpoint iqsort (i : Z) (n : nat) : M unit := 
  match n with
  | 0 => Ret tt
  | n.+1 => aget i >>= (fun p =>
         ipartl p (i) 0 0 n >>= (fun '(ny, nz) =>
         swap i (i + ny%:Z) >>
         iqsort i ny >> iqsort (ny%:Z) nz))
  end. *)

(* Lemma lemma12 {i : Z} {xs : seq E} {p : E} : 
  writeList i xs >> iqsort i (size xs) `<=` _.
Proof. *)

(* Lemma lemma13 {i : Z} {ys : seq E} {p : E} : 
  perm ys >>= (fun ys' => writeList i (ys' ++ [:: p])) `>=` 
  writeList i (p :: ys) >> swap i (i + (size ys)%:Z).
Proof. *)
  
(* Qed. *)

*)
Lemma write_read {i : Z} {p} : aput i p >> aget i = aput i p >> Ret p :> M _.
Proof. by rewrite -[RHS]aputget bindmret. Qed.

Lemma write_readC {i j : Z} {p} : 
  i != j -> aput i p >> aget j = aget j >>= (fun v => aput i p >> Ret v) :> M _.
Proof. by move => ?; rewrite -aputgetC // bindmret. Qed.

Lemma writeList_rcons {i : Z} (x : E) (xs : seq E) :
  writeList i (rcons xs x) = writeList i xs >> aput (i + (size xs)%:Z)%Z x.
Proof. by rewrite -cats1 writeList_cat /= -bindA bindmskip. Qed.

Lemma introduce_read {i : Z} (p : E) (xs : seq E) :
  writeList i (p :: xs) >> Ret p =
  writeList i (p :: xs) >> aget i.
Proof.
  rewrite /=.
  elim/last_ind: xs p i => [/= p i|].
  by rewrite bindmskip write_read.
  move => h t ih p i /=.
  transitivity (
    (aput i p >> writeList (i + 1) h >> aput (i + 1 + (size h)%:Z)%Z t) >> aget i
  ); last first.
  by rewrite writeList_rcons !bindA.
  rewrite ![RHS]bindA.
  rewrite write_readC.
  rewrite -2![RHS]bindA -ih [RHS]bindA.
  transitivity (
    (aput i p >> writeList (i + 1) h >> aput (i + 1 + (size h)%:Z)%Z t) >> Ret p
  ).
  by rewrite writeList_rcons !bindA.
  rewrite !bindA.
  bind_ext => ?.
  bind_ext => ?.
  by rewrite bindretf.
  apply/negP =>/eqP/esym.
  apply ltZ_eqF.
  rewrite -{1}(addZ0 i) -addZA ltZ_add2l.
  apply addZ_gt0wl => //.
  apply/leZP.
  rewrite -natZ0 -leZ_nat //. (* TODO: cleanup *)
Qed.

Section dipartl.
Variables (p : E) (i : Z) (nx : nat).

Local Open Scope nat_scope.
Local Obligation Tactic := idtac.

Let nx_pair : Type := {x : nat * nat | x.1 + x.2 <= nx}.

Let rel_nx_pair : rel nx_pair := fun x y =>
  let x1 := (sval x).1 in let x2 := (sval x).2 in
  let y1 := (sval y).1 in let y2 := (sval y).2 in
  nx - x1 - x2 < nx - y1 - y2.

Lemma well_founded_rel_nx_pair : well_founded rel_nx_pair.
Proof.
apply: (@well_founded_lt_compat _ (fun x => nx - (sval x).1 - (sval x).2)).
by move=> x y ?; apply/ssrnat.ltP.
Qed.

Program Fixpoint dipartl' (nynz : nx_pair)
    (f : forall x, rel_nx_pair x nynz -> M nx_pair) : M nx_pair :=
  let ny := (sval nynz).1 in
  let nz := (sval nynz).2 in
  match Bool.bool_dec (ny + nz == nx) true with
  | left H =>  Ret _(*ny,nz*)
  | right H => aget (i + (ny + nz)%:Z)%Z >>= (fun x =>
    if (x <= p)%O then
      swap (i + ny%:Z)%Z (i + ny%:Z + nz%:Z)%Z >> @f _ _ (*ny.+1,nz*)
    else
      @f _ _ (*ny,nz.+1*))
  end.
Next Obligation.
by move=> [nynz ?] /= _ _ _; exists nynz.
Defined.
Next Obligation.
move=> [[ny nz] nynz] /= _ /negP H _ _ _.
exists (ny.+1, nz).
rewrite /= leq_eqVlt (negbTE H) /= in nynz *.
by rewrite addSn.
Defined.
Next Obligation.
move=> [[ny nz] nynz] /= _ /negP H _ _ _ /=; rewrite /rel_nx_pair /=.
have {}nynz : ny + nz < nx by move: nynz; rewrite /= ltn_neqAle H.
destruct nx as [|nx'] => //.
by rewrite subSS -2!subnDA subSn.
Defined.
Next Obligation.
move=> [[ny nz] nynz] /= _ + _ => /negP H.
exists (ny, nz.+1).
rewrite /= leq_eqVlt (negbTE H) /= in nynz *.
by rewrite addnS.
Defined.
Next Obligation.
move=> [[ny nz] nynz] /= _ /negP H _ _ /=; rewrite /rel_nx_pair /=.
have {}nynz : ny + nz < nx by move: nynz; rewrite /= ltn_neqAle H.
destruct nx as [|nx'] => //.
by rewrite subnS prednK // -subnDA subn_gt0.
Qed.

Definition dipartl : nx_pair -> M nx_pair :=
  Fix well_founded_rel_nx_pair (fun _ => M _) dipartl'.

End dipartl.

Print exist.

(*Program Definition ipartl (p : E) (i : Z) (ny nz : nat) (nx : nat) :=
  (@dipartl p i nx (exist (fun x => x.1 + x.2 <= nx) (ny, nz) _)).*)

Fixpoint ipartl (p : E) (i : Z) (ny nz : nat) (nx : nat) : M (nat * nat)%type :=
  match nx with
  | 0 => Ret (ny, nz)
  | k.+1 => aget (i + (ny + nz)%:Z)%Z >>= (fun x => (* TODO *)
           if x <= p then
             swap (i + ny%:Z) (i + ny%:Z + nz%:Z) >> ipartl p i ny.+1 nz k
           else
             ipartl p i ny nz.+1 k)
  end.

Local Obligation Tactic := idtac.
Program Fixpoint iqsort' (ni : (Z * nat))
    (f : forall (n'j : (Z * nat)), (n'j.2 < ni.2)%coq_nat -> M unit) : M unit :=
  match ni.2 with
  | 0 => Ret tt
  | n.+1 => aget ni.1 >>= (fun p =>
            @dipartl p (ni.1 + 1)%Z n
              (exist (fun x => x.1 + x.2 <= n) (0, 0) isT) >>= (fun nynz =>
              let ny := (sval nynz).1 in
              let nz := (sval nynz).2 in
              swap ni.1 (ni.1 + ny%:Z) >>
              f (ni.1, ny) _ >> f ((ni.1 + ny%:Z + 1)%Z, nz) _))
  end.
Next Obligation.
move => [i [//|_]] /= _ n [<-] p [] [ny nz] /= nynz _.
apply/ssrnat.ltP; rewrite ltnS.
rewrite (leq_trans _ nynz) //.
rewrite leq_addr //.
Qed.
Next Obligation.
move => [i [//|_]] /= _ n [<-] p [] [ny nz] /= nynz _.
apply/ssrnat.ltP; rewrite ltnS.
rewrite (leq_trans _ nynz) //.
rewrite leq_addl //.
Qed.

Lemma well_founded_lt2 : well_founded (fun x y : (Z * nat) => (x.2 < y.2)%coq_nat).
Proof. 
  apply: (@well_founded_lt_compat _ _).
  move => [x1 x2] [y1 y2]; exact.
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

Lemma iqsort_nil {i : Z} : iqsort (i, 0) = Ret tt.
Proof. rewrite /iqsort Fix_eq //; exact: iqsort'_Fix. Qed.

Lemma iqsort_cons {i : Z} {n : nat}: iqsort (i, n.+1) = aget i >>= (fun p =>
@dipartl p (i + 1)%Z n
  (exist (fun x => x.1 + x.2 <= n) (0, 0) isT) >>= (fun nynz =>
  let ny := (sval nynz).1 in
  let nz := (sval nynz).2 in
  swap i (i + ny%:Z) >>
  iqsort (i, ny) >> iqsort ((i + ny%:Z + 1)%Z, nz))).
Proof. rewrite [in LHS]/iqsort Fix_eq //=; exact: iqsort'_Fix. Qed.

Lemma lemma12 {i : Z} {xs : seq E} {p : E} : 
  writeList i xs >> iqsort (i, (size xs)) `<=` (slowsort M xs) >> writeList i xs.
Proof. 
  have [n nxs] := ubnP (size xs); elim: n xs => // n ih xs in nxs *.
Admitted.

Lemma lemma13 {i : Z} {ys : seq E} {p : E} : 
  perm ys >>= (fun ys' => writeList i (ys' ++ [:: p])) `>=` 
  writeList i (p :: ys) >> swap i (i + (size ys)%:Z).
Proof. Abort.

End marray.
