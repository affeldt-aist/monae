From mathcomp Require Import all_ssreflect.
From mathcomp Require boolp.
Require Import monae_lib hierarchy monad_lib fail_lib state_lib.
From infotheo Require Import ssr_ext.

(*******************************************************************************)
(*                                   wip                                       *)
(*******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope order_scope.
Import Order.TTheory.
Local Open Scope monae_scope.
Local Open Scope tuple_ext_scope.

From infotheo Require Import ssrZ.
Require Import ZArith.

(* TODO: Pr to infotheo *)
Local Open Scope zarith_ext_scope.

Reserved Notation "n %:Z" (at level 2, left associativity, format "n %:Z").
Definition natZ := nosimpl Z_of_nat.
Notation "n %:Z" := (natZ n) : zarith_ext_scope.

Notation "z .+1Z" := (Z.succ z) (at level 2, left associativity,
  format "z .+1Z") : zarith_ext_scope.

Lemma add1Z z : (1 + z)%Z = z.+1Z.
Proof. by rewrite Z.add_1_l. Qed.

Lemma natZ0 : 0%:Z = 0%Z. Proof. exact: Nat2Z.inj_0. Qed.

Lemma natZS n : n.+1%:Z = n%:Z.+1Z.
Proof. by rewrite -Zpos_P_of_succ_nat. Qed.

Local Close Scope zarith_ext_scope.
(* TODO: Pr to infotheo (end) *)

Section marray.
Variables (E : UU0) (M : arrayMonad E Z_eqType).

Fixpoint readList (i : Z) (n : nat) : M (seq E) :=
  if n isn't k.+1 then Ret [::] else liftM2 cons (aGet i) (readList (i + 1) k).

Fixpoint writeList (i : Z) (s : seq E) : M unit :=
  if s isn't x :: xs then Ret tt else aPut i x >> writeList (i + 1) xs.

Definition writeL (i : Z) (s : seq E) := writeList i s >> Ret (size s).

Definition write2L (i : Z) '(s1, s2) :=
  writeList i (s1 ++ s2) >> Ret (size s1, size s2).

Definition write3L i '(xs, ys, zs) :=
  writeList i (xs ++ ys ++ zs) >> Ret (size xs, size ys, size zs).

Local Open Scope zarith_ext_scope.

Lemma writeList_cat (i : Z) (xs ys : seq E) :
  writeList i (xs ++ ys) = writeList i xs >> writeList (i + (size xs)%:Z) ys.
Proof.
elim: xs i => [|h t ih] i /=; first by rewrite bindretf addZ0.
by rewrite ih bindA -addZA add1Z natZS.
Qed.

End marray.
