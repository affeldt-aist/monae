(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2023 monae authors, license: LGPL-2.1-or-later               *)
Require Import Morphisms.
From mathcomp Require Import all_ssreflect.
From HB Require Import structures.
Require Import preamble hierarchy monad_lib typed_store_lib.
Require Import typed_store_universe.

(**md**************************************************************************)
(* # Application of the Delay-typedstore monad                                *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.

Module CoqTypeNat.
Import MLTypes CoqTypeNat.

Definition delayTypedStoreMonad (N : monad) :=
  delaytypedStoreMonad ml_type N nat.

Section setoid.
Variables (N : monad) (M : delayTypedStoreMonad N).
Import Setoid.

(* TODO: move *)
#[global] Add Parametric Morphism A B : bind with signature
  (@wBisim M A) ==> (pointwise_relation A (@wBisim M B)) ==> (@wBisim M B)
  as bindmor_delaystate.
Proof.
move => x y Hxy f g Hfg; apply: wBisim_trans.
- exact: (bindmwB _ _ _ _ _ Hxy).
- exact: (bindfwB _ _ _ _ y Hfg).
Qed.

End setoid.

Section factorial.
Variables (N : monad) (M : delayTypedStoreMonad N).

Local Notation coq_type := hierarchy.coq_type.
Local Open Scope do_notation.

Let factdts_body (r : loc ml_int) n : M (unit + nat)%type :=
  do v <- cget r;
  if n is m.+1 then do _ <- cput r (n * v); Ret (inr m)
               else Ret (inl tt).

Let while_factdtsE n r :
  while (factdts_body r) n ≈ do s <- cget r; cput r (n`! * s).
Proof.
elim: n => /= [|m IH].
  rewrite fixpointE/= !bindA.
  under [x in _ ≈ x]eq_bind => s do rewrite fact0 mul1n.
  rewrite cgetputskip.
  by under eq_bind do rewrite bindretf.
rewrite fixpointE/= bindA.
under eq_bind => s do rewrite bindA bindretf/=.
setoid_rewrite IH.
by under eq_bind do rewrite cputget cputput mulnA (mulnC m`! _).
Qed.

Definition factdts n :=
  do r <- cnew ml_int 1;
  do _ <- while (factdts_body r) n ;
  cget r.

Lemma factdtsE n : factdts n ≈ cnew ml_int n`! >> Ret n`!.
Proof.
rewrite /factdts.
setoid_rewrite while_factdtsE.
under eq_bind do rewrite bindA.
by rewrite cnewget cnewput muln1 cnewgetret.
Qed.

End factorial.

End CoqTypeNat.
