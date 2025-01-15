(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2023 monae authors, license: LGPL-2.1-or-later               *)
Require Import Morphisms.
From mathcomp Require Import all_ssreflect.
From HB Require Import structures.
Require Import preamble hierarchy monad_lib typed_store_lib.
Require Import typed_store_universe.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.

Module CoqTypeNat.
Import MLTypes CoqTypeNat.

Definition delayTypedStoreMonad (N : monad) :=
  delaytypedStoreMonad ml_type N nat.

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
elim: n => /= [|n' IH].
  rewrite fixpointE/= !bindA.
  under [x in _ ≈ x]eq_bind => s do rewrite fact0 mul1n.
  rewrite cgetputskip.
  by under eq_bind do rewrite bindretf.
rewrite fixpointE/= bindA.
under eq_bind => s do rewrite bindA bindretf/=.
setoid_rewrite IH.
by under eq_bind do rewrite cputget cputput mulnA (mulnC n'`! _).
Qed.

Definition factdts n :=
  do r <- cnew ml_int 1;
  do _ <- while (factdts_body r) n ;
  cget r.

Lemma factdtsE n : factdts n ≈ cnew ml_int n`! >> Ret n`!.
Proof.
rewrite/factdts.
setoid_rewrite factdts_loopE.
under eq_bind do rewrite bindA.
by rewrite cnewget cnewput muln1 cnewgetret.
Qed.
End factorial.
