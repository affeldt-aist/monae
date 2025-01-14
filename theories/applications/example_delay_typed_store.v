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

Definition factdts_aux_body (r : loc ml_int) (n : nat) : M (unit + nat)%type  :=
        do v <- cget r;
        match n with
          |O => do _ <- cput r v; Ret (inl tt)
          |m.+1 => do _ <- cput r (n * v); Ret (inr m)
        end.
Definition factn_aux (n: nat) (r : loc ml_int) :=
  do s <- cget r;
  do _ <- cput r (n`! * s); @ret M _ tt.
Definition factdts_aux (n : nat) (r : loc ml_int) := while (factdts_aux_body r) n.

Lemma factE_aux (n : nat) (r : loc ml_int) : factdts_aux n r ≈ factn_aux n r.
Proof.
rewrite/factdts_aux/factn_aux.
elim: n => /= [|n' IH].
  rewrite fixpointE/= !bindA.
  by under eq_bind => s do rewrite bindA bindretf/= -{1}(mul1n s).
rewrite fixpointE/= bindA.
under eq_bind => s do rewrite bindA bindretf/=.
setoid_rewrite IH.
by under eq_bind => x do rewrite cputget -bindA cputput mulnA (mulnC n'`! _).
Qed.

Definition factdts n := do r <- cnew ml_int 1;
                        do _ <- factdts_aux n r ;
                        do v <- cget r; Ret v.
Definition factn n := do r <- cnew ml_int n`!;
                      do v <- cget r; @ret M _ v.

Lemma factE n : factdts n ≈ factn n.
Proof.
rewrite/factdts/factn.
setoid_rewrite factE_aux.
under eq_bind => r.
  rewrite bindA.
  under eq_bind => x do rewrite bindA bindretf.
  over.
by rewrite cnewget cnewput muln1.
Qed.
End factorial.
