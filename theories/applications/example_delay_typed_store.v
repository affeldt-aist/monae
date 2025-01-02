(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2023 monae authors, license: LGPL-2.1-or-later               *)
Require Import ZArith Morphisms.
From mathcomp Require Import all_ssreflect ssrnat.
From mathcomp Require boolp.
From infotheo Require Import ssrZ.
Require Import monad_model.
From HB Require Import structures.
Require Import preamble hierarchy monad_lib typed_store_lib.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.

(******************************************************************************)
(*                             generated by coqgen                            *)
(******************************************************************************)
Module MLTypes.
Inductive ml_type : Set :=
  | ml_int
  | ml_bool
  | ml_unit
  | ml_ref (_ : ml_type)
  | ml_arrow (_ : ml_type) (_ : ml_type)
  | ml_rlist (_ : ml_type).

Definition ml_type_eq_dec (T1 T2 : ml_type) : {T1=T2}+{T1<>T2}.
revert T2; induction T1; destruct T2;
  try (right; intro; discriminate); try (now left);
  try (case (IHT1_5 T2_5); [|right; injection; intros; contradiction]);
  try (case (IHT1_4 T2_4); [|right; injection; intros; contradiction]);
  try (case (IHT1_3 T2_3); [|right; injection; intros; contradiction]);
  try (case (IHT1_2 T2_2); [|right; injection; intros; contradiction]);
  (case (IHT1 T2) || case (IHT1_1 T2_1)); try (left; now subst);
    right; injection; intros; contradiction.
Defined.

Definition val_nonempty (M : UU0 -> UU0) := tt.

Notation loc := (@loc _ monad_model.locT_nat).

Inductive rlist (a : Type) (a_1 : ml_type) :=
  | Nil
  | Cons (_ : a) (_ : loc (ml_rlist a_1)).

Definition ml_type_eq_mixin := hasDecEq.Build _ (comparePc MLTypes.ml_type_eq_dec).
HB.instance Definition ml_type_eqType := ml_type_eq_mixin.

End MLTypes.
(******************************************************************************)

Module CoqTypeNat.
Import MLTypes.

Section with_monad.
Context [M : Type -> Type].

Fixpoint coq_type_nat (T : ml_type) : Type :=
  match T with
  | ml_int => nat
  | ml_bool => bool
  | ml_unit => unit
  | ml_arrow T1 T2 => coq_type_nat T1 -> M (coq_type_nat T2)
  | ml_ref T1 => loc T1
  | ml_rlist T1 => rlist (coq_type_nat T1) T1
  end.
End with_monad.

HB.instance Definition _ := @isML_universe.Build ml_type coq_type_nat ml_unit val_nonempty.

Definition delayTypedStoreMonad (N : monad) :=
  delaytypedStoreMonad ml_type N monad_model.locT_nat.

Section factorial.
Variables (N : monad) (M : delayTypedStoreMonad N).
Local Notation coq_type := hierarchy.coq_type.
Local Open Scope do_notation.

Definition factdts_aux_body (r : loc ml_int) (n : nat) : M (unit + nat)%type  :=
        do v <- cget r;
        match n with
          |O => do _ <- cput r v; Ret (inl tt)
          |S m => do _ <- cput r (n*v); Ret (inr m)
        end.

Definition factn_aux (n: nat) (r : loc ml_int) :=
  do s <- cget r;
  do _ <- cput r (factorial n * s); @ret M _ tt.
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
by under eq_bind => x do rewrite cputget -bindA cputput mulnA (mulnC (factorial n') _).
Qed.

Definition factdts n := do r <- cnew ml_int 1;
                        do _ <- factdts_aux n r ;
                        do v <- cget r; Ret v.
Definition factn n := do r <- cnew ml_int (factorial n);
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
