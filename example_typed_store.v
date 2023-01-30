(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2020 monae authors, license: LGPL-2.1-or-later               *)
Require Import ZArith.
From mathcomp Require Import all_ssreflect.
From mathcomp Require boolp.
From infotheo Require Import ssrZ.
Require Import monae_lib hierarchy. (*monad_lib fail_lib state_lib.*)

(******************************************************************************)
(*                         Type store examples                                *)
(*                                                                            *)
(******************************************************************************)

Local Open Scope monae_scope.

Inductive ml_type : Set :=
  | ml_int
  | ml_bool
  | ml_unit
  | ml_ref (_ : ml_type)
  | ml_arrow (_ : ml_type) (_ : ml_type)
  | ml_undef.

Inductive undef_t : Set := Undef.

Module MLtypes.
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

Local Definition ml_type := ml_type.
Local Definition undef := Undef.
Variant loc : ml_type -> Type := mkloc T : nat -> loc T.

Section with_monad.
Context [M : Type -> Type].

Local (* Generated type translation function *)
Fixpoint coq_type (T : ml_type) : Type :=
  match T with
  | ml_int => nat
  | ml_bool => bool
  | ml_unit => unit
  | ml_arrow T1 T2 => coq_type T1 -> M (coq_type T2)
  | ml_ref T1 => loc T1
  | ml_undef => undef_t
  end.
End with_monad.
Local Definition ml_undef := ml_undef.
End MLtypes.

Module IMonadTS := MonadTypedStore (MLtypes).
Import MLtypes.
Import IMonadTS.

Lemma cgetret (M : typedStoreMonad) T :
  cget T = fun r => (cget _ r : M _) >>= Ret.
Proof. by apply boolp.funext => r; rewrite bindmret. Qed.

Section factorial.
Variable M : typedStoreMonad.
Local Definition coq_type := @MLtypes.coq_type M.

Fixpoint fact_ref (r : loc ml_int) (n : nat) : M unit :=
  if n is m.+1 then cget _ r >>= fun p => cput _ r (n * p) >> fact_ref r m
  else Ret tt.

Theorem fact_ref_ok n :
  crun _ (cnew ml_int 1 >>= fun r => fact_ref r n >> cget _ r) =
    Some (fact_rec n).
Proof.
set fn := fact_rec n.
set m := n.
set s := 1.
have smn : s * fact_rec m = fn by rewrite mul1n.
elim: m s smn => [|m IH] s /= smn.
  rewrite /fact_ref -smn muln1.
  under [fun r => _]boolp.funext do rewrite bindretf.
  by rewrite cgetret cnewget crunret // crunnew.
under [fun r => _]boolp.funext do rewrite bindA.
rewrite cnewget.
under [fun r => _]boolp.funext do rewrite bindA.
rewrite (cnewput ml_int s _ _ (fun r s => fact_ref r m >> cget ml_int r)).
by rewrite IH // (mulnC m.+1) -mulnA.
Qed.
End factorial.
