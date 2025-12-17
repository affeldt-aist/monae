(* monae: Monadic equational reasoning in Rocq                                *)
(* Copyright (C) 2025 monae authors, license: LGPL-2.1-or-later               *)
From mathcomp Require Import all_ssreflect ssralg ssrnum finmap.
From mathcomp Require Import boolp classical_sets reals.
From infotheo Require Import classical_sets_ext realType_ext fdist proba.
From infotheo Require Import fsdist convex necset.
Require category.
From HB Require Import structures.
Require Import preamble hierarchy monad_lib proba_lib.
Require Import monad_model proba_model gcm_model.
Require Import category.

(**md**************************************************************************)
(* # Model of the monad type altProbMonad                                     *)
(*                                                                            *)
(* ```                                                                        *)
(* gcmAP == model of a monad that combines non-deterministic choice and       *)
(*          probability, built on top of the geometrically convex monad       *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope proba_scope.
Local Open Scope category_scope.

Section P_delta_altProbMonad.
Variable R : realType.
Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope classical_set_scope.
Local Open Scope convex_scope.
Local Open Scope latt_scope.
Local Open Scope monae_scope.

Definition alt A (x y : gcm R A) : gcm R A := x [+] y.
Definition choice p A (x y : gcm R A) : gcm R A := x <| p |> y.

Lemma altA A : ssrfun.associative (@alt A).
Proof. by move=> x y z; rewrite /alt lubA. Qed.

Lemma image_fsdistmap A B (x : gcm R A) (k : choice_of_Type A -> gcm R B) :
  fsdistmap k @` x = (gcm R # k) x.
Proof.
rewrite /hierarchy.actm/= /actm 5!FCompE /category.actm/=.
by rewrite /free_semiCompSemiLattConvType_mor/=; unlock.
Qed.

Section funalt_funchoice.
Import category.
Import comps_notation.
Local Notation F1 := free_semiCompSemiLattConvType.
Local Notation F0 := free_convType.
Local Notation FC := free_choiceType.
Local Notation UC := forget_choiceType.
Local Notation U0 := forget_convType.
Local Notation U1 := forget_semiCompSemiLattConvType.

Lemma FunaltDr (A B : Type) (x y : gcm R A) (k : A -> gcm R B) :
  (gcm R # k) (x [+] y) = (gcm R # k) x [+] (gcm R # k) y.
Proof.
rewrite /hierarchy.actm /= /Monad_of_category_monad.actm /=.
by rewrite scsl_hom_is_lubmorph.
Qed.

Lemma FunpchoiceDr (A B : Type) (x y : gcm R A) (k : A -> gcm R B) p :
  (gcm R # k) (x <|p|> y) = (gcm R # k) x <|p|> (gcm R # k) y.
Proof.
rewrite /hierarchy.actm /= /Monad_of_category_monad.actm /=.
by rewrite scsl_hom_is_affine.
Qed.
End funalt_funchoice.

Section bindaltDl.
Import category.
Import comps_notation.
Local Notation F1 := (free_semiCompSemiLattConvType R).
Local Notation F0 := (free_convType R).
Local Notation FC := free_choiceType.
Local Notation UC := forget_choiceType.
Local Notation U0 := (forget_convType R).
Local Notation U1 := (forget_semiCompSemiLattConvType R).

Lemma affine_F1e0U1PD_alt T (u v : gcm R (gcm R T)) :
  (F1 # eps0 R (U1 (P_delta_left R T)))%category (u [+] v) =
  (F1 # eps0 R (U1 (P_delta_left R T)))%category u [+]
  (F1 # eps0 R (U1 (P_delta_left R T)))%category v.
Proof. exact: scsl_hom_is_lubmorph. Qed.

Lemma affine_e1PD_alt T (x y : el (F1 (FId (U1 (P_delta_left R T))))) :
  (eps1 R (P_delta_left R T)) (x [+] y) =
  (eps1 R (P_delta_left R T)) x [+] (eps1 R (P_delta_left R T)) y.
Proof. exact: scsl_hom_is_lubmorph. Qed.

(*
Local Notation F1o := necset_semiCompSemiLattConvType.
*)
Local Notation F0o := FSDist.t. (*FSDist_t__canonical__isConvexSpace__ConvexSpace. (* FIXME *)*)
Local Notation FCo := choice_of_Type.
Local Notation F1m := free_semiCompSemiLattConvType_mor.
Local Notation F0m := free_convType_mor.

Lemma bindaltDl : BindLaws.left_distributive (@hierarchy.bind (gcm R)) alt.
Proof.
move=> A B x y k.
rewrite hierarchy.bindE /= /join_ -category.bindE.
by rewrite scsl_hom_is_lubmorph.
Qed.
End bindaltDl.

HB.instance Definition _ :=
  @isMonadAlt.Build (Monad_of_category_monad.acto (Mgcm R)) alt altA bindaltDl.

Lemma altxx A : idempotent_op (@alt A).
Proof. by move=> x; rewrite /= /alt lubxx. Qed.
Lemma altC A : commutative (@alt A).
Proof. by move=> a b; rewrite /= /alt /= lubC. Qed.

HB.instance Definition _ :=
  @isMonadAltCI.Build (Monad_of_category_monad.acto (Mgcm R)) altxx altC.

Definition gcmACI := [the altCIMonad of gcm R].

Lemma choice1 A (x y : gcm R A) : x <| 1%:pr |> y = x.
Proof. by rewrite conv1. Qed.
Lemma choiceC A p (x y : gcm R A) : x <|p|> y = y <|(Prob.p p).~%:pr|> x.
Proof. by rewrite convC. Qed.
Lemma choicemm A p : idempotent_op (@choice p A).
Proof. by move=> m; rewrite /choice convmm. Qed.

Let choiceA A (p q : {prob R}) (x y z : gcm R A) :
  x <| p |> (y <| q |> z) = (x <| [r_of p, q] |> y) <| [s_of p, q] |> z.
Proof. exact: convA. Qed.

Section bindchoiceDl.
Import category.
Import comps_notation.
Local Notation F1 := (free_semiCompSemiLattConvType R).
Local Notation F0 := (free_convType R).
Local Notation FC := free_choiceType.
Local Notation UC := forget_choiceType.
Local Notation U0 := (forget_convType R).
Local Notation U1 := (forget_semiCompSemiLattConvType R).

Lemma affine_F1e0U1PD_conv T (u v : gcm R (gcm R T)) p :
  ((F1 # eps0 R (U1 (P_delta_left R T))) (u <|p|> v) =
   (F1 # eps0 R (U1 (P_delta_left R T))) u <|p|>
   (F1 # eps0 R (U1 (P_delta_left R T))) v)%category.
Proof. exact: scsl_hom_is_affine. Qed.

Lemma affine_e1PD_conv T (x y : el (F1 (FId (U1 (P_delta_left R T))))) p :
  (eps1 R (P_delta_left R T)) (x <|p|> y) =
  (eps1 R (P_delta_left R T)) x <|p|> (eps1 R (P_delta_left R T)) y.
Proof. exact: scsl_hom_is_affine. Qed.

(*Local Notation F1o := necset_semiCompSemiLattConvType.*)
Local Notation F0o := FSDist.t.
Local Notation FCo := choice_of_Type.
Local Notation F1m := (@free_semiCompSemiLattConvType_mor R).
Local Notation F0m := (@free_convType_mor R).

Lemma bindchoiceDl p :
  BindLaws.left_distributive (@hierarchy.bind (gcm R)) (@choice p).
Proof.
move=> A B x y k.
rewrite hierarchy.bindE /= /join_ -category.bindE.
exact: scsl_hom_is_affine.
Qed.

End bindchoiceDl.

HB.instance Definition _ :=
  isMonadConvex.Build R (Monad_of_category_monad.acto (Mgcm R))
    choice choice1 choiceC choicemm choiceA.

HB.instance Definition _ :=
  isMonadProb.Build R (Monad_of_category_monad.acto (Mgcm R)) bindchoiceDl.

Lemma choicealtDr A (p : {prob R}) :
  right_distributive (fun x y : Mgcm R A => x <| p |> y) (@alt A).
Proof. by move=> x y z; rewrite /choice lubDr. Qed.

HB.instance Definition _ :=
  @isMonadAltProb.Build R (Monad_of_category_monad.acto (Mgcm R)) choicealtDr.

Definition gcmAP := [the altProbMonad R of gcm R].

End P_delta_altProbMonad.

Section probabilisctic_choice_not_trivial.
Variable R : realType.
Local Open Scope proba_monad_scope.

(* An example that probabilistic choice in this model is not trivial:
   we can distinguish different probabilities. *)

Example gcmAP_choice_nontrivial (p q : {prob R}) :
  p <> q ->
  (* Ret = hierarchy.ret *)
  Ret true <|p|> Ret false <>
  Ret true <|q|> Ret false :> (gcmAP R : convexMonad R) bool.
Proof.
apply contra_not.
rewrite !gcm_retE /hierarchy.choice => /(congr1 (@NECSet.sort _ _)).
rewrite /= !necset_convType.convE !conv_cset1 /=.
move/(@set1_inj _ (conv _ _ _))/(congr1 (@FSDist.f _ _))/fsfunP/(_ true).
rewrite !fsdist_convE !fsdist1xx !fsdist10//; last exact/eqP. (*TODO: we should not need that*)
by rewrite !avgRE !mulr1 ?mulr0 ?addr0 => /val_inj.
Qed.

End probabilisctic_choice_not_trivial.
