(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2020 monae authors, license: LGPL-2.1-or-later               *)
Require Import Reals.
From mathcomp Require Import all_ssreflect ssralg ssrnum finmap.
From mathcomp Require Import boolp classical_sets.
From mathcomp Require Import reals Rstruct.
From infotheo Require Import classical_sets_ext Reals_ext Rbigop ssrR fdist.
From infotheo Require Import ssrR Reals_ext proba.
From infotheo Require Import Reals_ext realType_ext.
From infotheo Require Import fsdist convex necset.
Require category.
From HB Require Import structures.
Require Import monae_lib hierarchy monad_lib proba_lib monad_model gcm_model.
Require Import category.

(******************************************************************************)
(*                  Model of the monad type altProbMonad                      *)
(*                                                                            *)
(* gcmAP == model of a monad that combines non-deterministic choice and       *)
(*          probability, built on top of the geometrically convex monad       *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope proba_scope.
Local Open Scope category_scope.

Section P_delta_altProbMonad.
Local Open Scope R_scope.
Local Open Scope reals_ext_scope.
Local Open Scope classical_set_scope.
Local Open Scope convex_scope.
Local Open Scope latt_scope.
Local Open Scope monae_scope.

Definition alt A (x y : gcm A) : gcm A := x [+] y.
Definition choice p A (x y : gcm A) : gcm A := x <| p |> y.

Lemma altA A : ssrfun.associative (@alt A).
Proof. by move=> x y z; rewrite /alt lubA. Qed.

Lemma image_fsdistmap A B (x : gcm A) (k : choice_of_Type A -> gcm B) :
  fsdistmap k @` x = (gcm # k) x.
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

Lemma FunaltDr (A B : Type) (x y : gcm A) (k : A -> gcm B) :
  (gcm # k) (x [+] y) = (gcm # k) x [+] (gcm # k) y.
Proof.
rewrite /hierarchy.actm /= /Monad_of_category_monad.actm /=.
by rewrite scsl_hom_is_lubmorph.
Qed.

Lemma FunpchoiceDr (A B : Type) (x y : gcm A) (k : A -> gcm B) p :
  (gcm # k) (x <|p|> y) = (gcm # k) x <|p|> (gcm # k) y.
Proof.
rewrite /hierarchy.actm /= /Monad_of_category_monad.actm /=.
by rewrite scsl_hom_is_affine.
Qed.
End funalt_funchoice.

Section bindaltDl.
Import category.
Import comps_notation.
Local Notation F1 := free_semiCompSemiLattConvType.
Local Notation F0 := free_convType.
Local Notation FC := free_choiceType.
Local Notation UC := forget_choiceType.
Local Notation U0 := forget_convType.
Local Notation U1 := forget_semiCompSemiLattConvType.

Lemma affine_F1e0U1PD_alt T (u v : gcm (gcm T)) :
  (F1 # eps0 (U1 (P_delta_left T)))%category (u [+] v) =
  (F1 # eps0 (U1 (P_delta_left T)))%category u [+]
  (F1 # eps0 (U1 (P_delta_left T)))%category v.
Proof. exact: scsl_hom_is_lubmorph. Qed.

Lemma affine_e1PD_alt T (x y : el (F1 (FId (U1 (P_delta_left T))))) :
  (eps1 (P_delta_left T)) (x [+] y) =
  (eps1 (P_delta_left T)) x [+] (eps1 (P_delta_left T)) y.
Proof. exact: scsl_hom_is_lubmorph. Qed.

(*
Local Notation F1o := necset_semiCompSemiLattConvType.
*)
Local Notation F0o := FSDist_t__canonical__isConvexSpace__ConvexSpace. (* FIXME *)
Local Notation FCo := choice_of_Type.
Local Notation F1m := free_semiCompSemiLattConvType_mor.
Local Notation F0m := free_convType_mor.

Lemma bindaltDl : BindLaws.left_distributive (@hierarchy.bind gcm) alt.
Proof.
move=> A B x y k.
rewrite hierarchy.bindE /= /join_ -category.bindE.
by rewrite scsl_hom_is_lubmorph.
Qed.
End bindaltDl.

HB.instance Definition _ :=
  @isMonadAlt.Build (Monad_of_category_monad.acto Mgcm) alt altA bindaltDl.

Lemma altxx A : idempotent (@alt A).
Proof. by move=> x; rewrite /= /alt lubxx. Qed.
Lemma altC A : commutative (@alt A).
Proof. by move=> a b; rewrite /= /alt /= lubC. Qed.

HB.instance Definition _ :=
  @isMonadAltCI.Build (Monad_of_category_monad.acto Mgcm) altxx altC.

Definition gcmACI := [the altCIMonad of gcm].

Lemma choice0 A (x y : gcm A) : x <| 0%:pr |> y = y.
Proof. by rewrite conv0. Qed.
Lemma choice1 A (x y : gcm A) : x <| 1%:pr |> y = x.
Proof. by rewrite conv1. Qed.
Lemma choiceC A p (x y : gcm A) : x <|p|> y = y <|(Prob.p p).~%:pr|> x.
Proof. by rewrite convC. Qed.
Lemma choicemm A p : idempotent (@choice p A).
Proof. by move=> m; rewrite /choice convmm. Qed.
Lemma choiceA A (p q r s : {prob [realType of R]}) (x y z : gcm A) :
  p = (r * s) :> R /\ (Prob.p s).~ = ((Prob.p p).~ * (Prob.p q).~)%R ->
  x <| p |> (y <| q |> z) = (x <| r |> y) <| s |> z.
Proof. by case => *; apply: convA0. Qed.

Section bindchoiceDl.
Import category.
Import comps_notation.
Local Notation F1 := free_semiCompSemiLattConvType.
Local Notation F0 := free_convType.
Local Notation FC := free_choiceType.
Local Notation UC := forget_choiceType.
Local Notation U0 := forget_convType.
Local Notation U1 := forget_semiCompSemiLattConvType.

Lemma affine_F1e0U1PD_conv T (u v : gcm (gcm T)) p :
  ((F1 # eps0 (U1 (P_delta_left T))) (u <|p|> v) =
   (F1 # eps0 (U1 (P_delta_left T))) u <|p|>
   (F1 # eps0 (U1 (P_delta_left T))) v)%category.
Proof. exact: scsl_hom_is_affine. Qed.

Lemma affine_e1PD_conv T (x y : el (F1 (FId (U1 (P_delta_left T))))) p :
  (eps1 (P_delta_left T)) (x <|p|> y) =
  (eps1 (P_delta_left T)) x <|p|> (eps1 (P_delta_left T)) y.
Proof. exact: scsl_hom_is_affine. Qed.

(*Local Notation F1o := necset_semiCompSemiLattConvType.*)
Local Notation F0o := FSDist_t__canonical__isConvexSpace__ConvexSpace. (* FIXME *)
Local Notation FCo := choice_of_Type.
Local Notation F1m := free_semiCompSemiLattConvType_mor.
Local Notation F0m := free_convType_mor.

Lemma bindchoiceDl p :
  BindLaws.left_distributive (@hierarchy.bind gcm) (@choice p).
Proof.
move=> A B x y k.
rewrite hierarchy.bindE /= /join_ -category.bindE.
exact: scsl_hom_is_affine.
Qed.

End bindchoiceDl.

HB.instance Definition _ :=
  isMonadProb.Build real_realType (Monad_of_category_monad.acto Mgcm)
    choice0 choice1 choiceC choicemm choiceA bindchoiceDl.

Lemma choicealtDr A (p : {prob real_realType}) :
  right_distributive (fun x y : Mgcm A => x <| p |> y) (@alt A).
Proof. by move=> x y z; rewrite /choice lubDr. Qed.

HB.instance Definition _ :=
  @isMonadAltProb.Build real_realType (Monad_of_category_monad.acto Mgcm) choicealtDr.

Definition gcmAP := [the altProbMonad real_realType of gcm].

End P_delta_altProbMonad.

Section probabilisctic_choice_not_trivial.
Local Open Scope proba_monad_scope.

(* An example that probabilistic choice in this model is not trivial:
   we can distinguish different probabilities. *)
Example gcmAP_choice_nontrivial (p q : {prob real_realType}) :
  p <> q ->
  (* Ret = hierarchy.ret *)
  Ret true <|p|> Ret false <>
  Ret true <|q|> Ret false :> (Monad_of_category_monad.acto Mgcm) bool.
Proof.
apply contra_not.
rewrite !gcm_retE /Choice /= => /(congr1 (@NECSet.car _)).
rewrite !necset_convType.convE !conv_cset1 /=.
move/(@set1_inj _ (conv _ _ _))/(congr1 (@FSDist.f _))/fsfunP/(_ true).
by rewrite !fsdist_convE !fsdist1xx !mulR1 fsdist10 ?mulR0 ?addR0//;
  [exact: val_inj|exact/eqP].
Qed.

End probabilisctic_choice_not_trivial.
