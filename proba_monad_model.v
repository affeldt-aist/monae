From mathcomp Require Import all_ssreflect.
From mathcomp Require boolp.
From infotheo Require Import Reals_ext ssr_ext fsdist.
From infotheo Require convex_choice.
Require Import monae_lib monad proba_monad.

(*
  This file provides a model for the probability monad.
      depends on the formalization of distributions from the infotheo library
      (https://github.com/affeldt-aist/infotheo).
*)

Local Open Scope monae_scope.

Module MonadProbModel.
Local Obligation Tactic := idtac.

Definition ret' : forall A, A -> {dist (convex_choice.choice_of_Type A)} :=
  fun A a => FSDist1.d (a : convex_choice.choice_of_Type A).

Definition bind : forall A B,
  {dist (convex_choice.choice_of_Type A)} ->
  (A -> {dist (convex_choice.choice_of_Type B)}) ->
  {dist (convex_choice.choice_of_Type B)} :=
  fun A B m f => FSDistBind.d m f.

Definition functor : functor.
apply: (@Functor.Pack (fun A => {dist (convex_choice.choice_of_Type A)}) _).
apply (@Functor.Class _ (fun A B => @FSDistfmap (convex_choice.choice_of_Type A) (convex_choice.choice_of_Type B))).
move=> A.
exact: (FSDistfmap_id (convex_choice.choice_of_Type A)).
move=> A B C g h.
exact: (@FSDistfmap_comp (convex_choice.choice_of_Type A) (convex_choice.choice_of_Type B) (convex_choice.choice_of_Type C)).
Defined.

Lemma naturality_ret' : naturality FId functor ret'.
Proof.
move=> A B h.
by rewrite boolp.funeqE => a /=; rewrite /Fun /= /ret' FSDistfmap1.
Qed.

Definition ret : FId ~> functor := Natural.Pack naturality_ret'.

Program Definition monad : Monad.t :=
  @Monad_of_ret_bind _ ret bind _ _ _.
Next Obligation. move=> ? ? ? ?; exact: FSDistBind1f. Qed.
Next Obligation. move=> ? ?; exact: FSDistBindp1. Qed.
Next Obligation. move=> A B C m f g; exact: FSDistBindA. Qed.

Lemma BindE (A B : choiceType) m (f : A -> monad B) :
  (m >>= f) = FSDistBind.d m f.
Proof.
rewrite /Bind /Join /= /Monad_of_ret_bind.join /Fun /=.
rewrite /Monad_of_ret_bind.Map /bind FSDistBindA; congr FSDistBind.d.
by rewrite boolp.funeqE => a; rewrite /= FSDistBind1f.
Qed.

Program Definition prob_mixin : MonadProb.mixin_of monad :=
  @MonadProb.Mixin monad (fun p A => @ConvFSDist.d (convex_choice.choice_of_Type A) p) _ _ _ _ _ _.
Next Obligation. move=> ? ? ?; exact: ConvFSDist.conv0. Qed.
Next Obligation. move=> ? ? ?; exact: ConvFSDist.conv1. Qed.
Next Obligation. move=> ? ? ?; exact: ConvFSDist.convC. Qed.
Next Obligation. move=> ? ? ?; exact: ConvFSDist.convmm. Qed.
Next Obligation. move=> ? ? ? ? ? ? ? ? ? /=; exact: ConvFSDist.convA. Qed.
Next Obligation.
move=> p A B m1 m2 k.
rewrite !(@BindE (convex_choice.choice_of_Type A) (convex_choice.choice_of_Type B)).
by rewrite ConvFSDist.bind_left_distr.
Qed.

Definition prob_class : MonadProb.class_of (fun A : Type => {dist (convex_choice.choice_of_Type A)}) :=
  @MonadProb.Class _ _ prob_mixin.

Definition prob : MonadProb.t := MonadProb.Pack prob_class.

End MonadProbModel.
