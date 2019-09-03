Require Import ssreflect ssrmatching ssrfun ssrbool.
From mathcomp Require Import eqtype ssrnat seq choice fintype tuple.
From mathcomp Require boolp.
From infotheo Require Import Reals_ext ssr_ext fsdist.
Require Import monad proba_monad model.

(*
  This file provides a model for the probability monad.
      depends on the formalization of distributions from the infotheo library
      (https://github.com/affeldt-aist/infotheo).
*)

Local Open Scope monae_scope.

Module MonadProbModel.
Local Obligation Tactic := idtac.

Definition _ret : forall A : Type, A -> {dist (choice_of_Type A)} :=
  fun A a => FSDist1.d (a : choice_of_Type A).

Definition _bind : forall A B : Type, {dist (choice_of_Type A)} -> (A -> {dist (choice_of_Type B)}) -> {dist (choice_of_Type B)} :=
  fun A B m f => FSDistBind.d m f.

Program Definition monad : Monad.t :=
  @Monad_of_ret_bind _ _ret _bind _ _ _.
Next Obligation. move=> ? ? ? ?; exact: FSDistBind1f. Qed.
Next Obligation. move=> ? ?; exact: FSDistBindp1. Qed.
Next Obligation. move=> A B C m f g; exact: FSDistBindA. Qed.

Lemma BindE (A B : choiceType) m (f : A -> monad B) :
  (m >>= f) = FSDistBind.d m f.
Proof.
rewrite /Bind /Join /= /Monad_of_ret_bind.join /Fun /=.
rewrite /Monad_of_ret_bind.Map /_bind FSDistBindA; congr FSDistBind.d.
by rewrite boolp.funeqE => a; rewrite /= FSDistBind1f.
Qed.

Program Definition prob_mixin : MonadProb.mixin_of monad :=
  @MonadProb.Mixin monad (fun p (A : Type) (m1 m2 : {dist (choice_of_Type A)}) =>
    (@Conv2FSDist.d (choice_of_Type A) m1 m2 p)) _ _ _ _ _ _.
Next Obligation. move=> ? ? ?; exact: Conv2FSDist.conv0. Qed.
Next Obligation. move=> ? ? ?; exact: Conv2FSDist.conv1. Qed.
Next Obligation. move=> ? ? ?; exact: Conv2FSDist.convC. Qed.
Next Obligation. move=> ? ? ?; exact: Conv2FSDist.convmm. Qed.
Next Obligation. move=> ? ? ? ? ? ? ? ? [? ?] /=; exact: Conv2FSDist.convA. Qed.
Next Obligation.
move=> p A B m1 m2 k.
rewrite !(@BindE (choice_of_Type A) (choice_of_Type B)).
by rewrite Conv2FSDist.bind_left_distr.
Qed.

Definition prob_class : MonadProb.class_of (fun A : Type => {dist (choice_of_Type A)}) :=
  @MonadProb.Class _ _ prob_mixin.

Definition prob : MonadProb.t := MonadProb.Pack prob_class.

End MonadProbModel.
