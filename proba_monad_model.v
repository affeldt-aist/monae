Require Import ssreflect ssrmatching ssrfun ssrbool.
From mathcomp Require Import eqtype ssrnat seq choice fintype tuple.
From mathcomp Require Import boolp classical_sets.
From infotheo Require Import Reals_ext ssr_ext dist.
Require Import monad proba_monad model.

(*
  This file provides a model for the probability monad.
      depends on the formalization of distributions from the infotheo library
      (https://github.com/affeldt-aist/infotheo).
*)

Module MonadProbModel.
Local Obligation Tactic := idtac.

Let _bind : forall A B : Type, Dist (choice_of_Type A) -> (A -> Dist (choice_of_Type B)) -> Dist (choice_of_Type B) :=
  fun A B m f => DistBind.d m f.

Let _ret : forall A : Type, A -> Dist (choice_of_Type A) := fun A a => Dist1.d (a : choice_of_Type A).

Program Definition monad : Monad.t :=
  @Monad_of_bind_ret _ _bind _ret _ _ _.
Next Obligation. move=> ? ? ? ?; exact: DistBind1f. Qed.
Next Obligation. move=> ? ?; exact: DistBindp1. Qed.
Next Obligation. move=> A B C m f g; exact: DistBindA. Qed.

Lemma BindE (A B : choiceType) m (f : A -> monad B) :
  (m >>= f) = DistBind.d m f.
Proof.
rewrite /Bind /Join /= /Monad_of_bind_ret.join /Fun /=.
rewrite /Monad_of_bind_ret.fmap /_bind DistBindA; congr DistBind.d.
by rewrite funeqE => a; rewrite /= DistBind1f.
Qed.

Program Definition prob_mixin : MonadProb.mixin_of monad :=
  @MonadProb.Mixin monad (fun p (A : Type) (m1 m2 : Dist (choice_of_Type A)) =>
    (@Conv2Dist.d (choice_of_Type A) m1 m2 p)) _ _ _ _ _ _.
Next Obligation. move=> ? ? ?; exact: Conv2Dist.conv0. Qed.
Next Obligation. move=> ? ? ?; exact: Conv2Dist.conv1. Qed.
Next Obligation. move=> ? ? ?; exact: Conv2Dist.convC. Qed.
Next Obligation. move=> ? ? ?; exact: Conv2Dist.convmm. Qed.
Next Obligation. move=> ? ? ? ? ? ? ? ? [? ?] /=; exact: Conv2Dist.convA. Qed.
Next Obligation.
move=> p A B m1 m2 k.
rewrite !(@BindE (choice_of_Type A) (choice_of_Type B)).
by rewrite Conv2Dist.bind_left_distr.
Qed.

Definition prob_class : MonadProb.class_of (fun A : Type => Dist (choice_of_Type A)) :=
  @MonadProb.Class _ _ prob_mixin.

Definition prob : MonadProb.t := MonadProb.Pack prob_class.

End MonadProbModel.
