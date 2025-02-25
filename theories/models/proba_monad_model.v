(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2020 monae authors, license: LGPL-2.1-or-later               *)
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp Require boolp.
From mathcomp Require Import mathcomp_extra reals.
From infotheo Require Import realType_ext ssr_ext fsdist.
From infotheo Require Import convex.
From HB Require Import structures.
Require Import preamble hierarchy monad_lib proba_lib.

(******************************************************************************)
(*                     Model for the probability monad                        *)
(******************************************************************************)

Local Open Scope monae_scope.
Local Open Scope proba_scope.

Require monad_model.
Notation choice_of_Type := monad_model.choice_of_Type.

Module MonadProbModel.
Section monadprobmodel.
Variable R : realType.

Definition acto : UU0 -> UU0 := fun A => R.-dist (choice_of_Type A).

Definition ret : idfun ~~> acto :=
  fun A a => fsdist1 (a : choice_of_Type A).

Definition bind : forall A B, acto A -> (A -> acto B) -> acto B :=
  fun A B m f => (m >>= f)%fsdist.

Let left_neutral : BindLaws.left_neutral bind ret.
Proof. by move=> ? ? ? ?; exact: fsdist1bind. Qed.

Lemma right_neutral : BindLaws.right_neutral bind ret.
Proof. by move=> ? ?; exact: fsdistbind1. Qed.

Lemma associative : BindLaws.associative bind.
Proof. by move=> A B C m f g; exact: fsdistbindA. Qed.

HB.instance Definition _ := isMonad_ret_bind.Build
  acto left_neutral right_neutral associative.

Lemma BindE (A B : choiceType) m (f : A -> [the monad of acto] B) :
  (m >>= f) = (m >>= f)%fsdist.
Proof.
by rewrite /hierarchy.bind /= /bind.
Qed.

Local Open Scope reals_ext_scope.

Let choice := (fun p A => @fsdist_conv R (choice_of_Type A) p).

Let choice1 (T : UU0) : forall (a b : acto T), choice 1%R%:pr _ a b = a.
Proof. by move=> ? ?; exact: conv1. Qed.

Let choiceC (T : UU0) : forall p (a b : acto T), choice p _ a b = choice ((Prob.p p).~ %:pr) _ b a.
Proof. by move=> ? ?; exact: convC. Qed.

Let choicemm : forall (T : Type) p, idempotent (@choice p T).
Proof. by move=> ? ? ?; exact: convmm. Qed.

Let choiceA : forall (T : Type) (p q r s : {prob R}) (a b c : acto T),
  choice p _ a (choice q _ b c) = choice [s_of p, q] _ (choice [r_of p, q] _ a b) c.
Proof.
move=> ? p q r s a b c.
rewrite /choice -/(conv p a (conv q b c)) -/(conv s (conv r a b) c).
apply: convA0 => /=; first by rewrite -p_is_rs.
by rewrite s_of_pqE onemK.
Qed.

HB.instance Definition _ := isMonadConvex.Build R
  acto choice1 choiceC choicemm choiceA.

Let prob_bindDl p :
  BindLaws.left_distributive (@hierarchy.bind [the monad of acto]) (choice p).
Proof.
move=> A B m1 m2 k.
rewrite !(@BindE (choice_of_Type A) (choice_of_Type B)).
by rewrite fsdist_conv_bind_left_distr.
Qed.

HB.instance Definition mixin := isMonadProb.Build R
   acto prob_bindDl.
(* NB: we use Pack here for an application in gcm_model.v *)
Definition t := MonadProb.Pack (MonadProb.Class mixin).

End monadprobmodel.
End MonadProbModel.
HB.export MonadProbModel.
