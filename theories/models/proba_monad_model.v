(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2025 monae authors, license: LGPL-2.1-or-later               *)
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp Require boolp.
From mathcomp Require Import unstable mathcomp_extra reals.
From mathcomp Require Import ring.
From infotheo Require Import realType_ext ssr_ext fsdist.
From infotheo Require Import convex.
From HB Require Import structures.
Require Import preamble hierarchy monad_lib proba_lib.

(**md**************************************************************************)
(* # Model for the probability monad                                          *)
(******************************************************************************)

Local Open Scope monae_scope.
Local Open Scope proba_scope.

(* NB: To appear in coq-infotheo 0.9.6 *)
Section move_to_infotheo.
Local Open Scope convex_scope.
Local Open Scope fdist_scope.

Local Notation "m >>= f" := (fsdistbind m f).

Import GRing.Theory.

Lemma fsdist_conv_bind_right_distr {R : realType} (A B : choiceType) p
    (m : R.-dist A) (a b : A -> R.-dist B):
  m >>= (a <| p |> b) = (m >>= a) <| p |> (m >>= b).
Proof.
apply/fsdist_ext => b0.
rewrite fsdist_convE 3!fsdistbindE avgRE 2!big_distrr -big_split/=.
apply: eq_bigr=> a0 _; rewrite fsdist_convE avgRE/=.
ring.
Qed.

End move_to_infotheo.

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
Proof. by []. Qed.

Local Open Scope reals_ext_scope.

Let choice := fun p A => @fsdist_conv R (choice_of_Type A) p.

Let choice1 (T : UU0) (a b : acto T) : choice 1%R%:pr _ a b = a.
Proof. exact: conv1. Qed.

Let choiceC (T : UU0) p (a b : acto T) :
  choice p _ a b = choice ((Prob.p p).~ %:pr) _ b a.
Proof. exact: convC. Qed.

Let choicemm (T : Type) p : idempotent_op (@choice p T).
Proof. by move=> ?; exact: convmm. Qed.

Let choiceA (T : Type) (p q r s : {prob R}) (a b c : acto T) :
  choice p _ a (choice q _ b c) = choice [s_of p, q] _ (choice [r_of p, q] _ a b) c.
Proof.
rewrite /choice -/(conv p a (conv q b c)) -/(conv s (conv r a b) c).
apply: convA0 => /=; first by rewrite -p_is_rs.
by rewrite s_of_pqE onemK.
Qed.

HB.instance Definition _ := isMonadConvex.Build R
  acto choice1 choiceC choicemm choiceA.

Let prob_bindDl p :
  BindLaws.left_distributive (@hierarchy.bind acto) (choice p).
Proof.
move=> A B m1 m2 k.
rewrite !(@BindE (choice_of_Type A) (choice_of_Type B)).
by rewrite fsdist_conv_bind_left_distr.
Qed.

HB.instance Definition mixin := isMonadProb.Build R acto prob_bindDl.
(* NB: we use Pack here for an application in gcm_model.v *)
Definition t := MonadProb.Pack (MonadProb.Class mixin).

Let prob_bindDr p :
  BindLaws.right_distributive (@hierarchy.bind acto) (choice p).
Proof.
move=> A B m1 m2 k.
rewrite !(@BindE (choice_of_Type A) (choice_of_Type B)).
by rewrite fsdist_conv_bind_right_distr.
Qed.

HB.instance Definition _ := isMonadProbDr.Build R acto prob_bindDr.

End monadprobmodel.
End MonadProbModel.
HB.export MonadProbModel.
