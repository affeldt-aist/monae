(* monae: Monadic equational reasoning in Rocq                                *)
(* Copyright (C) 2025 monae authors, license: LGPL-2.1-or-later               *)
From mathcomp Require Import all_ssreflect ssralg ssrnum interval_inference.
From mathcomp Require boolp.
From mathcomp Require Import unstable mathcomp_extra reals.
From infotheo Require Import realType_ext ssr_ext fsdist.
From infotheo Require Import convex.
From HB Require Import structures.
Require Import preamble hierarchy monad_lib proba_lib.

(**md**************************************************************************)
(* # Model for the probability monad                                          *)
(******************************************************************************)

Local Open Scope monae_scope.
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.

Require monad_model.
Notation choice_of_Type := monad_model.choice_of_Type.

(* This factory is placed here (instead of hierarchy.v)
   because we need to use choice_of_Type *)
HB.factory Record isMonadConvex {R : realType} (M : UU0 -> UU0) of Monad M := {
  choice : forall (p : {prob R}) (T : UU0), M T -> M T -> M T ;
  (* identity axioms *)
  choice1 : forall (T : UU0) (a b : M T), choice 1%:i01 _ a b = a ;
  (* skewed commutativity *)
  choiceC : forall (T : UU0) p (a b : M T),
    choice p _ a b = choice (p%:num.~%:i01) _ b a ;
  choicemm : forall (T : UU0) p, idempotent_op (@choice p T) ;
  (* quasi associativity *)
  choiceA : forall (T : UU0) (p q : {prob R}) (a b c : M T),
    choice p _ a (choice q _ b c) = choice [s_of p, q] _ (choice [r_of p, q] _ a b) c }.

HB.builders Context R M of isMonadConvex R M.

Section class.
Variable T : UU0.

(* ConvexSpace is a subclass of Choice *)
Let MT := choice_of_Type (M T).

Let conv p (a b : MT) := choice p T a b.
Let conv1 (a b : MT) : conv 1%:i01 a b = a := choice1 T a b.
Let convmm p : idempotent_op (conv p) := choicemm T p.
Let convC p (a b : MT) : conv p a b = conv (p%:num.~)%:i01 b a := choiceC T p a b.
Let convA p q (a b c : MT) :
  conv p a (conv q b c) = conv [s_of p, q] (conv [r_of p, q] a b) c
    := choiceA T p q a b c.
Let mixin := isConvexSpace.Build R MT conv1 convmm convC convA.

(* We want a class whose type is ConvexSpace.axioms_,
   but, the factory isConvexSpace does not provide a mixin
   that can be directly fed to the class constructor ConvexSpace.Class
   So we first pack, then extract the class. *)
Let pack := HB.pack_for (convType R) MT mixin.
Definition class : ConvexSpace.axioms_ R (M T) := ConvexSpace.class pack.

End class.

HB.instance Definition _ := isMonadConvex0.Build R M class.

HB.end.

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

Let choice1 (T : UU0) (a b : acto T) : choice 1%:i01 _ a b = a.
Proof. exact: conv1. Qed.

Let choiceC (T : UU0) p (a b : acto T) :
  choice p _ a b = choice (p%:num.~%:i01) _ b a.
Proof. exact: convC. Qed.

Let choicemm (T : Type) p : idempotent_op (@choice p T).
Proof. by move=> ?; exact: convmm. Qed.

Let choiceA (T : Type) (p q : {prob R}) (a b c : acto T) :
  choice p _ a (choice q _ b c) = choice [s_of p, q] _ (choice [r_of p, q] _ a b) c.
Proof.
rewrite /choice -/(conv p a (conv q b c)).
apply: convA0 => /=; first by rewrite -p_is_rs.
by rewrite s_of_pqE onemK.
Qed.

HB.instance Definition _ := isMonadConvex.Build R
  acto choice choice1 choiceC choicemm choiceA.

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

HB.instance Definition _ := isMonadConvexDr.Build R acto prob_bindDr.

(* probDrMonad = probMonad + convexDrMonad *)
Succeed Definition test := t : probDrMonad R.

End monadprobmodel.
End MonadProbModel.
HB.export MonadProbModel.
