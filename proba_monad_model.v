(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2020 monae authors, license: LGPL-2.1-or-later               *)
Require Import Reals.
From mathcomp Require Import all_ssreflect.
From mathcomp Require boolp.
From infotheo Require Import Reals_ext ssr_ext fsdist.
From infotheo Require Import convex.
From HB Require Import structures.
Require Import monae_lib hierarchy proba_hierarchy monad_lib proba_lib.

(******************************************************************************)
(*                     Model for the probability monad                        *)
(*                                                                            *)
(* Module MonadProbModel == probMonad using fsdist from infotheo              *)
(******************************************************************************)

Local Open Scope monae_scope.
Local Open Scope proba_scope.

Notation choice_of_Type := convex.choice_of_Type.

Module MonadProbModel.
Section monadprobmodel.

Definition acto : UU0 -> UU0 := fun A => {dist (choice_of_Type A)}.

Lemma map_id : @FunctorLaws.id (FSDist.t \o choice_of_Type)
  (fun A B => @FSDistfmap (choice_of_Type A) (choice_of_Type B)).
Proof. by move=> A; exact: (FSDistfmap_id _). Qed.

Lemma map_comp : @FunctorLaws.comp (FSDist.t \o choice_of_Type)
  (fun A B => @FSDistfmap (choice_of_Type A) (choice_of_Type B)).
Proof. by move=> A B C g h; exact: FSDistfmap_comp. Qed.

HB.instance Definition _ := isFunctor.Build acto map_id map_comp.

Definition ret' : forall A, A -> {dist (choice_of_Type A)} :=
  fun A a => FSDist1.d (a : choice_of_Type A).

Lemma naturality_ret' : naturality FId [the functor of acto] ret'.
Proof.
move=> A B h.
by rewrite boolp.funeqE => a /=; rewrite /actm /= /ret' FSDistfmap1.
Qed.

Definition ret : FId ~> [the functor of acto] :=
  Natural.Pack (Natural.Mixin naturality_ret').

Definition bind : forall A B, acto A -> (A -> acto B) -> acto B :=
  fun A B m f => FSDistBind.d m f.

Lemma left_neutral : BindLaws.left_neutral bind ret.
Proof. by move=> ? ? ? ?; exact: FSDistBind1f. Qed.
Lemma right_neutral : BindLaws.right_neutral bind ret.
Proof. by move=> ? ?; exact: FSDistBindp1. Qed.
Lemma associative : BindLaws.associative bind.
Proof. by move=> A B C m f g; exact: FSDistBindA. Qed.

Lemma fmapE (A B : UU0) (f : A -> B) (m : acto A) :
  ([the functor of acto] # f) m = bind _ _ m (@ret _ \o f).
Proof. by []. Qed.

HB.instance Definition _ := @Monad_of_ret_bind.Build
  acto ret bind fmapE left_neutral right_neutral associative.

Lemma BindE (A B : choiceType) m (f : A -> [the monad of acto] B) :
  (m >>= f) = FSDistBind.d m f.
Proof.
by rewrite /hierarchy.bind /= /bind.
Qed.

Local Open Scope reals_ext_scope.

Let choice := (fun p A => @ConvFSDist.d (choice_of_Type A) p).
Let choice0 : forall (T : UU0) (a b : acto T), choice 0%:pr _ a b = b.
Proof. by move=> ? ? ?; exact: ConvFSDist.conv0. Qed.
Let choice1 : forall (T : UU0) (a b : acto T), choice 1%:pr _ a b = a.
Proof. by move=> ? ? ?; exact: ConvFSDist.conv1. Qed.
Let choiceC : forall (T : UU0) p (a b : acto T),
  choice p _ a b = choice (p.~ %:pr) _ b a.
Proof. by move=> ? ? ?; exact: ConvFSDist.convC. Qed.
Let choicemm : forall (T : Type) p, idempotent (@choice p T).
Proof. by move=> ? ? ?; exact: ConvFSDist.convmm. Qed.
Let choiceA : forall (T : Type) (p q r s : prob) (a b c : acto T),
    (p = r * s :> R /\ s.~ = p.~ * q.~)%R ->
    let bc := (choice q _ b c) in
    let ab := (choice r _ a b) in
    choice p _ a bc = choice s _ ab c.
Proof. by move=> ? ? ? ? ? ? ? ? ? /=; exact: ConvFSDist.convA. Qed.
Let prob_bindDl p :
  BindLaws.left_distributive (@hierarchy.bind [the monad of acto]) (choice p).
Proof.
move=> A B m1 m2 k.
rewrite !(@BindE (choice_of_Type A) (choice_of_Type B)).
by rewrite ConvFSDist.bind_left_distr.
Qed.

HB.instance Definition mixin := isMonadProb.Build acto choice0 choice1 choiceC
                                choicemm choiceA prob_bindDl.
Definition t := MonadProb.Pack (MonadProb.Class mixin).

End monadprobmodel.
End MonadProbModel.
