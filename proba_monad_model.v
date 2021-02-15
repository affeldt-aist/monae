(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2020 monae authors, license: LGPL-2.1-or-later               *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require boolp.
From infotheo Require Import Reals_ext ssr_ext fsdist.
From infotheo Require Import convex.
Require Import monae_lib hierarchy monad_lib proba_lib.

(******************************************************************************)
(*                     Model for the probability monad                        *)
(******************************************************************************)

Local Open Scope monae_scope.
Local Open Scope proba_scope.

Notation choice_of_Type := convex.choice_of_Type.

Module MonadProbModel.
Local Obligation Tactic := idtac.

Set Printing All.

Definition ret' : forall A, A -> {dist (choice_of_Type A)} :=
  fun A a => FSDist1.d (a : choice_of_Type A).

Definition bind : forall A B, {dist (choice_of_Type A)} ->
  (A -> {dist (choice_of_Type B)}) -> {dist (choice_of_Type B)} :=
  fun A B m f => FSDistBind.d m f.

Definition functor : functor.
apply: (@Functor.Pack (fun A => {dist (choice_of_Type A)}) _).
apply (@Functor.Mixin _ (fun A B => @FSDistfmap (choice_of_Type A) (choice_of_Type B))).
  by move=> A; exact: (FSDistfmap_id _).
by move=> A B C g h; exact: FSDistfmap_comp.
Defined.

Lemma naturality_ret' : naturality FId functor ret'.
Proof.
move=> A B h.
by rewrite boolp.funeqE => a /=; rewrite /Actm /= /ret' FSDistfmap1.
Qed.

Definition ret : FId ~> functor := Natural.Pack (Natural.Mixin naturality_ret').

Program Definition monad_ : monad :=
  @Monad_of_ret_bind _ ret bind _ _ _.
Next Obligation. move=> ? ? ? ?; exact: FSDistBind1f. Qed.
Next Obligation. move=> ? ?; exact: FSDistBindp1. Qed.
Next Obligation. move=> A B C m f g; exact: FSDistBindA. Qed.

Lemma BindE (A B : choiceType) m (f : A -> monad_ B) :
  (m >>= f) = FSDistBind.d m f.
Proof.
rewrite /Bind /Join /= /Monad_of_ret_bind.join /Actm /=.
rewrite /Monad_of_ret_bind.Map /bind FSDistBindA; congr FSDistBind.d.
by rewrite boolp.funeqE => a; rewrite /= FSDistBind1f.
Qed.

Program Definition prob_mixin : MonadProb.mixin_of monad_ :=
  @MonadProb.Mixin monad_ (fun p A => @ConvFSDist.d (choice_of_Type A) p) _ _ _ _ _ _.
Next Obligation. move=> ? ? ?; exact: ConvFSDist.conv0. Qed.
Next Obligation. move=> ? ? ?; exact: ConvFSDist.conv1. Qed.
Next Obligation. move=> ? ? ?; exact: ConvFSDist.convC. Qed.
Next Obligation. move=> ? ? ?; exact: ConvFSDist.convmm. Qed.
Next Obligation. move=> ? ? ? ? ? ? ? ? ? /=; exact: ConvFSDist.convA. Qed.
Next Obligation.
move=> p A B m1 m2 k.
rewrite !(@BindE (choice_of_Type A) (choice_of_Type B)).
by rewrite ConvFSDist.bind_left_distr.
Qed.

Definition prob_class : MonadProb.class_of (fun A : Type => {dist (choice_of_Type A)}) :=
  @MonadProb.Class _ _ prob_mixin.

Definition prob : probMonad := MonadProb.Pack prob_class.

End MonadProbModel.

Module MonadProbDrModel.

Local Obligation Tactic := idtac.

Require Import Reals.
From mathcomp Require Import finmap.
From infotheo Require Import Rbigop.
Local Open Scope R_scope.

Local Open Scope proba_scope.

Definition probDr_mixin : MonadProbDr.mixin_of MonadProbModel.prob.
refine (MonadProbDr.Mixin _) => p A B m k1 k2.
rewrite 3!(@MonadProbModel.BindE (choice_of_Type A) (choice_of_Type B)).
apply/FSDist_ext => b /=.
rewrite FSDistBind.dE /=.
case: ifPn.
  move=> /bigfcupP[/= dB].
  rewrite andbT => /imfsetP[a /= /imfsetP[/= a' a'm aa']]; move: a'm; rewrite -{}aa' {a'} => ma ->{dB} bk1k2.
  rewrite /Choice /= ConvFSDist.dE /= !FSDistBind.dE /=.
  case: ifPn => bk1.
    case: ifPn => bk2.
      admit.
    admit.
  admit.
move=> bk1k2.
Abort.

End MonadProbDrModel.
