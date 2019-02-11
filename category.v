From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype tuple finfun bigop prime binomial.
From mathcomp Require Import ssralg finset fingroup perm finalg matrix.
From mathcomp Require Import boolp classical_sets.
Require Import ProofIrrelevance FunctionalExtensionality.
Require Reals Lra.
From infotheo Require ssrR Reals_ext Ranalysis_ext ssr_ext ssralg_ext logb Rbigop.
From infotheo Require proba.
From infotheo Require convex.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma compA {A B C D} (f : C -> D) (g : B -> C) (h : A -> B) : f \o (g \o h) = (f \o g) \o h.
Proof. by []. Qed.

Lemma compfid A B (f : A -> B) : f \o id = f. Proof. by []. Qed.

Lemma compidf A B (f : A -> B) : id \o f = f. Proof. by []. Qed.

Lemma compE A B C (g : B -> C) (f : A -> B) a : (g \o f) a = g (f a).
Proof. by []. Qed.


Module Category.
Record class_of (T : Type) : Type := Class {
  ob : T -> Type ; (* T and ob forms a ``universe a la Tarski'' *)
  hom : forall A B, (ob A -> ob B) -> Prop ; (* subset of morphisms *)
(*  _  : injective ob ; (* ob is injective *)*)
  _ : forall (A : T), hom (A:=A) (B:=A) id ; (* id is in hom *)
  _  : forall (A B C : T) (f : ob A -> ob B) (g : ob B -> ob C),
      hom f -> hom g -> hom (g \o f) ; (* hom is closed under composition *)
}.
Structure t : Type := Pack { T : Type ; class : class_of T }.
Module Exports.
End Exports.
End Category.

Section convType_category.
Import convex.
Lemma affine_function_comp_proof' :
  forall (A B C : convType) (f : A -> B) (g : B -> C),
    affine_function f -> affine_function g -> affine_function (g \o f).
Proof. by move=>A B C f g Hf Hg a b t; rewrite /affine_function_at compE Hf Hg. Qed.

Definition convType_category_class : Category.class_of convType :=
Category.Class affine_function_id_proof affine_function_comp_proof'.
End convType_category.

Section Type_category.
Definition Type_category_class : Category.class_of Type :=
@Category.Class Type id (fun _ _ _ => True) (fun _ => I) (fun _ _ _ _ _ _ _ => I).
End Type_category.
