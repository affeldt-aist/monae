From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype tuple finfun bigop prime binomial.
From mathcomp Require Import ssralg finset fingroup perm finalg matrix.
From mathcomp Require Import boolp classical_sets.
Require Import Reals Lra.
From infotheo Require Import ssrR Reals_ext Ranalysis_ext ssr_ext logb Rbigop.
From infotheo Require Import proba.
From infotheo Require Import convex.
Require Import category.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section convType_category.
Lemma affine_function_comp_proof' :
  forall (A B C : convType) (f : A -> B) (g : B -> C),
    affine_function f -> affine_function g -> affine_function (g \o f).
Proof. by move=>A B C f g Hf Hg a b t; rewrite /affine_function_at compE Hf Hg. Qed.
Definition convType_category_class : Category.class_of convType :=
  Category.Class affine_function_id_proof affine_function_comp_proof'.
Canonical convType_category := Category.Pack convType_category_class.
End convType_category.

Module Category_Examples.
Section Example_cat.
Variables (C : category) (A B : C) (f g : {hom A,B}).
End Example_cat.
Section Example_convType.
Import convex.
Local Open Scope convex_scope.
Variables (A B : convType) (f : {hom A,B}) (g : {affine A -> B}).
Variable x : A.
Check (f x : B).
Check (f x : El B).
Check (g x : B).
Check (g x : El B).
Check (f : A -> B).
Check (g : A -> B).
Fail Check (f : {affine A -> B}).
Fail Check (g : {hom A,B}).
Goal affine_function f.
Proof. by case: f. Qed.
End Example_convType.
Section Example_Type.
Variables (A B : Type) (f : {hom A,B}) (g : A -> B).
Variable x : A.
Check (f x : B).
Check (f x : El B).
Check (g x : B).
Check (g x : El B).
Check (f : A -> B).
Fail Check (g : {hom A,B}).
End Example_Type.
End Category_Examples.
