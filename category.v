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
  obj : T -> Type ; (* T and ob forms a ``universe a la Tarski'' *)
  hom : forall A B, (obj A -> obj B) -> Prop ; (* subset of morphisms *)
(*  _  : injective obj ; (* obj is injective *)*)
  _ : forall (A : T), hom (A:=A) (B:=A) id ; (* id is in hom *)
  _  : forall (A B C : T) (f : obj A -> obj B) (g : obj B -> obj C),
      hom f -> hom g -> hom (g \o f) ; (* hom is closed under composition *)
}.
Structure t : Type := Pack { car : Type ; class : class_of car }.
Module Exports.
Notation category := t.
Coercion car : category >-> Sortclass.
Definition El (C : t) : C -> Type :=
  let: Pack _ (Class x _ _ _) := C in x.
Definition Hom (C : t) : forall (A B : C), (El A -> El B) -> Prop :=
  let: Pack _ (Class _ x _ _) := C in x.
End Exports.
End Category.
Export Category.Exports.

Module HomPhant.
Section ClassDef.
Variables (C : category) (U V : C).
Local Notation U' := (El U).
Local Notation V' := (El V).
Definition axiom (f : U' -> V') := Hom f.
Structure map (phUV : phant (U' -> V')) := Pack {apply; _ : axiom apply}.
Local Coercion apply : map >-> Funclass.
Variables (phUV : phant (U' -> V')) (f g : U' -> V') (cF : map phUV).
Definition class := let: Pack _ c as cF' := cF return axiom cF' in c.
Definition clone fA of phant_id g (apply cF) & phant_id fA class :=
  @Pack phUV f fA.
End ClassDef.
Module Exports.
Coercion apply : map >-> Funclass.
Notation HomPhant fA := (Pack (Phant _) fA).
Notation "{ 'hom' U  , V }" := (map (Phant (El U -> El V)))
  (at level 0, format "{ 'hom' U , V }") : category_scope.
(*
Notation "{ 'hom' fUV }" := (map (Phant fUV))
  (at level 0, format "{ 'hom'  fUV }") : category_scope.
*)
End Exports.
End HomPhant.
Export HomPhant.Exports.

Open Scope category_scope.

Section convType_category.
Import convex.
Lemma affine_function_comp_proof' :
  forall (A B C : convType) (f : A -> B) (g : B -> C),
    affine_function f -> affine_function g -> affine_function (g \o f).
Proof. by move=>A B C f g Hf Hg a b t; rewrite /affine_function_at compE Hf Hg. Qed.
Definition convType_category_class : Category.class_of convType :=
  Category.Class affine_function_id_proof affine_function_comp_proof'.
Canonical convType_category := Category.Pack convType_category_class.
End convType_category.

Section Type_category.
Definition Type_category_class : Category.class_of Type :=
@Category.Class Type id (fun _ _ _ => True) (fun _ => I) (fun _ _ _ _ _ _ _ => I).
Canonical Type_category := Category.Pack Type_category_class.
End Type_category.

Section Examples.
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
End Examples.

