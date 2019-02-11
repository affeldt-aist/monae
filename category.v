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

(* Our `category' is always concrete; a subcategory of the category of types and functions. *)
Module Category.
Record class_of (T : Type) : Type := Class {
  obj : T -> Type ; (* T and obj is like a ``universe a la Tarski'' *)
  hom : forall A B, (obj A -> obj B) -> Prop ; (* subset of morphisms *)
(*  _ : injective obj ; (* NB: do we need this? *)*)
  _ : forall (A : T), hom (A:=A) (B:=A) id ; (* id is in hom *)
  _ : forall (A B C : T) (f : obj A -> obj B) (g : obj B -> obj C),
      hom f -> hom g -> hom (g \o f) ; (* hom is closed under composition *)
}.
Structure t : Type := Pack { car : Type ; class : class_of car }.
Module Exports.
Notation category := t.
Coercion car : category >-> Sortclass.
Definition El (C : t) : C -> Type :=
  let: Pack _ (Class x _ _ _) := C in x.
End Exports.
End Category.
Export Category.Exports.

Module CategoryHomPhant.
Section ClassDef.
Variables (C : category) (U V : C).
Local Notation U' := (El U).
Local Notation V' := (El V).
Let hom (X : category) : forall (A B : X), (El A -> El B) -> Prop :=
  let: Category.Pack _ (Category.Class _ x _ _) := X in x.
Definition axiom (f : U' -> V') := hom f.
Structure map (phUV : phant (U' -> V')) := Pack {apply; _ : axiom apply}.
Local Coercion apply : map >-> Funclass.
Variables (phUV : phant (U' -> V')) (f g : U' -> V') (cF : map phUV).
Definition class := let: Pack _ c as cF' := cF return axiom cF' in c.
Definition clone fA of phant_id g (apply cF) & phant_id fA class :=
  @Pack phUV f fA.
End ClassDef.
Module Exports.
Coercion apply : map >-> Funclass.
Notation Hom fA := (Pack (Phant _) fA).
Notation "{ 'hom' U , V }" := (map (Phant (El U -> El V)))
  (at level 0) : category_scope.
(*
Notation "{ 'hom' fUV }" := (map (Phant fUV))
  (at level 0, format "{ 'hom'  fUV }") : category_scope.
*)
End Exports.
End CategoryHomPhant.
Export CategoryHomPhant.Exports.

Open Scope category_scope.

Section category_interface.
Variable C : category.
Lemma category_id_proof : forall (a : C), @CategoryHomPhant.axiom C a a id.
Proof. by case: C => [? []]. Qed.
Definition category_id (a : C) : {hom a,a} := Hom (category_id_proof a).
(* 
Canonical category_id.
Variable A : C.
Check id : {hom A,A}.
(* this does not work *)
*)
Lemma category_comp_proof : forall (a b c : C) (f : {hom a,b}) (g : {hom b,c}),
    @CategoryHomPhant.axiom C a c (g \o f).
Proof.
case: C => [car [el hom ? hom_comp]] a b c f g.
by apply/hom_comp;case:f;case:g.
Qed.
Definition category_comp (a b c : C) (f : {hom a,b}) (g : {hom b,c})
  : {hom a,c} := Hom (category_comp_proof f g).
End category_interface.
Notation "'Id' a" := (category_id a) (at level 10) : category_scope.
Notation "g '\\o' f" := (category_comp f g) (at level 50) : category_scope.

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

(* map laws of a functor *)
Module FunctorLaws.
Section def.
Variable (C D : category).
Variable (M : C -> D) (f : forall A B, {hom A,B} -> {hom M A, M B}).
Definition id := forall A, f (Id A) = (Id (M A)) :> {hom M A, M A}.
Definition comp := forall A B C (g : {hom B,C}) (h : {hom A,B}),
  f (g \\o h) = f g \\o f h :> {hom M A, M C}.
End def.
End FunctorLaws.

Module Functor.
Record class_of (C D : category) (m : C -> D) : Type := Class {
  f : forall A B, {hom A,B} -> {hom m A, m B} ;
  _ : FunctorLaws.id f ;
  _ : FunctorLaws.comp f
}.
Structure t (C D : category) : Type := Pack { m : C -> D ; class : class_of m }.
Module Exports.
Variables (C D : category).
Notation functor := (t C D).
Coercion m : functor >-> Funclass.
Definition Fun (F : functor) : forall A B, {hom A, B} -> {hom F A, F B} :=
  let: Pack _ (Class f _ _) := F return forall A B, {hom A, B} -> {hom F A, F B} in f.
Arguments Fun _ [A] [B].
End Exports.
End Functor.
Export Functor.Exports.
Notation "F # f" := (Fun F f) (at level 11).
