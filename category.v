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

Module Hom.
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
Notation hom f := (axiom f).
Coercion apply : map >-> Funclass.
Notation Hom fA := (Pack (Phant _) fA).
Notation "{ 'hom' U , V }" := (map (Phant (El U -> El V)))
  (at level 0) : category_scope.
Notation "[ 'hom' 'of' f 'as' g ]" := (@clone _ _ _ _ f g _ _ idfun id)
  (at level 0, format "[ 'hom'  'of'  f  'as'  g ]") : category_scope.
Notation "[ 'hom' 'of' f ]" := (@clone _ _ _ _ f f _ _ id id)
  (at level 0, format "[ 'hom'  'of'  f ]") : category_scope.
(*
Notation "{ 'hom' fUV }" := (map (Phant fUV))
  (at level 0, format "{ 'hom'  fUV }") : category_scope.
*)
End Exports.
End Hom.
Export Hom.Exports.

Open Scope category_scope.

Section category_interface.
Variable C : category.

Lemma category_idfun_proof : forall (a : C), hom (idfun : El a -> El a).
Proof. by case: C => [? []]. Qed.
Canonical idfun_hom a := Hom (category_idfun_proof a).
Lemma category_comp_proof : forall (a b c : C) (f : {hom a,b}) (g : {hom b,c}),
    hom (g \o f).
Proof.
case: C => [car [el hom ? hom_comp]] a b c f g.
by apply/hom_comp;case:f;case:g.
Qed.
Canonical comp_hom (a b c : C) (f : {hom a, b}) (g : {hom b, c}) := Hom (category_comp_proof f g).

Variables (a b c:C) (f : {hom a,b}) (g : {hom b,c}).
Check [hom of (g \o f)].
End category_interface.
(*
Notation "'Id' a" := (category_id a) (at level 10) : category_scope.
Notation "g '\\o' f" := (category_comp f g) (at level 50) : category_scope.
*)

Section category_lemmas.
Variable C : category.
Lemma hom_ext (a b : C) (f g : El a -> El b) (p : hom f) (q : hom g) (H : f = g)
  : Hom p = Hom q.
Proof.
move:p q.
rewrite H=>p q.
by have->:p=q by apply/proof_irrelevance.
Qed.
Lemma hom_extext (a b : C) (f g : El a -> El b) (p : hom f) (q : hom g)
      : (forall x, f x = g x) -> Hom p = Hom q.
Proof.
move/functional_extensionality=>H.
by apply hom_ext.
Qed.
End category_lemmas.

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
Definition hom_Type (a b : Type) (f : a -> b) : {hom a,b} := Hom (I : hom (f : El a -> El b)).
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
Definition id := forall A, f [hom of idfun] = [hom of idfun] :> {hom M A, M A}.
Definition comp := forall A B C (g : {hom B,C}) (h : {hom A,B}),
  f [hom of g \o h] = [hom of f g \o f h] :> {hom M A, M C}.
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
Section exports.
Variables (C D : category).
Definition Fun (F : t C D) : forall A B, {hom A, B} -> {hom m F A, m F B} :=
  let: Pack _ (Class f _ _) := F return forall A B, {hom A, B} -> {hom m F A, m F B} in f.
Arguments Fun _ [A] [B].
End exports.
Notation functor := t.
Coercion m : functor >-> Funclass.
End Exports.
End Functor.
Export Functor.Exports.
Notation "F # f" := (Fun F f) (at level 11).

Section functor_lemmas.
Variable C D : category.
Variable F : functor C D.
Lemma functor_id : FunctorLaws.id (Fun F).
Proof. by case: F => [? []]. Qed.
Lemma functor_o : FunctorLaws.comp (Fun F).
Proof. by case: F => [? []]. Qed.
End functor_lemmas.

Section squaring.
Definition Squaring (A : Type) := (A * A)%type.
Notation "A `2" := (Squaring A) (at level 100).
Definition squaring_f A B (f : {hom A, B}) : {hom A`2,B`2} := hom_Type (fun x => (f x.1, f x.2)).
Lemma squaring_f_id : FunctorLaws.id squaring_f.
Proof. by move=> A /=; apply hom_extext => -[x1 x2]. Qed.
Lemma squaring_f_comp : FunctorLaws.comp squaring_f.
Proof. by move=> A B C g h /=; apply hom_extext => -[x1 x2]. Qed.
Definition squaring : functor _ _ :=
  Functor.Pack (Functor.Class squaring_f_id squaring_f_comp).
Notation "f ^`2" := (squaring # f) (at level 100).
End squaring.

Section functorid.
Definition id_f (A B : Type) (f : {hom A,B}) := hom_Type f.
Lemma id_id : FunctorLaws.id id_f. Proof. by move=>A;apply hom_extext. Qed.
Lemma id_comp : FunctorLaws.comp id_f. Proof. by move=>*;apply hom_extext. Qed.
Definition FId : functor _ _ := Functor.Pack (Functor.Class id_id id_comp).
End functorid.

