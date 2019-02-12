Ltac typeof X := type of X.
Require Import FunctionalExtensionality Coq.Program.Tactics ProofIrrelevance.
Require Classical.
Require Import ssreflect ssrmatching ssrfun ssrbool.
From mathcomp Require Import eqtype ssrnat seq path div choice fintype tuple.
From mathcomp Require Import finfun bigop.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "A `2" (format "A `2", at level 3).
Reserved Notation "f ^`2" (format "f ^`2", at level 3).
Reserved Notation "l \\ p" (at level 50).
Reserved Notation "m >>= f" (at level 50).
Reserved Notation "f =<< m" (at level 50).
Reserved Notation "'do' x <- m ; e"
  (at level 60, x ident, m at level 200, e at level 60).
Reserved Notation "'do' x : T <- m ; e"
  (at level 60, x ident, m at level 200, e at level 60).
Reserved Notation "m >=> n" (at level 50).
Reserved Notation "n <=< m" (at level 50).
Reserved Notation "x '[~]' y" (at level 50).
Reserved Notation "'[~p]'".
Reserved Notation "f ($) m" (at level 11).
Reserved Notation "f (o) g" (at level 11).

Notation "l \\ p" := ([seq x <- l | x \notin p]).

Section funcomp_lemmas.
Lemma compA {A B C D} (f : C -> D) (g : B -> C) (h : A -> B) : f \o (g \o h) = (f \o g) \o h.
Proof. by []. Qed.

Lemma compfid A B (f : A -> B) : f \o id = f. Proof. by []. Qed.

Lemma compidf A B (f : A -> B) : id \o f = f. Proof. by []. Qed.

Lemma compE A B C (g : B -> C) (f : A -> B) a : (g \o f) a = g (f a).
Proof. by []. Qed.
End funcomp_lemmas.

(* Our `category' is always concrete; morphisms are just functions. *)
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
(*
Lemma hom_ext' (a b : C) (f g : El a -> El b) (p : hom f) (q : hom g) (H : f = g)
  : Hom p = Hom q.
Proof.
move:p q.
rewrite H=>p q.
by have->:p=q by apply/proof_irrelevance.
Qed.
Lemma hom_extext' (a b : C) (f g : El a -> El b) (p : hom f) (q : hom g)
      : (forall x, f x = g x) -> Hom p = Hom q.
Proof. by move/functional_extensionality=>H; apply hom_ext'. Qed.
*)
(*
Definition hom_ext_apply := locked Hom.apply.
Local Notation "[ 'ext' f ]" := (hom_ext_apply f).
*)
Local Notation "[ 'ext' f ]" := (Hom.apply f).
Lemma hom_ext (a b : C) (f g : {hom a,b}) : [ext f] = [ext g] -> f = g.
Proof.
case:f=>f Hf;case:g=>g Hg.
rewrite/Hom.apply=>H.
move:H Hf Hg=>->Hf Hg.
by have->:Hf=Hg by apply proof_irrelevance.
Qed.
Lemma hom_extext (a b : C) (f g : {hom a,b}) :
  (forall x, [ext f] x = [ext g] x) -> f = g.
Proof. by move/functional_extensionality=>H; apply hom_ext. Qed.
End category_lemmas.
(*Notation "[ 'ext' f ]" := (hom_ext_apply f).*)

Section Type_category.
Definition Type_category_class : Category.class_of Type :=
@Category.Class Type id (fun _ _ _ => True) (fun _ => I) (fun _ _ _ _ _ _ _ => I).
Canonical Type_category := Category.Pack Type_category_class.
Definition hom_Type (a b : Type) (f : a -> b) : {hom a,b} := Hom (I : hom (f : El a -> El b)).
End Type_category.

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
Notation "A `2" := (Squaring A).
Definition squaring_f A B (f : {hom A, B}) : {hom A`2,B`2} := hom_Type (fun x => (f x.1, f x.2)).
Lemma squaring_f_id : FunctorLaws.id squaring_f.
Proof. by move=> A /=; apply hom_extext => -[x1 x2]. Qed.
Lemma squaring_f_comp : FunctorLaws.comp squaring_f.
Proof. by move=> A B C g h /=; apply hom_extext => -[x1 x2]. Qed.
Definition squaring : functor _ _ :=
  Functor.Pack (Functor.Class squaring_f_id squaring_f_comp).
Notation "f ^`2" := (squaring # f).
End squaring.

Section functorid.
Variables C : category.
Definition id_f (A B : C) (f : {hom A,B}) := f.
Lemma id_id : FunctorLaws.id id_f. Proof. by move=>A;apply hom_extext. Qed.
Lemma id_comp : FunctorLaws.comp id_f. Proof. by move=>*;apply hom_extext. Qed.
Definition FId : functor _ _ := Functor.Pack (Functor.Class id_id id_comp).
Lemma FIdf (A B : C) (f : {hom A,B}) : FId # f = f.
Proof. by []. Qed.
End functorid.

Section functorcomposition.
Variables (C0 C1 C2 : category) (F : functor C1 C2) (G : functor C0 C1).
Definition functorcomposition a b := fun h : {hom a,b} => F # (G # h).
Lemma functorcomposition_id : FunctorLaws.id functorcomposition.
Proof.
by rewrite /FunctorLaws.id => A; rewrite /functorcomposition 2!functor_id.
Qed.
Lemma functorcomposition_comp : FunctorLaws.comp functorcomposition.
Proof.
rewrite /FunctorLaws.comp => a b c g h; rewrite /functorcomposition.
by rewrite 2!functor_o.
Qed.
Definition FComp : functor C0 C2:=
  Functor.Pack (Functor.Class functorcomposition_id functorcomposition_comp).
End functorcomposition.

Section functorcomposition_lemmas.
Variables (C0 C1 C2 C3 : category).
Lemma FCompId (f : functor C0 C1) : FComp f (FId C0) = f.
Proof.
destruct f as [m [f0 f1 f2]]; congr Functor.Pack; congr Functor.Class => //;
  exact/ProofIrrelevance.proof_irrelevance.
Qed.
Lemma FIdComp (f : functor C0 C1) : FComp (FId _) f = f.
Proof.
destruct f as [m [f0 f1 f2]]; congr Functor.Pack; congr Functor.Class => //;
  exact/ProofIrrelevance.proof_irrelevance.
Qed.
Lemma FCompA (f : functor C2 C3) (g : functor C1 C2) (h : functor C0 C1)
  : FComp (FComp f g) h = FComp f (FComp g h).
Proof.
destruct f as [m [f0 f1 f2]].
destruct g as [n [g0 g1 g2]].
destruct h as [o [h0 h1 h2]].
congr Functor.Pack; congr Functor.Class => //;
  exact/ProofIrrelevance.proof_irrelevance.
Qed.
Lemma FCompE (f : functor C1 C2) (g : functor C0 C1) A B (k : {hom A, B}) : (FComp f g) # k = f # (g # k).
Proof. by []. Qed.
End functorcomposition_lemmas.

Section natural_transformation.
Variables (C D : category) (f g : functor C D).
Definition transformation_type := forall A, {hom f A ,g A}.
Definition naturalP (phi : transformation_type) :=
  forall A B (h : {hom A,B}), (g # h) \o (phi A) = (phi B) \o (f # h).
End natural_transformation.
Arguments naturalP [C D] f g.

Section natural_transformation_example.
Definition fork' A (a : A) := (a, a).
Definition fork A := hom_Type (@fork' A).
(* fork is a natural transformation FId -> squaring *)
Lemma fork_natural : naturalP (FId _) squaring fork.
Proof. by []. Qed.
End natural_transformation_example.
