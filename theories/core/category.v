(* monae: Monadic equational reasoning in Rocq                                *)
(* Copyright (C) 2025 monae authors, license: LGPL-2.1-or-later               *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import boolp.
Require Import preamble.

(**md**************************************************************************)
(* # Formalization of basic category theory                                   *)
(*                                                                            *)
(* This file provides definitions of category, functor, monad, as well as     *)
(* basic theorems. It comes as a generalization of the first part of          *)
(* hierarchy.v which is specialized to the category of sets.                  *)
(*                                                                            *)
(* ```                                                                        *)
(*            category == type of categories, a category C is implemented     *)
(*                        with a universe a la Tarski, there is a realizer    *)
(*                        function el that associates to each object A the    *)
(*                        type el A of its elements; this corresponds to the  *)
(*                        definition of concrete categories                   *)
(*        {hom A -> B} == the hom-set of morphisms from A to B, where A and B *)
(*                        are objects of a category C                         *)
(*         FunctorLaws == module that defines the functor laws                *)
(*             F ~~> G == unnatural transformation, i.e., functions of type   *)
(*                        forall a, {hom F a ,G a};  corresponds to a         *)
(*                        natural transformation when it satisfies the        *)
(*                        predicate naturality                                *)
(*              F ~> G == natural transformation: F ~~> G with naturality     *)
(*                 NId == the identity natural transformation                 *)
(*          [NEq F, G] == natural transformation from F to G, where the       *)
(*                        object parts of F and G are convertible, and the    *)
(*                        morphism parts are transportable; e.g., when they   *)
(*                        are compositions that differ only by associativity  *)
(*                        or insertion of identity functors                   *)
(*                  \v == vertical composition                                *)
(*                  \h == horizontal composition, or Godement product         *)
(*              F -| G == pair of adjoint functors (Module                    *)
(*                        Module AdjointFunctors); see also TriangularLaws.   *)
(*      Module AdjComp == define a pair of adjoint functors by composition of *)
(*                        two pairs of adjoint functors                       *)
(*  JoinLaws, BindLaws == modules that define the monad laws                  *)
(*             isMonad == mixin that defines the monad interface              *)
(*   Monad_of_ret_join == factory, monad defined by ret and join              *)
(*   Monad_of_ret_bind == factory, monad defined by ret and bind;             *)
(*                        M need not be a priori a functor                    *)
(* Monad_of_adjoint_functors == monad defined from a pair of adjoint functors *)
(* ```                                                                        *)
(******************************************************************************)

Reserved Notation "F ~~> G" (at level 51).
Reserved Notation "'{' 'hom' U '->' V '}'"
  (at level 0, U at level 98, V at level 99, format "{ 'hom'  U  ->  V }").
Reserved Notation "'{' 'hom' '[' C ']' U '->' V '}'"
  (at level 0, U at level 98, V at level 99, format "{ 'hom' [ C ]  U  ->  V }").

Declare Scope category_scope.
Delimit Scope category_scope with category.

Local Open Scope category_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* opaque ssrfun.frefl blocks some proofs involving functor_ext *)
#[global]
Remove Hints frefl : core.

Lemma frefl_transparent A B (f : A -> B) : f =1 f.
Proof. by []. Defined.

#[global]
Hint Resolve frefl_transparent : core.

HB.mixin Record isCategory (obj : Type) := {
  hom : obj -> obj -> Type ;
  id : forall a, hom a a ;
  comp : forall {a b c}, hom a b -> hom b c -> hom a c ;
  left_id : forall a b (f : hom a b), comp f (id b) = f ;
  right_id : forall a b (f : hom a b), comp (id a) f = f ;
  assoc : forall a b c d (f : hom a b) (g : hom b c) (h : hom c d),
      comp (comp f g) h = comp f (comp g h);
}.
Arguments isCategory.phant_Build : clear implicits.

#[short(type=category)]
HB.structure Definition Category := {C of isCategory C}.
Arguments id {C} : rename.
Arguments comp {C a b c} : rename.

Notation "{ 'hom' U -> V }" := (hom U V) : category_scope.
Notation "{ 'hom' '[' C ']' U '->' V }" := (@hom C U V)
  (only parsing) : category_scope.

(* Notations \c and [\c f , .. , g , h] for hom compositions. *)
Notation "[id]" := (id _).
Notation "g \c f" := (comp f g) (at level 50, format "g  \c  f").
Module comps_notation.

Notation "[ '\o' f , g , .. , h ]" := ( .. (f \o g) .. \o h) (at level 0,
  format "[ '[' '\o'  f ,  g ,  '/' .. ,  '/' h ']' ]") : category_scope.
Notation "[ '\c' f , g , .. , h ]" := ( .. (f \c g) .. \c h) (at level 0,
  format "[ '[' '\c'  f ,  g ,  '/' .. ,  '/' h ']' ]") : category_scope.
End comps_notation.

(* transportation of hom along equality *)
Section transport_lemmas.
Variable C : category.
Definition transport_dom
  (a a' b : C) (p : a = a') (f : {hom a -> b}) : {hom a' -> b} :=
    eq_rect a (fun x => {hom x -> b}) f a' p.
Definition transport_codom
  (a b b' : C) (p : b = b') (f : {hom a -> b}) : {hom a  -> b'} :=
    eq_rect b (fun x => {hom a -> x}) f b' p.
Definition transport_hom (a a' b b' : C) (pa : a = a') (pb : b = b')
  (f : {hom a -> b}) : {hom a' -> b'} :=
  eq_rect b (fun y => {hom a' -> y})
          (eq_rect a (fun x => {hom x -> b}) f a' pa)
          b' pb.
Definition hom_of_eq (a b : C) (p : a = b) : {hom a -> b} :=
  transport_codom p (id a).
End transport_lemmas.

Section concrete_transport_lemmas.
Variable C : category.
(* F for factorization *)
Lemma transport_domF (a a' b : C) (p : a = a') (f : {hom a -> b}) :
  transport_dom p f = f \c hom_of_eq (esym p).
Proof. by subst a'=> /=; rewrite right_id. Qed.

Lemma transport_codomF (a b b' : C) (p : b = b') (f : {hom a -> b}) :
  transport_codom p f = hom_of_eq p \c f.
Proof. by subst b'=> /=; rewrite left_id. Qed.
Lemma transport_homF (a a' b b' : C) (pa : a = a') (pb : b = b') (f : {hom a -> b}) :
  transport_hom pa pb f = hom_of_eq pb \c f \c hom_of_eq (esym pa).
Proof. by subst a' b'=> //=; rewrite left_id right_id. Qed.
End concrete_transport_lemmas.

Section Type_as_a_category.
(* TODO: consider using universe polymorphism *)
Let UUx := Type@{UU_category}.

HB.instance Definition _ :=
  isCategory.Build
    UUx (fun a b => a -> b) (@idfun) (fun _ _ _ f g => g \o f)
    (fun _ _ _ => erefl)
    (fun _ _ _ => erefl)
    (fun _ _ _ _ _ _ _ => erefl).

End Type_as_a_category.

Module FunctorLaws.
Section def.
Variable (C D : category).
Variable (F : C -> D) (f : forall a b, {hom a -> b} -> {hom F a -> F b}).
Definition id := forall a, f (id a) = (id (F a)).
Definition comp := forall a b c (g : {hom b -> c}) (h : {hom a -> b}),
  f (g \c h) = f g \c f h.
End def.
End FunctorLaws.

HB.mixin Record isFunctor (C D : category) (F : C -> D) := {
  Fhom : forall a b, {hom a -> b} -> {hom F a -> F b} ;
  Fhom_id : FunctorLaws.id Fhom ;
  Fhom_comp : FunctorLaws.comp Fhom }.

#[short(type=functor)]
HB.structure Definition Functor C D := {F of isFunctor C D F}.
Arguments Fhom_id {C D}.
Arguments Fhom_comp {C D}.

Definition functor_phant (C D : category) of phant (C -> D) := functor C D.
Arguments Fhom {C D} F {a b} f: rename.
Notation "F # f" := (Fhom F f) : category_scope.
Notation "{ 'functor' fCD }" := (functor_phant (Phant fCD))
                                  (format "{ 'functor'  fCD }"): category_scope.

Section functor_lemmas.
Variables (C D : category) (F : {functor C -> D}).

Lemma functor_ext (G : {functor C -> D}) (pm : F =1 G) :
  (forall (A B : C) (f : {hom A -> B}),
      transport_hom (pm A) (pm B) (F # f) = G # f) -> F = G.
Proof.
move: pm.
case: F => mf cf; case: G => mg cg /= pm.
move: cf cg.
rewrite /transport_hom.
move: (funext pm) => ppm.
subst mg => -[[ff idf cf]] -[[fg idg cg]] p.
have pp : ff = fg.
  apply functional_extensionality_dep=> A.
  apply functional_extensionality_dep=> B.
  apply functional_extensionality_dep=> f.
  move: (p A B f).
  have -> // : pm = (fun _ => erefl).
  exact: proof_irr.
rewrite {p}.
move: idf cf idg cg; rewrite pp => idf cf idg cg.
have -> : idf = idg by exact: proof_irr.
have -> : cf = cg by exact: proof_irr.
exact: erefl.
Qed.
End functor_lemmas.

Section Fhom_comp_tail.
Import comps_notation.
Variable C D : category.
Lemma Fhom_comp_tail (F : {functor C -> D})
      a b c d (g : {hom b -> c}) (h : {hom a -> b}) (k : {hom F c -> d}) :
  k \c (F # (g \c h)) = [\c k, F # g, F # h].
Proof. by rewrite Fhom_comp assoc. Qed.
End Fhom_comp_tail.
Arguments Fhom_comp_tail [C D] F [a b c d].

Section functorid.
Variables C : category.
Definition id_f (A B : C) (f : {hom A -> B}) := f.
Lemma id_id : FunctorLaws.id id_f. Proof. by []. Qed.
Lemma id_comp : FunctorLaws.comp id_f. Proof. by []. Qed.
Let _id (x : C) := x.
HB.instance Definition _ := isFunctor.Build C C _id id_id id_comp.
Definition FId : {functor C -> C} := _id.
Lemma FIdf (A B : C) (f : {hom A -> B}) : FId # f = f.
Proof. by []. Qed.
End functorid.
Arguments FId {C}.

Section functorcomposition.
Variables C0 C1 C2 : category.
Variables (F : {functor C1 -> C2}) (G : {functor C0 -> C1}).

Definition functorcomposition a b := fun h : {hom a -> b} => F # (G # h).

Lemma functorcomposition_id : FunctorLaws.id functorcomposition.
Proof. by move=> A; rewrite /functorcomposition 2!Fhom_id. Qed.

Lemma functorcomposition_comp : FunctorLaws.comp functorcomposition.
Proof.
by move=> a b c g h; rewrite /functorcomposition; rewrite 2!Fhom_comp.
Qed.

HB.instance Definition _ :=
  isFunctor.Build C0 C2 (F \o G) functorcomposition_id functorcomposition_comp.
End functorcomposition.


Section functorcomposition_lemmas.
Lemma FCompE (C0 C1 C2 : category)
  (F : {functor C1 -> C2}) (G : {functor C0 -> C1}) a b (k : {hom a -> b}) :
  (F \o G) # k = F # (G # k).
Proof. by []. Qed.

Variables (C0 C1 C2 C3 : category).

Lemma FCompId (F : {functor C0 -> C1}) : F \o FId = F :> {functor _ -> _}.
Proof. by apply: functor_ext=> *; rewrite FCompE FIdf. Qed.

Lemma FIdComp (F : {functor C0 -> C1}) : FId \o F = F :> {functor _ -> _}.
Proof. by apply: functor_ext=> *; rewrite FCompE FIdf. Qed.

Lemma FCompA
  (F : {functor C2 -> C3}) (G : {functor C1 -> C2}) (H : {functor C0 -> C1}) :
  (F \o G) \o H = F \o (G \o H) :> {functor _ -> _}.
Proof. apply: functor_ext=> *; by rewrite FCompE. Qed.
End functorcomposition_lemmas.

Notation "F ~~> G" := (forall a, {hom F a -> G a}) : category_scope.
Definition naturality (C D : category) (F G : {functor C -> D}) (f : F ~~> G) :=
  forall a b (h : {hom a -> b}), (G # h) \c (f a) = (f b) \c (F # h).
Arguments naturality [C D].
HB.mixin Record isNatural
         (C D : category) (F G : {functor C -> D}) (f : F ~~> G) :=
  {natural : naturality F G f}.
#[short(type=nattrans)]
HB.structure Definition Nattrans
             (C D : category) (F G : {functor C -> D}) :=
  {f of isNatural C D F G f}.
Arguments natural [C D F G] phi : rename.
Notation "F ~> G" := (nattrans F G) : category_scope.

Section natural_transformation_lemmas.
Import comps_notation.
Variables (C D : category) (F G : {functor C -> D}).
Lemma natural_tail (phi : F ~> G) a b c (h : {hom a -> b}) (f : {hom G b -> c}) :
  [\c f, G # h, phi a] = [\c f, phi b, F # h].
Proof. by rewrite -!assoc natural. Qed.

Lemma nattrans_ext (f g : F ~> G) :
  f = g <-> forall a, f a = g a.
Proof.
split => [ -> // |]; move: f g => [f [[Hf]]] [g [[Hg]]] /= fg''.
have fg' : forall a, f a = g a by move=> a; rewrite fg''.
move: (functional_extensionality_dep fg') => fg.
by move: Hf Hg; rewrite fg=> Hf Hg; rewrite (proof_irr Hf Hg).
Qed.
End natural_transformation_lemmas.
Arguments natural_tail [C D F G].

Section id_natural_transformation.
Variables (C D : category) (F : {functor C -> D}).
Definition unnattrans_id := fun (a : C) => id (F a).
Definition natural_id : naturality _ _ unnattrans_id.
Proof. by move=> *; rewrite left_id right_id. Qed.

HB.instance Definition _ :=
  isNatural.Build C D F F unnattrans_id natural_id.
Definition NId : F ~> F := locked (unnattrans_id : _ ~> _).
Lemma NIdE : NId  = (fun a => id (F a)) :> (_ ~~> _).
Proof. by rewrite /NId -lock. Qed.
End id_natural_transformation.

Module NEq.
Section def.
Import comps_notation.
Variables (C D : category) (F G : {functor C -> D}).
Variable (Iobj : forall c, F c = G c).
Local Notation tc := (transport_codom (Iobj _)).
Local Notation td := (transport_dom (esym (Iobj _))).
Variable (Imor : forall a b (f : {hom a -> b}), tc (F # f) = td (G # f)).
Definition f : F ~~> G := fun (c : C) => tc (id (F c)).
Lemma natural : naturality F G f.
Proof.
move=> a b h.
rewrite /f !transport_codomF !right_id.
have -> : (hom_of_eq (Iobj b) \c F # h) = tc (F # h)
  by rewrite transport_codomF.
by rewrite Imor transport_domF /= esymK.
Qed.

HB.instance Definition _ := isNatural.Build C D F G f natural.
Definition n : F ~> G := f.
End def.
Module Exports.
(*Arguments f [C D F G] c / : rename.*)
Arguments f [C D F G] Iobj /.
Arguments n [C D] : simpl never.
Notation NEq := n.
Lemma NEqE C D F G Iobj Imor :
  @NEq C D F G Iobj Imor =
  (fun a => transport_codom (Iobj _) (id (F a))) :> (_ ~~> _).
Proof. by []. Qed.
End Exports.
End NEq.
Export NEq.Exports.
Notation "[ 'NEq' F , G ]" :=
  (NEq F G (fun a => erefl) (fun a b f => erefl))
    (at level 0, format "[ 'NEq'  F ,  G ]") : category_scope.

Section vertical_composition.
Variables (C D : category) (F G H : {functor C -> D}).
Variables (g : G ~> H) (f : F ~> G).
Definition vcomp := fun a => g a \c f a.
Definition natural_vcomp : naturality _ _ vcomp.
Proof. by move=> a b h; rewrite assoc (natural g) -assoc (natural f) -assoc. Qed.
HB.instance Definition _ := isNatural.Build C D F H
  vcomp natural_vcomp.
Definition VComp : F ~> H := vcomp.
End vertical_composition.
Notation "f \v g" := (locked (VComp f g)).

Section vcomp_lemmas.
Variables (C D : category) (F G H : {functor C -> D}).
Variables (g : G ~> H) (f : F ~> G).
Lemma VCompE_nat : g \v f = (fun a => g a \c f a) :> (_ ~~> _).
Proof. by unlock. Qed.
Lemma VCompE a : (g \v f) a = g a \c f a.
Proof. by unlock. Qed.
End vcomp_lemmas.

Section vcomp_lemmas2.
Variables (C D : category) (F G H I : {functor C -> D}).
Variables (h : H ~> I) (g : G ~> H) (f : F ~> G).

Lemma VCompId : f \v NId F = f.
Proof. by apply nattrans_ext=> a; rewrite VCompE NIdE right_id. Qed.
Lemma VIdComp : NId G \v f = f.
Proof. by apply nattrans_ext=> a; rewrite VCompE NIdE left_id. Qed.
Lemma VCompA : (h \v g) \v f = h \v (g \v f).
Proof. by apply nattrans_ext=> a; rewrite !VCompE !assoc. Qed.
End vcomp_lemmas2.

Section horizontal_composition.
Variables (C D E : category) (F G : {functor C -> D}) (F' G' : {functor D -> E}).
Variables (s : F ~> G) (t : F' ~> G').

Definition hcomp : F' \o F ~~> G' \o G :=
  fun (c : C) => t (G c) \c F' # s c.
Lemma natural_hcomp : naturality (F' \o F) (G' \o G) hcomp.
Proof.
move=> c0 c1 h.
rewrite [in LHS]assoc (natural t) -[in LHS]assoc -[in RHS]assoc; congr (_ \c _).
rewrite [in RHS]FCompE.
rewrite -2!(@Fhom_comp D). (* TODO: why must D be explicit? *)
congr (F' # _).
by rewrite natural.
Qed.

HB.instance Definition _ := isNatural.Build C E (F' \o F) (G' \o G)
  hcomp natural_hcomp.

Definition HComp : F' \o F ~> G' \o G := hcomp.
End horizontal_composition.
Notation "f \h g" := (locked (HComp g f)).

Section hcomp_extensionality_lemmas.
Variables (C D E : category) (F G : {functor C -> D}) (F' G' : {functor D -> E}).
Variables (s : F ~> G) (t : F' ~> G').
Lemma HCompE_def : t \h s = HComp s t. Proof. by unlock. Qed.
Lemma HCompE c : (t \h s) c = t (G c) \c F' # s c.
Proof. by unlock. Qed.
Lemma HCompE_alt c : (t \h s) c = G' # (s c) \c t (F c).
Proof. by rewrite HCompE natural. Qed.
End hcomp_extensionality_lemmas.

Section hcomp_id_assoc_lemmas.
Import comps_notation.
Variables C D E Z : category.
Variables (F G : {functor C -> D}) (F' G' : {functor D -> E}) (F'' G'' : {functor E -> Z}).
Variables (s : F ~> G) (t : F' ~> G') (u : F'' ~> G'').

Lemma HCompId c : (t \h NId F) c = t (F c).
Proof. by rewrite HCompE NIdE Fhom_id right_id. Qed.
Lemma HIdComp c : (NId G' \h s) c = G' # s c.
Proof. by rewrite HCompE NIdE left_id. Qed.
(* TODO: introduce the application of a functor to a natural transformation? *)

Lemma HCompA c : ((u \h t) \h s) c = (u \h (t \h s)) c.
Proof. by rewrite !HCompE -assoc FCompE Fhom_comp. Qed.

Lemma HCompA_nat : (u \h t) \h s =
  [NEq G'' \o (G' \o G) , (G'' \o G') \o G]
  \v (u \h (t \h s))
  \v [NEq (F'' \o F') \o F , F'' \o (F' \o F)].
Proof.
apply nattrans_ext => c.
rewrite 2!VCompE /= left_id right_id.
by rewrite HCompA.
Qed.
End hcomp_id_assoc_lemmas.

Section hcomp_lemmas.
Variables (C D E : category).
Variables (F G : {functor C -> D}) (F' G' : {functor D -> E}).
Variables (s : F ~> G) (t : F' ~> G').

(* higher level horizontal composition is a vertical composition of
   horizontal compositions *)
Lemma HComp_VH : t \h s = (t \h NId G) \v (NId F' \h s).
Proof. by apply nattrans_ext=> a; rewrite VCompE HCompE HIdComp HCompId. Qed.
Lemma HComp_VH_aux : t \h s = (NId G' \h s) \v (t \h NId F).
Proof.
by apply nattrans_ext=> a; rewrite VCompE HCompE HIdComp HCompId -natural.
Qed.

Lemma NIdFId c : NId (@FId C) c = [id].
Proof. by rewrite NIdE. Qed.

Lemma NIdFComp : NId (F' \o F) = (NId F') \h (NId F).
Proof.
by apply nattrans_ext => c /=; rewrite HCompE !NIdE /= left_id Fhom_id.
Qed.
End hcomp_lemmas.

Section hcomp_lemmas.
(* horizontal and vertical compositions interchange *)
Variables (C D E : category).
Variables (F G H : {functor C -> D}) (F' G' H' : {functor D -> E}).
Variables (s : F ~> G) (t : F' ~> G').
Variables (s' : G ~> H) (t' : G' ~> H').
Lemma HCompACA : (t' \h s') \v (t \h s) = (t' \v t) \h (s' \v s).
Proof.
rewrite (HComp_VH s' t') (HComp_VH s t).
rewrite -VCompA (VCompA (t' \h NId H)) -HComp_VH_aux (HComp_VH s' t).
apply nattrans_ext => c /=.
rewrite !HCompE !VCompE !HCompE !NIdE /= !left_id !Fhom_id !right_id.
by rewrite -!assoc Fhom_comp.
Qed.
End hcomp_lemmas.

(* adjoint functor *)
(* We define adjointness F -| G in terms of its unit and counit. *)

Module TriangularLaws.
Section triangularlaws.
Variables (C D : category) (F : {functor C -> D}) (G : {functor D -> C}).
Variables (eta : FId ~> G \o F) (eps : F \o G ~> FId).
Definition left := forall c, eps (F c) \c F # (eta c) = [id].
Definition right := forall d, G # (eps d) \c eta (G d) = [id].
Definition left_tail := forall c d (k : {hom F c -> d}),
    k \c eps (F c) \c F # (eta c) = k.
Definition right_tail := forall c d (k : {hom G d -> c}),
    k \c G # (eps d) \c eta (G d) = k.
End triangularlaws.
End TriangularLaws.

Module AdjointFunctors.
Section def.
Variables (C D : category) (F : {functor C -> D}) (G : {functor D -> C}).
Record t := mk {
  eta : FId ~> G \o F ;
  eps : F \o G ~> FId ;
  triL : TriangularLaws.left eta eps ;
  triR : TriangularLaws.right eta eps
}.
End def.
Section lemmas.
Local Notation "F -| G" := (t F G).
Variables (C D : category) (F : {functor C -> D}) (G : {functor D -> C}).
Variable A : F -| G.

Lemma triL_tail : TriangularLaws.left_tail (eta A) (eps A).
Proof. by move=> ? ? ?; rewrite -assoc triL right_id. Qed.

Lemma triR_tail : TriangularLaws.right_tail (eta A) (eps A).
Proof. by move=> ? ? ?; rewrite -assoc triR right_id. Qed.

Definition hom_iso c d : {hom F c -> d} -> {hom c -> G d} :=
  fun h => (G # h) \c (eta A c).

Definition hom_inv c d : {hom c -> G d} -> {hom F c -> d} :=
  fun h => (eps A d) \c (F # h).

Import comps_notation.

Lemma hom_isoK (c : C) (d : D) (f : {hom F c -> d}) : hom_inv (hom_iso f) = f.
Proof.
rewrite /hom_inv /hom_iso.
by rewrite Fhom_comp !assoc -(natural (eps _)) triL_tail FIdf.
Qed.
Lemma hom_invK (c : C) (d : D) (g : {hom c -> G d}) : hom_iso (hom_inv g) = g.
Proof.
rewrite /hom_inv /hom_iso.
by rewrite Fhom_comp (natural_tail (eta _)) triR FIdf left_id.
Qed.

Lemma hom_iso_inj (c : C) (d : D) : injective (@hom_iso c d).
Proof. exact: can_inj (@hom_isoK c d). Qed.
Lemma hom_inv_inj (c : C) (d : D) : injective (@hom_inv c d).
Proof. exact: can_inj (@hom_invK c d). Qed.

Lemma eta_hom_iso (c : C) : eta A c = hom_iso [id].
Proof. by rewrite /hom_iso /= Fhom_id left_id. Qed.
Lemma eps_hom_inv (d : D) : eps A d = hom_inv [id].
Proof. by rewrite /hom_inv /= Fhom_id right_id. Qed.

Lemma ext (B : F -| G) : eta A = eta B -> eps A = eps B -> A = B.
Proof.
move: A B => [? ? ? ?] [? ? ? ?] /= ? ?; subst.
congr mk; exact/proof_irr.
Qed.

(*
Lemma left_unique (F' : functor C D) (B : adjunction F' G) :
  exists phi, phi : natural_isomorphism F F'.
Lemma right_unique (G' : functor D C) (B : adjunction F G') :
  exists phi, phi : natural_isomorphism G G'.
*)

End lemmas.
Arguments hom_isoK [C D F G].
Arguments hom_invK [C D F G].
Arguments hom_iso_inj [C D F G].
Arguments hom_inv_inj [C D F G].
End AdjointFunctors.
Notation "F -| G" := (AdjointFunctors.t F G).


Module AdjComp.
Section def.
Import comps_notation.
Variables C0 C1 C2 : category.
Variables (F0 : {functor C0 -> C1}) (G0 : {functor C1 -> C0}).
Variables (F1 : {functor C1 -> C2}) (G1 : {functor C2 -> C1}).
Variables
  (eta0 : FId ~> G0 \o F0) (eta1 : FId ~> G1 \o F1)
  (eps0 : F0 \o G0 ~> FId) (eps1 : F1 \o G1 ~> FId)
  (triL0 : TriangularLaws.left eta0 eps0)
  (triL1 : TriangularLaws.left eta1 eps1)
  (triR0 : TriangularLaws.right eta0 eps0)
  (triR1 : TriangularLaws.right eta1 eps1).

Definition F := F1 \o F0.
Definition G := G0 \o G1.

Definition Eta : FId ~> G \o F :=
  [NEq G0 \o (G1 \o F1) \o F0 , G \o F]
    \v (NId G0 \h eta1 \h NId F0)
    \v [NEq G0 \o F0 , G0 \o FId \o F0]
    \v eta0.
Lemma EtaE a : Eta a = G0 # (eta1 (F0 a)) \c (eta0 a).
Proof. by rewrite !VCompE /= left_id right_id HCompId HIdComp. Qed.

Definition Eps : F \o G ~> FId :=
  (eps1)
    \v [NEq F1 \o FId \o G1 , F1 \o G1]
    \v (NId F1 \h eps0 \h NId G1)
    \v [NEq F \o G , (F1 \o (F0 \o G0)) \o G1].
Lemma EpsE a : Eps a = (eps1 _) \c F1 # (eps0 (G1 a)).
Proof. by rewrite !VCompE /= !right_id HCompId HIdComp. Qed.

Lemma triL : TriangularLaws.left Eta Eps.
Proof.
(* NB(tanaka): This proof does NOT follow the manner of 2-category, for now. *)
move=> c/=.
rewrite EpsE EtaE.
rewrite (Fhom_comp_tail F).
rewrite -(Fhom_comp_tail F1 (eps0 _)).
rewrite -(natural eps0) FIdf.
rewrite Fhom_comp !assoc triL1 left_id.
by rewrite -(Fhom_comp F1) triL0 Fhom_id.
Qed.

Lemma triR : TriangularLaws.right Eta Eps.
Proof.
move=> c.
rewrite EpsE EtaE.
rewrite (Fhom_comp G)/= !assoc.
rewrite -(Fhom_comp_tail G0).
rewrite (natural eta1) FIdf.
rewrite Fhom_comp -!assoc triR0 right_id.
by rewrite -(Fhom_comp G0) triR1 Fhom_id.
Qed.

End def.

Module Exports.
Section adj_comp.
Variables (C0 C1 C2 : category).
Variables (F : {functor C0 -> C1}) (G : {functor C1 -> C0}) (A0 : F -| G).
Variables (F' : {functor C1 -> C2}) (G' : {functor C2 -> C1}) (A1 : F' -| G').
Definition adj_comp := AdjointFunctors.mk
  (triL (AdjointFunctors.triL A0) (AdjointFunctors.triL A1))
  (triR (AdjointFunctors.triR A0) (AdjointFunctors.triR A1)).
End adj_comp.
End Exports.
End AdjComp.
Export AdjComp.Exports.

Module JoinLaws.
Section join_laws.
Variables (C : category) (M : {functor C -> C}) .
Variables (ret : FId ~~> M) (join : M \o M ~~> M).
Definition left_unit :=
  forall a, join a \c ret (M a) = [id].
Definition right_unit :=
  forall a, join a \c M # ret a = [id].
Definition associativity :=
  forall a, join a \c M # join a = join a \c join (M a).
End join_laws.
End JoinLaws.

Module BindLaws.
(*
bind is usually typed in the literature as follows:

bind : forall A B, M A -> (A -> M B) -> M B.
Notation "m >>= f" := (b m f).

We use a different type to keep the {hom _ -> _} structures:

bind : forall a b, {hom a -> M b} -> {hom M a -> M b}.
Notation "m >>= f" := (fn (bind f) m).
*)
Section abscat.
Variables (C : category) (*M : {functor C -> C}*) (M : C -> C).
Variable bind : forall a b, {hom a -> M b} -> {hom M a -> M b}.
Variable ret : forall a, {hom a -> M a}.

Definition associative :=
  forall a b c (f : {hom a -> M b}) (g : {hom b -> M c}),
  bind g \c bind f = bind (bind g \c f).
Definition left_neutral :=
  forall a b (f : {hom a -> M b}), (bind f \c ret a) = f.
Definition right_neutral :=
  forall a, bind (ret a) = [id].
End abscat.

End BindLaws.

HB.mixin Record isMonad (C : category) (M : C -> C) of @Functor C C M := {
  ret : FId ~> M ;
  join : M \o M ~> M ;
  bind : forall (a b : C), {hom a -> M b} -> {hom M a -> M b} ;
  bindE : forall (a b : C) (f : {hom a -> M b}),
    bind a b f = join b \c M # f ;
  joinretM : JoinLaws.left_unit ret join ;
  joinMret : JoinLaws.right_unit ret join ;
  joinA : JoinLaws.associativity join
}.
#[short(type=monad)]
HB.structure Definition Monad (C : category) := {M of isMonad C M &}.
Arguments bind {C M a b} : rename, simpl never.
Notation "m >>= f" := (bind f m).

Section monad_interface.
Variable (C : category) (M : monad C).
(* *_tail lemmas are for g and h in ((f \c .. \c g) \c h) *)
Import comps_notation.
Lemma fmap_bindret (a b : C) (f : {hom a -> b}) : M # f = bind (ret b \c f).
Proof. by rewrite bindE Fhom_comp assoc joinMret left_id. Qed.
Lemma joinretM_tail a (c : C) (f : {hom M a -> c}) : [\c f, join _, ret _] = f.
Proof. by rewrite -assoc joinretM right_id. Qed.
Lemma joinMret_tail a (c : C) (f : {hom M a -> c}) : [\c f, join _, M # ret _] = f.
Proof. by rewrite -assoc joinMret right_id. Qed.
Lemma joinA_tail a (c : C) (f : {hom M (M (M a)) -> c}) :
  [\c f, join _, M # join _] = [\c f, join _, join _].
Proof. by rewrite -assoc joinA assoc. Qed.
End monad_interface.

HB.factory Record Monad_of_ret_join (C : category) (M : C -> C)
           of @Functor C C M := {
  ret : FId ~> M ;
  join : M \o M ~> M ;
  joinretM : JoinLaws.left_unit ret join ;
  joinMret : JoinLaws.right_unit ret join ;
  joinA : JoinLaws.associativity join
}.
HB.builders Context C M of Monad_of_ret_join C M.
Let F := M : {functor _ -> _}.
Let bind (a b : C) (f : {hom a -> M b}) : {hom M a -> M b} := join _ \c (F # f).
Let bindE (a b : C) (f : {hom a -> M b}) :
    bind f = join b \c M # f.
Proof. by []. Qed.
HB.instance Definition _ := isMonad.Build C M bindE joinretM joinMret joinA.
HB.end.


HB.factory Record Monad_of_ret_bind (C : category) (M : C -> C) :=
{
  ret : forall a, {hom a -> M a} ;
  bind : forall (a b : C), {hom a -> M b} -> {hom M a -> M b} ;
  bindfret : BindLaws.left_neutral bind ret ;
  bindret : BindLaws.right_neutral bind ret ;
  bindA : BindLaws.associative bind ;
}.

HB.builders Context C M of Monad_of_ret_bind C M.

Let fmap a b (f : {hom a -> b}) := bind (ret b \c f).
Let fmap_id : FunctorLaws.id fmap.
Proof. by move=> ?; rewrite /fmap right_id bindret. Qed.
Let fmap_o : FunctorLaws.comp fmap.
Proof. by move=> a b c g h; rewrite /fmap bindA !assoc bindfret. Qed.
HB.instance Definition _ := isFunctor.Build _ _ _ fmap_id fmap_o.

Let fmapE a b (f : {hom a -> b}) : M # f = bind (ret b \c f).
Proof. by []. Qed.
Let ret_naturality : naturality FId M ret.
Proof. by move=> A B h; rewrite bindfret. Qed.
HB.instance Definition _ :=
  isNatural.Build _ _ FId M (ret : FId ~~> M) ret_naturality.

Let join : M \o M ~~> M := fun _ => bind [id].
Let join_naturality : naturality (M \o M) M join.
Proof.
move=> a b h.
rewrite /Fhom/= /fmap /join/=.
rewrite -(natural ret)/=.
rewrite !bindA/= !bindfret right_id.
by rewrite assoc bindfret left_id.
Qed.
HB.instance Definition _ := isNatural.Build _ _ _ _ _ join_naturality.

Let bind_fmap a b c (f : {hom a -> b}) (g : {hom b -> M c}) :
  bind g \c (fmap f) = bind (g \c f).
Proof. by rewrite /= bindA assoc bindfret. Qed.
Lemma bindE (a b : C) (f : {hom a -> M b}) : bind f = join b \c M # f.
Proof. by rewrite bind_fmap left_id. Qed.
Lemma joinretM : JoinLaws.left_unit ret join.
Proof. by move=> ?; rewrite /join bindfret. Qed.
Lemma joinMret : JoinLaws.right_unit ret join.
Proof. by move=> ?; rewrite /join/= bind_fmap left_id bindret. Qed.
Lemma joinA : JoinLaws.associativity join.
Proof. by move=> ?; rewrite /join/= bind_fmap left_id bindA right_id. Qed.

HB.instance Definition _ := isMonad.Build C M bindE joinretM joinMret joinA.
HB.end.

Module _Monad_of_adjoint_functors.
Section mixin.
Import comps_notation.
Variables C D : category.
Variables (F : {functor C -> D}) (G : {functor D -> C}).
Variable A : F -| G.
Definition eps := AdjointFunctors.eps A.
Definition eta := AdjointFunctors.eta A.
Definition M := G \o F.
Definition join : M \o M ~~> M := fun a => G # (eps (F a)).
Definition ret : FId ~~> M := fun a => eta a.
Let triL := AdjointFunctors.triL A.
Let triR := AdjointFunctors.triR A.
Lemma naturality_ret : naturality FId M ret.
Proof. by move=> *; rewrite (natural eta). Qed.
HB.instance Definition _ := isNatural.Build C C FId M ret naturality_ret.
Lemma naturality_join : naturality (M \o M) M join.
Proof.
rewrite /join => a b h.
rewrite /M !FCompE -2!(Fhom_comp G); congr (G # _).
exact: (natural eps).
Qed.
HB.instance Definition _ := isNatural.Build C C (M \o M) M join naturality_join.
Let joinE : join = fun a => G # (@eps (F a)).
Proof. by []. Qed.
Let join_associativity' a : join a \c join (M a) = join a \c (M # join a).
Proof.
rewrite joinE -2!(Fhom_comp G).
by congr (G # _); exact: (natural eps).
Qed.
Lemma join_associativity : JoinLaws.associativity join.
Proof. by move=> a; rewrite join_associativity'. Qed.
Lemma join_left_unit : JoinLaws.left_unit ret join.
Proof. by move=> a; rewrite joinE triR. Qed.
Lemma join_right_unit : JoinLaws.right_unit ret join.
Proof.
move=> a; rewrite joinE /M FCompE/= -Fhom_comp -[in RHS]Fhom_id.
congr (G # _).
exact: triL.
Qed.

HB.instance Definition _ := Functor.on M.
HB.instance Definition monad_of_adjoint_mixin :=
  Monad_of_ret_join.Build C M join_left_unit join_right_unit join_associativity.
End mixin.

Section pack.
Variables (C D : category) (F : {functor C -> D}) (G : {functor D -> C}).
Variables (A : F -| G).
Definition pack : monad C := HB.pack_for (monad C) (G \o F) (monad_of_adjoint_mixin A).
End pack.
End _Monad_of_adjoint_functors.
Notation Monad_of_adjoint_functors := _Monad_of_adjoint_functors.pack.

(*
Require hierarchy.

Module BindLaws2.
Section misc_laws_on_Type_monad.
Local Notation CT := (Type : category).

Variable M : {functor CT -> CT}.
Variable bind : forall a b, {hom a -> M b} -> {hom M a -> M b}.
Local Notation "m >>= f" := (bind f m).
Variable ret : forall a, {hom a -> M a}.
Variable add : forall a, M a -> M a -> M a.
Variable zero : forall a, M a.
Definition bind_right_distributive  :=
  forall a b (m : M a) (k1 k2 : a -> M b),
    m >>= (fun x => add (k1 x) (k2 x)) = add (m >>= k1) (m >>= k2).
Definition bind_left_distributive :=
  forall a b (m1 m2 : M a) (k : a -> M b),
    (add m1 m2) >>= k = add (m1 >>= k) (m2 >>= k).
Definition right_zero := forall a b (g : M b), g >>= (fun _ => zero a) = zero a.
Definition left_zero := forall a b g, zero a >>= g = zero b.
Definition left_id := forall a (m : M a), add (zero a) m = m.
Definition right_id := forall a (m : M a), add m (zero a) = m.

Fact associative_Type (x y z : CT)
     (f : {hom x -> M y}) (g : {hom y -> M z}) :
  (fun w => (f w >>= g)) = (bind g \o f).
Proof. by []. Qed.
End misc_laws_on_Type_monad.
End BindLaws2.
*)

