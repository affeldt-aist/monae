(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2020 monae authors, license: LGPL-2.1-or-later               *)
From mathcomp Require Import all_ssreflect.
Require Import imonae_lib.
Require ihierarchy.
From HB Require Import structures.

(******************************************************************************)
(*                  Formalization of basic category theory                    *)
(*                                                                            *)
(* This file provides definitions of category, functor, monad, as well as     *)
(* basic theorems. It comes as a generalization of the first part of          *)
(* ihierarchy.v which is specialized to the category of sets.                 *)
(*                                                                            *)
(*            category == type of categories, a category C is implemented     *)
(*                        with a universe a la Tarski, there is a realizer    *)
(*                        function el that associates to each object A the    *)
(*                        type el A of its elements; this corresponds to the  *)
(*                        definition of concrete categories                   *)
(*          {hom A, B} == the hom-set of morphisms from A to B, where A and B *)
(*                        are objects of a category C                         *)
(*             [hom f] == morphism corresponding to the function f            *)
(*                  CT := [the category of Type]                              *)
(*         FunctorLaws == module that defines the functor laws                *)
(*                  \O == functor composition                                 *)
(*             F ~~> G == forall a, {hom F a ,G a}, which corresponds to a    *)
(*                        natural transformation when it satisfies the        *)
(*                        predicate naturality                                *)
(*                 NId == the identity natural transformation                 *)
(*          [NEq F, G] == natural transformation from F to G where F and G    *)
(*                        are convertible, especially when they are           *)
(*                        compositions, and differ only by associativity or   *)
(*                        insertion of unit functors                          *)
(*                  \v == vertical composition                                *)
(*                  \h == horizontal composition, or Godement product         *)
(*              F -| G == pair of adjoint functors (Module                    *)
(*                        Module AdjointFunctors); see also TriangularLaws.   *)
(*      Module AdjComp == define a pair of adjoint functors by composition of *)
(*                        two pairs of adjoint functors                       *)
(*  JoinLaws, BindLaws == modules that define the monad laws                  *)
(*             isMonad == mixin that defines the monad interface              *)
(*   Monad_of_ret_bind == factory, monad defined by ret and bind              *)
(*   Monad_of_ret_join == factory, monad defined by ret and join              *)
(* Monad_of_adjoint_functors == module that defines a monad by a pair of      *)
(*                        adjoint functors                                    *)
(* Monad_of_category_monad == module, interface to isMonad from ihierarchy.v  *)
(* Monad_of_category_monad.m == turns a monad over the Type category into     *)
(*                        a monad in the sense of isMonad from ihierarchy.v   *)
(******************************************************************************)

Reserved Notation "F ~~> G" (at level 51).

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

(* Our categories are always concrete; morphisms are just functions. *)
HB.mixin Record isCategory (obj : ihierarchy.UU1) := {
  hom : obj -> obj -> ihierarchy.UU0 ;
  id : forall a, hom a a ;
  comp : forall {a b c}, hom a b -> hom b c -> hom a c ;
  left_id : forall a b (f : hom a b), comp (id a) f = f ;
  right_id : forall a b (f : hom a b), comp f (id b) = f ;
  assoc : forall a b c d (f : hom a b) (g : hom b c) (h : hom c d),
      comp f (comp g h) = comp (comp f g) h ;
}.
Arguments isCategory.phant_Build : clear implicits.

#[short(type=category)]
HB.structure Definition Category := {C of isCategory C}.
Arguments id {C} : rename.
Arguments comp {C a b c} : rename.

HB.mixin Record isConcreteCategory (obj : ihierarchy.UU1) of @Category obj := {
  el : obj -> ihierarchy.UU0 ;
  (*inhom : forall a b, (el a -> el b) -> Prop ; *)
  fn : forall {a b : [the category of obj]}, hom a b -> el a -> el b ;
  fn_inj : forall a b, injective (@fn a b) ;
  id_is_idfun : forall a : [the category of obj] , fn (id a) = idfun;
  comp_is_funcomp : forall (a b c : [the category of obj]) (f : hom a b) (g : hom b c),
      fn (comp f g) = fn g \o fn f ;
}.
Arguments isConcreteCategory.phant_Build : clear implicits.
#[short(type=concrete_category)]
HB.structure Definition ConcreteCategory := {C of isConcreteCategory C}.
Arguments id_is_idfun [C] : rename.
Arguments comp_is_funcomp [C] : rename.

(* TODO: use -> in the notation*)
Notation "{ 'hom' U , V }" := (hom U V)
  (at level 0, format "{ 'hom'  U ,  V }") : category_scope.
Notation "{ 'hom' C ; U , V }" := (@hom C U V)
  (only parsing) : category_scope.

Arguments fn [C a b] : rename.

Section hom_interface.
Lemma hom_ext (C : concrete_category) (a b : C) (f g : hom a b) :
  f = g <-> fn f = fn g.
Proof. by split; [move-> | exact: fn_inj]. Qed.
End hom_interface.

(* Notations \c and [\c f , .. , g , h] for hom compositions. *)
Notation "[id]" := (id _).
Notation "g \c f" := (comp f g) (at level 50, format "g  \c  f").
Module comps_notation.
Notation "[ '\o' f , .. , g , h ]" := (f \o .. (g \o h) ..) (at level 0,
  format "[ '[' '\o'  f ,  '/' .. ,  '/' g ,  '/' h ']' ]") : category_scope.
Notation "[ '\c' f , .. , g , h ]" := (f \c .. (g \c h) ..) (at level 0,
  format "[ '[' '\c'  f ,  '/' .. ,  '/' g ,  '/' h ']' ]") : category_scope.
End comps_notation.

(* transportation of hom along equality *)
Section transport_lemmas.
Variable C : category.
Definition transport_dom
  (a a' b : C) (p : a = a') (f : {hom a, b}) : {hom a', b} :=
    eq_rect a (fun x => {hom x, b}) f a' p.
Definition transport_codom
  (a b b' : C) (p : b = b') (f : {hom a, b}) : {hom a , b'} :=
    eq_rect b (fun x => {hom a, x}) f b' p.
Definition transport_hom (a a' b b' : C) (pa : a = a') (pb : b = b')
  (f : {hom a, b}) : {hom a', b'} :=
  eq_rect b (fun y => {hom a', y})
          (eq_rect a (fun x => {hom x, b}) f a' pa)
          b' pb.
Definition hom_of_eq (a b : C) (p : a = b) : {hom a, b} :=
  transport_codom p (id a).
End transport_lemmas.

Section concrete_transport_lemmas.
Variable C : category.
(* F for factorization *)
Lemma transport_domF (a a' b : C) (p : a = a') (f : {hom a, b}) :
  transport_dom p f = f \c hom_of_eq (esym p).
Proof. by subst a'=> /=; rewrite left_id. Qed.

Lemma transport_codomF (a b b' : C) (p : b = b') (f : {hom a, b}) :
  transport_codom p f = hom_of_eq p \c f.
Proof. by subst b'=> /=; rewrite right_id. Qed.
Lemma transport_homF (a a' b b' : C) (pa : a = a') (pb : b = b') (f : {hom a, b}) :
  transport_hom pa pb f = hom_of_eq pb \c f \c hom_of_eq (esym pa).
Proof. by subst a' b'=> //=; rewrite left_id right_id. Qed.
End concrete_transport_lemmas.

Section Type_as_a_category.
(* TODO: rename to Set_as_a_category? *)
Let UUx := ihierarchy.UU0.

HB.instance Definition _ :=
  isCategory.Build
    UUx (fun a b => a -> b) (@idfun) (fun _ _ _ f g => g \o f)
    (fun _ _ _ => erefl)
    (fun _ _ _ => erefl)
    (fun _ _ _ _ _ _ _ => erefl).

HB.instance Definition _ := 
  isConcreteCategory.Build
    UUx (fun x => x) (fun _ _ f => f) (fun a b => @inj_id (a -> b))
    (fun _ => erefl) (fun _ _ _ _ _ => erefl).
End Type_as_a_category.
Notation CT := [the category of ihierarchy.UU0].

Module FunctorLaws.
Section def.
Variable (C D : category).
Variable (F : C -> D) (f : forall a b, {hom a, b} -> {hom F a, F b}).
Definition id := forall a, f (id a) = (id (F a)).
Definition comp := forall a b c (g : {hom b, c}) (h : {hom a, b}),
  f (g \c h) = f g \c f h.
End def.
End FunctorLaws.

HB.mixin Record isFunctor (C D : category) (F : C -> D) := {
  actm : forall a b, {hom a, b} -> {hom F a, F b} ;
  functor_id_hom : FunctorLaws.id actm ;
  functor_o_hom : FunctorLaws.comp actm }.

HB.structure Definition Functor C D := {F of isFunctor C D F}.
(*Notation functor := Functor.type.*)

Definition functor_phant (C D : category) of phant (C -> D) := Functor.type C D.
Arguments actm [C D] F [a b] f: rename.
Notation "F # f" := (actm F f) : category_scope.
Notation "{ 'functor' fCD }" := (functor_phant (Phant fCD))
                                  (format "{ 'functor'  fCD }"): category_scope.

Section functor_lemmas.
Variables (C D : category) (F : {functor C -> D}).

Lemma functor_id a : F # (id a) = [id].
Proof. by rewrite functor_id_hom. Qed.

Lemma functor_o a b c (g : {hom b, c}) (h : {hom a, b}) :
  F # (g \c h) = F # g \c F # h.
Proof. by rewrite functor_o_hom. Qed.

Lemma functor_ext (G : {functor C -> D}) (pm : F =1 G) :
  (forall (A B : C) (f : {hom A, B}),
      transport_hom (pm A) (pm B) (F # f) = G # f) -> F = G.
Proof.
move: pm.
case: F => mf cf; case: G => mg cg /= pm.
move: cf cg.
rewrite /transport_hom.
move: (funext pm) => ppm.
subst mg => -[[ff idf cf]] -[[fg idg cg]] p.
have pp : ff = fg.
  apply funext_dep=> A.
  apply funext_dep=> B.
  apply funext_dep=> f.
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

Section functor_o_head.
Import comps_notation.
Variable C D : category.
Lemma functor_o_head (F : {functor C -> D})
      a b c d (g : {hom b, c}) (h : {hom a, b}) (k : {hom d, F a}) :
  (F # (g \c h)) \c k = [\c F # g, F # h, k].
Proof. by rewrite functor_o_hom assoc. Qed.
End functor_o_head.
Arguments functor_o_head [C D] F [a b c d].

Section functorid.
Variables C : category.
Definition id_f (A B : C) (f : {hom A, B}) := f.
Lemma id_id : FunctorLaws.id id_f. Proof. by []. Qed.
Lemma id_comp : FunctorLaws.comp id_f. Proof. by []. Qed.
Let _id (x : C) := x.
HB.instance Definition _ := isFunctor.Build C C _id id_id id_comp.
Definition FId : {functor C -> C} := [the {functor _ -> _} of _id].
Lemma FIdf (A B : C) (f : {hom A, B}) : FId # f = f.
Proof. by []. Qed.
End functorid.
Arguments FId {C}.

Section functorcomposition.
Variables C0 C1 C2 : category.
Variables (F : {functor C1 -> C2}) (G : {functor C0 -> C1}).

Definition functorcomposition a b := fun h : {hom a, b} => F # (G # h).

Lemma functorcomposition_id : FunctorLaws.id functorcomposition.
Proof. by move=> A; rewrite /functorcomposition 2!functor_id_hom. Qed.

Lemma functorcomposition_comp : FunctorLaws.comp functorcomposition.
Proof.
by move=> a b c g h; rewrite /functorcomposition; rewrite 2!functor_o_hom.
Qed.

HB.instance Definition _ :=
  isFunctor.Build C0 C2 (F \o G) functorcomposition_id functorcomposition_comp.
End functorcomposition.
Notation "F \O G" := ([the {functor _ -> _} of F \o G]) : category_scope.

Section functorcomposition_lemmas.
Lemma FCompE (C0 C1 C2 : category)
      (F : {functor C1 -> C2}) (G : {functor C0 -> C1}) a b (k : {hom a, b}) :
  (F \O G) # k = F # (G # k).
Proof. by []. Qed.

Variables (C0 C1 C2 C3 : category).

Lemma FCompId (F : {functor C0 -> C1}) : F \O FId = F.
Proof. by apply: functor_ext=> *; rewrite FCompE FIdf. Qed.

Lemma FIdComp (F : {functor C0 -> C1}) : FId \O F = F.
Proof. by apply: functor_ext=> *; rewrite FCompE FIdf. Qed.

Lemma FCompA
  (F : {functor C2 -> C3}) (G : {functor C1 -> C2}) (H : {functor C0 -> C1}) :
  (F \O G) \O H = F \O (G \O H).
Proof. apply: functor_ext=> *; by rewrite FCompE. Qed.
End functorcomposition_lemmas.

Notation "F ~~> G" := (forall a, {hom F a ,G a}) : category_scope.
Definition naturality (C D : category) (F G : {functor C -> D}) (f : F ~~> G) :=
  forall a b (h : {hom a, b}), (G # h) \c (f a) = (f b) \c (F # h).
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
Lemma natural_head (phi : F ~> G) a b c (h : {hom a, b}) (f : {hom c, F a}) :
  [\c G # h, phi a, f] = [\c phi b, F # h, f].
Proof. by rewrite -!assoc natural. Qed.

Lemma nattrans_ext (f g : F ~> G) :
  f = g <-> forall a, f a = g a.
Proof.
split=> [ -> // |]; move: f g => [f [[Hf]]] [g [[Hg]]] /= fg''.
have fg' : forall a, f a = g a :> {hom _, _} by move=> a; rewrite fg''.
move: (funext_dep fg') => fg.
by move: Hf Hg; rewrite fg=> Hf Hg; rewrite (proof_irr _ Hf Hg).
Qed.
End natural_transformation_lemmas.
Arguments natural_head [C D F G].

Section id_natural_transformation.
Variables (C D : category) (F : {functor C -> D}).
Definition unnattrans_id := fun (a : C) => id (F a).
Definition natural_id : naturality _ _ unnattrans_id.
Proof. by move=> *; rewrite left_id right_id. Qed.

HB.instance Definition _ :=
  isNatural.Build C D F F unnattrans_id natural_id.
Definition NId : F ~> F := locked [the _ ~> _ of unnattrans_id].
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
Variable (Imor : forall a b (f : {hom a, b}), tc (F # f) = td (G # f)).
Definition f : F ~~> G := fun (c : C) => tc (id (F c)).
Lemma natural : naturality F G f.
Proof.
move=> a b h.
rewrite /f !transport_codomF !left_id.
have -> : (hom_of_eq (Iobj b) \c F # h) = tc (F # h)
  by rewrite transport_codomF.
by rewrite Imor transport_domF /= esymK.
Qed.

HB.instance Definition _ := isNatural.Build C D F G f natural.
Definition n : F ~> G := [the _ ~> _ of f].
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
Proof. by move=> a b h; rewrite -assoc (natural g) assoc (natural f) assoc. Qed.
HB.instance Definition _ := isNatural.Build C D F H
  vcomp natural_vcomp.
Definition VComp : F ~> H := [the F ~> H of vcomp].
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
Proof. by apply nattrans_ext=> a; rewrite VCompE NIdE left_id. Qed.
Lemma VIdComp : NId G \v f = f.
Proof. by apply nattrans_ext=> a; rewrite VCompE NIdE right_id. Qed.
Lemma VCompA : (h \v g) \v f = h \v (g \v f).
Proof. by apply nattrans_ext=> a; rewrite !VCompE !assoc. Qed.
End vcomp_lemmas2.

Section horizontal_composition.
Variables (C D E : category) (F G : {functor C -> D}) (F' G' : {functor D -> E}).
Variables (s : F ~> G) (t : F' ~> G').

Definition hcomp : F' \O F ~~> G' \O G :=
  fun (c : C) => t (G c) \c F' # s c.
Lemma natural_hcomp : naturality (F' \O F) (G' \O G) hcomp.
Proof.
move=> c0 c1 h.
rewrite -[in LHS]assoc (natural t) [in LHS]assoc [in RHS]assoc; congr (_ \c _).
rewrite [in RHS]FCompE.
rewrite -2!(@functor_o D). (* TODO: why must D be explicit? *)
congr (F' # _).
by rewrite natural.
Qed.

HB.instance Definition _ := isNatural.Build C E (F' \O F) (G' \O G)
  hcomp natural_hcomp.

Definition HComp : F' \O F ~> G' \O G := [the _ ~> _ of hcomp].
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
Proof. by rewrite HCompE NIdE functor_id left_id. Qed.
Lemma HIdComp c : (NId G' \h s) c = G' # s c.
Proof. by rewrite HCompE NIdE right_id. Qed.
(* TODO: introduce the application of a functor to a natural transformation? *)

Lemma HCompA c : ((u \h t) \h s) c = (u \h (t \h s)) c.
Proof.  by rewrite !HCompE assoc FCompE -(functor_o F''). Qed.

Lemma HCompA_nat : (u \h t) \h s =
  [NEq G'' \O (G' \O G) , (G'' \O G') \O G]
  \v (u \h (t \h s))
  \v [NEq (F'' \O F') \O F , F'' \O (F' \O F)].
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

Lemma NIdFComp : NId (F' \O F) = (NId F') \h (NId F).
Proof.
by apply nattrans_ext => c /=; rewrite HCompE !NIdE /= right_id functor_id.
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
rewrite !HCompE !VCompE !HCompE !NIdE /= !right_id !functor_id !left_id.
by rewrite !assoc functor_o.
Qed.
End hcomp_lemmas.

(* adjoint functor *)
(* We define adjointness F -| G in terms of its unit and counit. *)

Module TriangularLaws.
Section triangularlaws.
Variables (C D : category) (F : {functor C -> D}) (G : {functor D -> C}).
Variables (eta : FId ~> G \O F) (eps : F \O G ~> FId).
Definition left := forall c, eps (F c) \c F # (eta c) = [id].
Definition right := forall d, G # (eps d) \c eta (G d) = [id].
End triangularlaws.
End TriangularLaws.

Module AdjointFunctors.
Section def.
Variables (C D : category) (F : {functor C -> D}) (G : {functor D -> C}).
Record t := mk {
  eta : FId ~> G \O F ;
  eps : F \O G ~> FId ;
  triL : TriangularLaws.left eta eps ;
  triR : TriangularLaws.right eta eps
}.
End def.
Section lemmas.
Local Notation "F -| G" := (t F G).
Variables (C D : category) (F : {functor C -> D}) (G : {functor D -> C}).
Variable A : F -| G.

Definition hom_iso c d : {hom F c, d} -> {hom c, G d} :=
  fun h => (G # h) \c (eta A c).

Definition hom_inv c d : {hom c, G d} -> {hom F c, d} :=
  fun h => (eps A d) \c (F # h).

Import comps_notation.

Lemma hom_isoK (c : C) (d : D) (f : {hom F c, d}) : hom_inv (hom_iso f) = f.
Proof.
rewrite /hom_inv /hom_iso.
by rewrite functor_o -(natural_head (eps _)) triL FIdf left_id.
Qed.
Lemma hom_invK (c : C) (d : D) (g : {hom c, G d}) : hom_iso (hom_inv g) = g.
Proof.
rewrite /hom_inv /hom_iso.
by rewrite functor_o assoc (natural (eta A)) -assoc triR FIdf right_id.
Qed.

Lemma hom_iso_inj (c : C) (d : D) : injective (@hom_iso c d).
Proof. exact: can_inj (@hom_isoK c d). Qed.
Lemma hom_inv_inj (c : C) (d : D) : injective (@hom_inv c d).
Proof. exact: can_inj (@hom_invK c d). Qed.

Lemma eta_hom_iso (c : C) : eta A c = hom_iso [id].
Proof. by rewrite /hom_iso /= functor_id right_id. Qed.
Lemma eps_hom_inv (d : D) : eps A d = hom_inv [id].
Proof. by rewrite /hom_inv /= functor_id left_id. Qed.

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

(* TODO: extend Functor to LeftAdjointFunctor and RightAdjointFunctor *)
(* TODO: extend Nattrans to AdjUnit and AdjCounit *)
(* Provide rewriting lemmas tri_left/right and tri_left/right_head for units and counits *)

Module AdjComp.
Section def.
Import comps_notation.
Variables C0 C1 C2 : category.
Variables (F0 : {functor C0 -> C1}) (G0 : {functor C1 -> C0}).
Variables (F1 : {functor C1 -> C2}) (G1 : {functor C2 -> C1}).
Variables
  (eta0 : FId ~> G0 \O F0) (eta1 : FId ~> G1 \O F1)
  (eps0 : F0 \O G0 ~> FId) (eps1 : F1 \O G1 ~> FId)
  (triL0 : TriangularLaws.left eta0 eps0)
  (triL1 : TriangularLaws.left eta1 eps1)
  (triR0 : TriangularLaws.right eta0 eps0)
  (triR1 : TriangularLaws.right eta1 eps1).

Definition F := F1 \O F0.
Definition G := G0 \O G1.

Definition Eta : FId ~> G \O F :=
  [NEq G0 \O (G1 \O F1) \O F0 , G \O F]
    \v ((NId G0) \h (eta1) \h (NId F0))
    \v [NEq G0 \O F0 , G0 \O FId \O F0]
    \v (eta0).

Lemma EtaE a : Eta a = G0 # (eta1 (F0 a)) \c (eta0 a).
Proof. by rewrite !VCompE /= left_id right_id HCompId HIdComp. Qed.

Definition Eps : F \O G ~> FId :=
  (eps1)
    \v [NEq F1 \O FId \O G1 , F1 \O G1]
    \v ((NId F1) \h (eps0) \h (NId G1))
    \v [NEq F \O G , (F1 \O (F0 \O G0)) \O G1].
Lemma EpsE a : Eps a = (eps1 _) \c F1 # (eps0 (G1 a)).
Proof. by rewrite !VCompE /= !left_id HCompId HIdComp. Qed.

Lemma triL : TriangularLaws.left Eta Eps.
Proof.
(* NB(tanaka): This proof does NOT follow the manner of 2-category, for now. *)
move=> c.
rewrite EpsE EtaE assoc (functor_o F) /F -(functor_o_head F1).
rewrite -(natural eps0) FIdf /=.
rewrite (functor_o_head F1).
rewrite -assoc (triL1 (F0 c)). (* should be "tri_left_head" *)
rewrite right_id.
by rewrite -functor_o triL0 functor_id.
Qed.

Lemma triR : TriangularLaws.right Eta Eps.
Proof.
move=> c.
rewrite EpsE EtaE.
rewrite (functor_o_head G).
rewrite -(functor_o_head G0 _ (eta1 _)).
rewrite (natural eta1).
rewrite -(functor_o_head G0).
by rewrite -assoc triR1 right_id FIdf triR0.
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
Variables (ret : FId ~~> M) (join : M \O M ~~> M).
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

Variable b : forall A B, M A -> (A -> M B) -> M B.
Local Notation "m >>= f" := (b m f).

This does not work well since it does not keep the {hom _, _} structure
in the result.
*)
Section abscat.
Variables (C : category) (M : {functor C -> C}).
Variable bind : forall a b, {hom a, M b} -> {hom M a, M b}.
Variable ret : forall a, {hom a, M a}.
Definition associative :=
  forall a b c (f : {hom a, M b}) (g : {hom b, M c}),
  bind g \c bind f = bind (bind g \c f).
Definition left_neutral :=
  forall a b (f : {hom a, M b}), (bind f \c ret a) = f.
Definition right_neutral :=
  forall a, bind (ret a) = [id].
End abscat.

Section conccat.
Variables (C : concrete_category) (M : C -> C).
Variable bind : forall a b, {hom a, M b} -> {hom M a, M b}.
Local Notation "m >>= f" := (fn (bind f) m).
Variable ret : forall a, {hom a, M a}.

Definition associative_conc :=
  forall a b c (m : el (M a)) (f : {hom a, M b}) (g : {hom b, M c}),
  (m >>= f) >>= g = m >>= (bind g \c f).
Definition left_neutral_conc :=
  forall a b (f : {hom a, M b}), (bind f \c ret a) = f.
Definition right_neutral_conc :=
  forall a (m : el (M a)), m >>= ret a = m.
End conccat.
End BindLaws.


HB.mixin Record isMonad (C : category) (M : C -> C) of @Functor C C M := {
  ret : FId ~> [the {functor C -> C} of M] ;
  join : [the {functor C -> C} of M] \O [the {functor C -> C} of M] ~>
         [the {functor C -> C} of M] ;
  bind : forall (a b : C), {hom a, M b} -> {hom M a, M b} ;
  bindE : forall (a b : C) (f : {hom a, M b}),
    bind a b f = join b \c [the {functor C -> C} of M] # f ;
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
(* *_head lemmas are for [fun of f] \o ([fun of g] \o ([fun of h] \o ..))*)
Import comps_notation.
Lemma fmap_bindret (a b : C) (f : {hom a, b}) : M # f = bind (ret b \c f).
Proof. by rewrite bindE functor_o -assoc joinMret right_id. Qed.
Lemma joinretM_head a (c : C) (f : {hom c, M a}) : [\c join _, ret _, f] = f.
Proof. by rewrite -assoc joinretM right_id. Qed.
Lemma joinMret_head a (c : C) (f : {hom c, M a}) : [\c join _, M # ret _, f] = f.
Proof. by rewrite -assoc joinMret right_id. Qed.
Lemma joinA_head a (c : C) (f : {hom c, M (M (M a))}) :
  [\c join _, M # join _, f] = [\c join _, join _, f].
Proof. by rewrite -assoc joinA assoc. Qed.
End monad_interface.

HB.factory Record Monad_of_ret_join (C : category) (M : C -> C)
           of @Functor C C M := {
  ret : FId ~> [the {functor C -> C} of M] ;
  join : M \O M ~> [the {functor C -> C} of M] ;
  joinretM : JoinLaws.left_unit ret join ;
  joinMret : JoinLaws.right_unit ret join ;
  joinA : JoinLaws.associativity join
}.
HB.builders Context C M of Monad_of_ret_join C M.
Let F := [the {functor _ -> _} of M].
Let bind (a b : C) (f : {hom a, M b}) : {hom M a, M b} := join _ \c (F # f).
Let bindE (a b : C) (f : {hom a, M b}) :
    bind f = join b \c [the {functor C -> C} of M] # f.
Proof. by []. Qed.
HB.instance Definition _ := isMonad.Build C M bindE joinretM joinMret joinA.
HB.end.

(* Monads defined by ret and bind; M need not be a priori a functor *)
(*
HB.factory Record Monad_of_ret_bind (C : concrete_category) (acto : C -> C)
           of @Functor C C acto := {
  ret' : forall a, {hom a, acto a} ;
  bind : forall (a b : C), {hom a, acto b} -> {hom acto a, acto b} ;
  bindretf : BindLaws.left_neutral_conc bind ret' ;
  bindmret : BindLaws.right_neutral_conc bind ret' ;
  bindA : BindLaws.associative_conc bind ;
}.
HB.builders Context C M of Monad_of_ret_bind C M.
*)
Module _Monad_of_ret_bind.
Section def.
Variables (C : concrete_category) (M : C -> C).
Variables
  (ret' : forall a, {hom a, M a})
  (bind : forall (a b : C), {hom a, M b} -> {hom M a, M b})
  (bindretf : BindLaws.left_neutral_conc bind ret')
  (bindmret : BindLaws.right_neutral_conc bind ret')
  (bindA : BindLaws.associative_conc bind).
Let fmap a b (f : {hom a, b}) := bind (ret' b \c f).
Let fmap_id : FunctorLaws.id fmap.
Proof.
move=> A; apply/hom_ext/funext=>m. rewrite /fmap.
rewrite/idfun/=.
by rewrite -[in RHS](bindmret m) left_id id_is_idfun /=.
Qed.
Let fmap_o : FunctorLaws.comp fmap.
Proof.
move=> a b c g h; apply/hom_ext/funext=>m; rewrite /fmap comp_is_funcomp /=.
rewrite bindA.
congr (fn (bind _)).
by rewrite -[in RHS]assoc bindretf assoc.
Qed.
HB.instance Definition _ := isFunctor.Build _ _ _ fmap_id fmap_o.
Definition F := [the {functor C -> C} of M].
Let ret'_naturality : naturality FId F ret'.
Proof. by move=> A B h; rewrite FIdf bindretf. Qed.
HB.instance Definition _ :=
  isNatural.Build _ _ FId F (ret' : FId ~~> F) ret'_naturality.
Definition ret := [the FId ~> F of ret'].
Let join' : F \O F ~~> F := fun _ => bind [id].
Let join'_naturality : naturality (F \O F) F join'.
Proof.
move => A B h.
apply/fn_inj/funeqP => m.
rewrite /join' 2!comp_is_funcomp /= 2!bindA left_id.
by rewrite -assoc bindretf right_id.
Qed.
HB.instance Definition _ := isNatural.Build _ _ _ _ _ join'_naturality.
Definition join := [the F \O F ~> F of join'].

Let bind_fmap a b c (f : {hom a, b}) (g : {hom b, F c}) :
  bind g \c (fmap f) = bind (g \c f).
Proof.
apply/fn_inj/funeqP => m.
by rewrite comp_is_funcomp /= bindA -assoc bindretf.
Qed.
Lemma bindE (a b : C) (f : {hom a, F b}) :
  bind f = join b \c [the {functor C -> C} of F] # f.
Proof. by rewrite bind_fmap right_id. Qed.
Lemma joinretM : JoinLaws.left_unit ret join.
Proof. by rewrite /join => A; rewrite bindretf. Qed.
Lemma joinMret : JoinLaws.right_unit ret join.
Proof.
move=> a.
rewrite /join /= /join' bind_fmap right_id.
apply/fn_inj/funeqP => m.
by rewrite bindmret id_is_idfun.
Qed.
Lemma joinA : JoinLaws.associativity join.
Proof.
move=> a.
rewrite /join /= /join' bind_fmap right_id.
apply/fn_inj/funeqP => m.
by rewrite comp_is_funcomp /= bindA left_id.
Qed.
Definition build :=
  Monad.Pack
    (Monad.Class
       (isMonad.Axioms_
          (icategory_Functor__to__icategory_isFunctor F)
          ret
          join
          bind
          bindE
          joinretM
          joinMret
          joinA)).
End def.
End _Monad_of_ret_bind.
Notation Monad_of_ret_bind := _Monad_of_ret_bind.build.

(* Trying to turn the above module into a factory, HB.end fails with
Error: No builders to declare, did you forget HB.instance?

HB.factory Record Monad_of_ret_bind (C : concrete_category) (acto : C -> C)
           of @Functor C C acto := {
  ret' : forall a, {hom a, acto a} ;
  bind : forall (a b : C), {hom a, acto b} -> {hom acto a, acto b} ;
  bindretf : BindLaws.left_neutral_conc bind ret' ;
  bindmret : BindLaws.right_neutral_conc bind ret' ;
  bindA : BindLaws.associative_conc bind ;
}.
HB.builders Context C acto of Monad_of_ret_bind C acto.
Let F := @_Monad_of_ret_bind.F C acto ret' bind bindretf bindmret bindA.
Let bindE := @_Monad_of_ret_bind.bindE C acto ret' bind bindretf bindmret bindA.
Let joinretM := @_Monad_of_ret_bind.joinretM C acto ret' bind bindretf bindmret bindA.
Let joinMret := @_Monad_of_ret_bind.joinMret C acto ret' bind bindretf bindmret bindA.
Let joinA := @_Monad_of_ret_bind.joinA C acto ret' bind bindretf bindmret bindA.
HB.instance Definition _ := isMonad.Build C F bindE joinretM joinMret joinA.
HB.end.
*)


Module _Monad_of_adjoint_functors.
Section def.
Import comps_notation.
Variables C D : category.
Variables (F : {functor C -> D}) (G : {functor D -> C}).
Variable A : F -| G.
Definition eps := AdjointFunctors.eps A.
Definition eta := AdjointFunctors.eta A.
Definition M := G \O F.
Definition join : M \O M ~~> M := fun a => G # (eps (F a)).
Definition ret : FId ~~> M := fun a => eta a.
Let triL := AdjointFunctors.triL A.
Let triR := AdjointFunctors.triR A.
Lemma naturality_ret : naturality FId M ret.
Proof. by move=> *; rewrite (natural eta). Qed.
HB.instance Definition _ := isNatural.Build C C FId M ret naturality_ret.
Lemma naturality_join : naturality (M \O M) M join.
Proof.
rewrite /join => a b h.
rewrite /M !FCompE -2!(functor_o G); congr (G # _).
exact: (natural eps).
Qed.
HB.instance Definition _ := isNatural.Build C C (M \O M) M join naturality_join.
Let joinE : join = fun a => G # (@eps (F a)).
Proof. by []. Qed.
Let join_associativity' a : join a \c join (M a) = join a \c (M # join a).
Proof.
rewrite joinE -2!(functor_o G).
by congr (G # _); exact: (natural eps).
Qed.
Lemma join_associativity : JoinLaws.associativity join.
Proof. by move=> a; rewrite join_associativity'. Qed.
Lemma join_left_unit : JoinLaws.left_unit ret join.
Proof. by move=> a; rewrite joinE triR. Qed.
Lemma join_right_unit : JoinLaws.right_unit ret join.
Proof.
move=> a; rewrite joinE. rewrite /M FCompE.
rewrite /= -functor_o -[in RHS]functor_id.
congr (G # _).
exact: triL.
Qed.
(*TODO: make this go through
HB.instance Definition _ :=
 Monad_of_ret_join.Build _ _ join_left_unit join_right_unit join_associativity.*)
Let bind (a b : C) (f : {hom a, M b}) : {hom M a, M b} := join _ \c (M # f).
Let bindE (a b : C) (f : {hom a, M b}) : bind f = join b \c (M # f).
Proof. by []. Qed.

HB.instance Definition monad_of_adjoint_mixin :=
  isMonad.Build C M bindE join_left_unit join_right_unit join_associativity.
(* TODO: eliminate Warning: non forgetful inheritance detected *)

Definition build (C D : category)
           (F : {functor C -> D}) (G : {functor D -> C}) (A : F -| G) :=
  Monad.Pack
    (Monad.Class
       (isMonad.Axioms_ _ _ _ _
                        bindE join_left_unit join_right_unit join_associativity)).
End def.
End _Monad_of_adjoint_functors.
Notation Monad_of_adjoint_functors := _Monad_of_adjoint_functors.build.
(* TODO: Could this be an HB.factory? *)

Module BindLaws2.
Section misc_laws_on_Type_monad.
Variable M : {functor CT -> CT}.
Variable bind : forall a b, {hom a, M b} -> {hom M a, M b}.
Local Notation "m >>= f" := (bind f m).
Variable ret : forall a, {hom a, M a}.
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
     (f : {hom x, M y}) (g : {hom y, M z}) :
  (fun w => (f w >>= g)) = (bind g \o f).
Proof. by []. Qed.
End misc_laws_on_Type_monad.
End BindLaws2.

(* Converter from category.monad to hierarchy.monad *)
Import ihierarchy.

Module Monad_of_category_monad.
Section def.
Variable M : icategory.Monad.Exports.monad CT.

Definition acto (A : UU0) : UU0 := M A.

Definition actm (A B : UU0) (h : A -> B) (x : acto A) : acto B :=
  (M # [the {hom CT; A, B} of h]) x.

Lemma actm_id : FunctorLaws.id actm.
Proof. by move => ?; rewrite /actm icategory.functor_id. Qed.

Lemma actm_comp : FunctorLaws.comp actm.
Proof. by move => *; rewrite {1}/actm icategory.functor_o. Qed.

HB.instance Definition _ := ihierarchy.isFunctor.Build acto actm_id actm_comp.

Let F := [the functor of acto].

Lemma actmE (a b : CT) (h : {hom a, b}) : (F # h)%monae = (M # h)%category.
Proof. by congr (icategory.actm M); apply hom_ext. Qed.

Definition ret_ : forall A, FId%monae A -> F A :=
  fun A (a : A) => @icategory.ret _ M A a.

Definition join_ : forall A, [the functor of F \o F] A -> F A :=
  fun A => @icategory.join _ M A.

Lemma naturality_ret : ihierarchy.naturality _ _ ret_.
Proof.
move => A B h.
rewrite actmE /ret_.
set L := LHS.
change L with (M # h \c icategory.ret A).
by rewrite icategory.natural.
Qed.

HB.instance Definition _ := ihierarchy.isNatural.Build _ _ ret_ naturality_ret.

Definition ret : (FId ~> F)%monae := [the nattrans _ _ of ret_].

Lemma naturality_join : ihierarchy.naturality [the functor of F \o F] F join_.
Proof.
move=> a b h; rewrite (_ : h = [the {hom a, b} of h])//.
rewrite /join_ actmE.
set L := LHS.
change L with (M # h \c icategory.join a).
by rewrite icategory.natural.
Qed.

HB.instance Definition _ := ihierarchy.isNatural.Build _ _ join_ naturality_join.

Definition join := [the nattrans _ _ of join_].

Lemma retE a : ret a = icategory.ret a. Proof. by []. Qed.

Lemma joinE a : join a = icategory.join a. Proof. by []. Qed.

Lemma joinretM : ihierarchy.JoinLaws.left_unit ret join.
Proof.
move=> a.
rewrite joinE retE /=.
set L := LHS.
change L with (icategory.join a \c icategory.ret (F a)).
by rewrite icategory.joinretM.
Qed.

Lemma joinMret : ihierarchy.JoinLaws.right_unit ret join.
Proof.
move=> a; rewrite joinE retE.
set L := LHS.
change L with (icategory.join a \c (F # icategory.ret a)).
by rewrite icategory.joinMret.
Qed.

Lemma joinA : ihierarchy.JoinLaws.associativity join.
Proof.
move=> a; rewrite joinE actmE.
set X := (X in X \o _).
set Y := (Y in _ \o Y).
change (X \o Y) with (X \c Y).
by rewrite icategory.joinA.
Qed.

HB.instance Definition _ := ihierarchy.isMonad_ret_join.Build acto 
  joinretM joinMret joinA.
End def.
End Monad_of_category_monad.
HB.export Monad_of_category_monad.
