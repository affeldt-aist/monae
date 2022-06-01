(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2020 monae authors, license: LGPL-2.1-or-later               *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import boolp.
Require Import monae_lib.
From HB Require Import structures.

(******************************************************************************)
(*                  Formalization of basic category theory                    *)
(*                                                                            *)
(* This file provides definitions of category, functor, monad, as well as     *)
(* basic theorems. It comes as a generalization of the first part of          *)
(* hierarchy.v which is specialized to the category of sets.                  *)
(*                                                                            *)
(*            category == type of categories, a category C is implemented     *)
(*                        with a universe a la Tarski, there is a realizer    *)
(*                        function el that associates to each object A the    *)
(*                        type el A of its elements; this corresponds to the  *)
(*                        definition of concrete categories                   *)
(*          {hom A, B} == the hom-set of morphisms from A to B, where A and B *)
(*                        are objects of a category C                         *)
(*             [hom f] == morphism corresponding to the function f            *)
(* Section Type_as_a_category == the first instance of a category: Type       *)
(*       Type_category == the category corresponding to the Coq type Type     *)
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
(* Monad_of_category_monad == module, interface to isMonad from hierarchy.v   *)
(* Monad_of_category_monad.m == turns a monad over the Type category into     *)
(*                        a monad in the sense of isMonad from hierarchy.v    *)
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
HB.mixin Record isCategory (obj : Type) := {
  el : obj -> Type ;
  inhom : forall a b, (el a -> el b) -> Prop ;
  idfun_inhom : forall a, @inhom a a idfun ;
  funcomp_inhom : forall a b c (f : el a -> el b) (g : el b -> el c),
      inhom _ _ f -> inhom _ _ g -> inhom _ _ (g \o f)
}.
Arguments isCategory.phant_Build : clear implicits.
#[short(type=category)]
HB.structure Definition Category := {C of isCategory C}.
Arguments idfun_inhom [C] : rename.
Arguments funcomp_inhom [C a b c f g] : rename.


HB.mixin Record isHom (C : category) (a b : C) (f : el a -> el b) := {
  isHom_inhom : inhom a b f
}.
HB.structure Definition Hom (C : category) (a b : C) :=
  {f of isHom C a b f}.
Arguments isHom_inhom [C a b].
(*Notation hom := Hom.type.*)
(* TODO: use -> in the notation*)
Notation "{ 'hom' U , V }" := (Hom.type U V)
  (at level 0, format "{ 'hom'  U ,  V }") : category_scope.
Notation "{ 'hom' C ; U , V }" := (@Hom.type C U V)
  (only parsing) : category_scope.
(*(at level 0, format "{ 'hom'  C ;  U ,  V }", only parsing) : category_scope.*)
Notation "[ 'hom' f ]" := [the {hom _ , _} of f]
  (at level 0, format "[ 'hom'  f ]") : category_scope.
(* TODO: FIX: At some places, this [hom f] notation is not used for printing and
   [the {hom ...} of f] is undesirably printed instead. *)

Definition HomPack (C : category) (a b : C) (f : el a -> el b)
           (Hf : inhom a b f) :=
  Hom.Pack (@Hom.Class C a b f (isHom.Axioms_ a b f Hf)).
Arguments HomPack [C].

Lemma hom_ext (C : category) (a b : C) (f g : {hom a, b}) : f = g <-> f = g :> (_ -> _).
Proof.
move: f g => [f [[Hf]]] [g [[Hg]]] /=; split => [[]//|fg /=].
move: Hf Hg; rewrite fg=> Hf Hg.
by rewrite (boolp.Prop_irrelevance Hf Hg).
Qed.

Section hom_interface.
Variable C : category.
Implicit Types a b c : C.

HB.instance Definition _ c :=
  isHom.Build _ _ _ (@idfun (el c)) (idfun_inhom c).

HB.instance Definition _ (a b c : C) (f : {hom b, c}) (g : {hom a, b}):=
  isHom.Build _ _ _ (f \o g) (funcomp_inhom (isHom_inhom g) (isHom_inhom f)).
End hom_interface.

(* Notation [\o f , .. , g , h] for hom compositions. *)
Module comps_notation.
Notation "[ '\o' f , .. , g , h ]" := (f \o .. (g \o h) ..) (at level 0,
  format "[ '[' '\o'  f ,  '/' .. ,  '/' g ,  '/' h ']' ]") : category_scope.
End comps_notation.

Section category_lemmas.
Variable C : category.

Lemma homfunK (a b : C) (f : {hom a, b}) : [hom f] = f.
Proof. by []. Qed.

Lemma homcompA (a b c d : C) (h : {hom c, d}) (g : {hom b, c}) (f : {hom a, b}) :
  [hom [hom h \o g] \o f] = [hom h \o [hom g \o f]].
Proof. by move: f g h => [? ?] [? ?] [? ?]; apply hom_ext. Qed.

Lemma homcompE (a b c : C) (g : {hom b, c}) (f : {hom a, b}) :
  [hom g \o f] = g \o f :> (el a -> el c).
Proof. by []. Qed.

Lemma hom_compE (a b c : C) (g : {hom b, c}) (f : {hom a, b}) x :
  g (f x) = (g \o f) x.
Proof. exact: compE. Qed.

Import comps_notation.

(* Restricting the components of a composition to homs and using the lemma
   homcompA, we can avoid the infinite sequence of redundunt compositions
   "_ \o id" or "id \o _" that pops out when we "rewrite !compA".*)
Lemma hom_compA (a b c d : C) (h : {hom c, d}) (g : {hom b, c}) (f : {hom a, b}) :
  (h \o g) \o f = [\o h, g, f] :> (el a -> el d).
Proof. exact: compA. Qed.

Example hom_compA' (a b c d : C) (h : {hom c, d}) (g : {hom b, c}) (f : {hom a, b}) :
  (h \o g) \o f = [\o h, g, f].
Proof.
rewrite 10!compA.
Undo 1.
by rewrite !hom_compA.
(* rewrite !homcompA blocks id's from coming in, thanks to {hom _,_} conditions on arguments. *)
Abort.

(* Tactic support is desirable for the following two cases :
   1. rewriting at the head of the sequence;
      compare for example the lemmas natural and natural_head below
   2. rewriting under [hom _];
      dependent type errors and explicit application of hom_ext is tedious.
*)

End category_lemmas.

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
  transport_codom p [hom idfun].
(* (* this works too; not sure which is better *)
Definition hom_of_eq (a b : C) (p : a = b) : {hom a, b} :=
  transport_codom p [hom idfun].
*)

(* F for factorization *)
Lemma transport_domF (a a' b : C) (p : a = a') (f : {hom a, b}) :
  transport_dom p f = [hom f \o hom_of_eq (esym p)].
Proof. apply hom_ext; by subst a'. Qed.
Lemma transport_codomF (a b b' : C) (p : b = b') (f : {hom a, b}) :
  transport_codom p f = [hom hom_of_eq p \o f].
Proof. apply hom_ext; by subst b'. Qed.
Lemma transport_homF (a a' b b' : C) (pa : a = a') (pb : b = b') (f : {hom a, b}) :
  transport_hom pa pb f = [hom hom_of_eq pb \o f \o hom_of_eq (esym pa)].
Proof. apply hom_ext; by subst a' b'. Qed.
End transport_lemmas.

Section Type_as_a_category.
(* TODO: consider using universe polymorphism *)
Let UUx := Type.
HB.instance Definition _ :=
  isCategory.Build UUx (fun x : Type => x)
    (fun _ _ _ => True) (fun=> I) (fun _ _ _ _ _ _ _ => I).
Definition hom_Type (a b : [the category of UUx]) (f : a -> b) : {hom a, b} :=
  HomPack a b f I.
End Type_as_a_category.

Notation CT := [the category of Type].

Module FunctorLaws.
Section def.
Variable (C D : category).
Variable (F : C -> D) (f : forall a b, {hom a, b} -> {hom F a, F b}).
Definition id := forall a, f [hom idfun] = [hom idfun] :> {hom F a, F a}.
Definition comp := forall a b c (g : {hom b, c}) (h : {hom a, b}),
  f [hom g \o h] = [hom f g \o f h].
End def.
End FunctorLaws.

HB.mixin Record isFunctor (C D : category) (F : C -> D) := {
  actm : forall a b, {hom a, b} -> {hom F a, F b} ;
  functor_id_hom : FunctorLaws.id actm ;
  functor_o_hom : FunctorLaws.comp actm }.
HB.structure Definition Functor C D := {F of isFunctor C D F}.
(*Notation functor := Functor.type.*)
Definition functor_phant (C D : category) (_ : phant (C -> D)) := Functor.type C D.
Arguments actm [C D] F [a b] f: rename.
Notation "F # f" := (actm F f) : category_scope.
Notation "{ 'functor' fCD }" := (functor_phant (Phant fCD))
  (format "{ 'functor'  fCD }") : category_scope.
Definition FunctorPack (C D : category) (F : C -> D)
           (actm : forall a b, {hom a, b} -> {hom F a, F b})
           (fid : FunctorLaws.id actm) (fcomp : FunctorLaws.comp actm)
  : {functor C -> D} :=
  Functor.Pack (Functor.Class (isFunctor.Axioms_ _ _ _ fid fcomp)).

Section functor_lemmas.
Variables (C D : category) (F : {functor C -> D}).
Lemma functor_id a : F # [hom idfun] = idfun :> (el (F a) -> el (F a)).
Proof. by rewrite functor_id_hom. Qed.
Lemma functor_o a b c (g : {hom b, c}) (h : {hom a, b}) :
  F # [hom g \o h] = F # g \o F # h :> (el (F a) -> el (F c)).
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

Section functor_o_head.
Import comps_notation.
Variable C D : category.
Lemma functor_o_head a b c (g : {hom b, c}) (h : {hom a, b}) d (F : {functor C -> D})
    (k : {hom d, F a}) :
  (F # [hom g \o h]) \o k = [\o F # g, F # h, k].
Proof. by rewrite functor_o_hom. Qed.
End functor_o_head.
Arguments functor_o_head [C D a b c g h d] F.

Section functorid.
Variables C : category.
Definition id_f (A B : C) (f : {hom A, B}) := f.
Lemma id_id : FunctorLaws.id id_f. Proof. by []. Qed.
Lemma id_comp : FunctorLaws.comp id_f. Proof. by []. Qed.
HB.instance Definition _ := isFunctor.Build _ _ idfun id_id id_comp.
Definition FId : {functor C -> C} := [the {functor _ -> _} of idfun].
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
  forall a b (h : {hom a, b}), (G # h) \o (f a) = (f b) \o (F # h).
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
Definition NattransPack (C D : category) (F G : {functor C -> D}) (f : F ~~> G)
           (Hf : naturality F G f) :=
  Nattrans.Pack (Nattrans.Class (@isNatural.Axioms_ C D F G f Hf)).

Section natural_transformation_lemmas.
Import comps_notation.
Variables (C D : category) (F G : {functor C -> D}).
Lemma natural_head (phi : F ~> G) a b c (h : {hom a, b}) (f : {hom c, F a}) :
  [\o G # h, phi a, f] = [\o phi b, F # h, f].
Proof. by rewrite -!hom_compA natural. Qed.

Lemma nattrans_ext (f g : F ~> G) :
  f = g <-> forall a, (f a = g a :> (_ -> _)).
Proof.
split=> [ -> // |]; move: f g => [f [[Hf]]] [g [[Hg]]] /= fg''.
have fg' : forall a, f a = g a :> {hom _, _} by move=> a; rewrite hom_ext fg''.
move: (functional_extensionality_dep fg') => fg.
by move: Hf Hg; rewrite fg=> Hf Hg; rewrite (proof_irr _ Hf Hg).
Qed.
End natural_transformation_lemmas.
Arguments natural_head [C D F G].

Section id_natural_transformation.
Variables (C D : category) (F : {functor C -> D}).
Definition unnattrans_id := fun (a : C) => [hom (@idfun (el (F a)))].
Definition natural_id : naturality _ _ unnattrans_id.
Proof. by []. Qed.

HB.instance Definition _ :=
  isNatural.Build C D F F unnattrans_id natural_id.
Definition NId : F ~> F := NattransPack natural_id.
Lemma NIdE : NId  = (fun a => [hom idfun]) :> (_ ~~> _).
Proof. by []. Qed.
End id_natural_transformation.

Module NEq.
Section def.
Import comps_notation.
Variables (C D : category) (F G : {functor C -> D}).
Variable (Iobj : forall c, F c = G c).
Local Notation tc := (transport_codom (Iobj _)).
Local Notation td := (transport_dom (esym (Iobj _))).
Variable (Imor : forall a b (f : {hom a, b}), tc (F # f) = td (G # f)).
Definition f : F ~~> G := fun (c : C) => tc [hom idfun].
Lemma natural : naturality F G f.
Proof.
move=> a b h.
rewrite /f !transport_codomF 2!homcompE 2!compfid.
have /hom_ext -> : [hom (hom_of_eq (Iobj b) \o F # h)] = [hom tc (F # h)]
  by rewrite transport_codomF.
by rewrite Imor transport_domF homfunK /= esymK.
Qed.
Definition n : F ~> G := NattransPack natural.
End def.
Module Exports.
Arguments n [C D] : simpl never.
Notation NEq := n.
Lemma NEqE C D F G Iobj Imor :
  @NEq C D F G Iobj Imor =
  (fun a => transport_codom (Iobj _) [hom idfun]) :> (_ ~~> _).
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
Definition ntcomp := fun a => [hom g a \o f a].
Definition natural_vcomp : naturality _ _ ntcomp.
Proof. by move=> A B h; rewrite compA (natural g) -compA (natural f). Qed.
Definition VComp : F ~> H := NattransPack natural_vcomp.
End vertical_composition.
Notation "f \v g" := (VComp f g).

Section vcomp_lemmas.
Variables (C D : category) (F G H I : {functor C -> D}).
Variables (h : H ~> I) (g : G ~> H) (f : F ~> G).
Lemma VCompId : f \v NId F = f.
Proof. by apply nattrans_ext. Qed.
Lemma VIdComp : NId G \v f = f.
Proof. by apply nattrans_ext. Qed.
Lemma VCompA : (h \v g) \v f = h \v (g \v f).
Proof. by apply nattrans_ext. Qed.
Lemma VCompE_nat : g \v f = (fun a => [hom g a \o f a]) :> (_ ~~> _).
Proof. by []. Qed.
Lemma VCompE a : (g \v f) a = g a \o f a :> (_ -> _).
Proof. by []. Qed.
End vcomp_lemmas.

Section horizontal_composition.
Variables (C D E : category) (F G : {functor C -> D}) (F' G' : {functor D -> E}).
Variables (s : F ~> G) (t : F' ~> G').

Lemma natural_hcomp :
  naturality (F' \O F) (G' \O G) (fun c => [hom t (G c) \o F' # s c]).
Proof.
move=> c0 c1 h.
rewrite [in LHS]compA (natural t) -[in LHS]compA -[in RHS]compA; congr (_ \o _).
rewrite [in RHS]FCompE -2!functor_o; congr (F' # _); apply hom_ext => /=.
by rewrite (natural s).
Qed.

Definition HComp : (F' \O F) ~> (G' \O G) := NattransPack natural_hcomp.
End horizontal_composition.
Notation "f \h g" := (locked (HComp g f)).

Section hcomp_extensionality_lemmas.
Variables (C D E : category) (F G : {functor C -> D}) (F' G' : {functor D -> E}).
Variables (s : F ~> G) (t : F' ~> G').
Lemma HCompE_def : t \h s = HComp s t. Proof. by unlock. Qed.
Lemma HCompE c : (t \h s) c = t (G c) \o F' # s c :> (_ -> _).
Proof. by unlock. Qed.
Lemma HCompE_alt c : (t \h s) c = G' # (s c) \o t (F c) :> (_ -> _).
Proof. by rewrite HCompE natural. Qed.
End hcomp_extensionality_lemmas.

Section hcomp_id_assoc_lemmas.
Import comps_notation.
Variables C D E Z : category.
Variables (F G : {functor C -> D}) (F' G' : {functor D -> E}) (F'' G'' : {functor E -> Z}).
Variables (s : F ~> G) (t : F' ~> G') (u : F'' ~> G'').

Lemma HCompId c : (t \h NId F) c = t (F c).
Proof. by rewrite hom_ext HCompE NIdE functor_id compfid. Qed.
Lemma HIdComp c : (NId G' \h s) c = G' # s c.
Proof. by rewrite hom_ext HCompE NIdE compidf. Qed.
(* TODO: introduce the application of a functor to a natural transformation? *)

Let HCompA_def : (u \h t) \h s =
  [NEq G'' \O (G' \O G) , (G'' \O G') \O G]
  \v (u \h (t \h s))
  \v [NEq (F'' \O F') \O F , F'' \O (F' \O F)].
Proof.
apply nattrans_ext => c /=.
rewrite compidf compfid [in LHS]HCompE [in RHS]HCompE.
rewrite [in LHS]HCompE hom_compA -functor_o; congr [\o _, _].
by congr (_ # _); apply hom_ext; rewrite HCompE.
Qed.
Lemma HCompA c : ((u \h t) \h s) c = (u \h (t \h s)) c.
Proof. by rewrite hom_ext HCompA_def. Qed.

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

Lemma NIdFId c : NId (@FId C) c = [hom idfun].
Proof. by []. Qed.

Lemma NIdFComp : NId (F' \O F) = (NId F') \h (NId F).
Proof. by apply nattrans_ext => c /=; rewrite HCompE /= compidf functor_id. Qed.

(* horizontal and vertical compositions interchange *)
Variables (H : {functor C -> D}) (H' : {functor D -> E}).
Variables (s' : G ~> H) (t' : G' ~> H').
Lemma HCompACA : (t' \h s') \v (t \h s) = (t' \v t) \h (s' \v s).
Proof.
apply nattrans_ext => c /=.
rewrite !HCompE !VCompE -compA -[in RHS]compA; congr (_ \o _).
by rewrite natural_head -functor_o.
Qed.
End hcomp_lemmas.

(* adjoint functor *)
(* We define adjointness F -| G in terms of its unit and counit. *)

Module TriangularLaws.
Section triangularlaws.
Variables (C D : category) (F : {functor C -> D}) (G : {functor D -> C}).
Variables (eta : FId ~> G \O F) (eps : F \O G ~> FId).
Definition left := forall c, eps (F c) \o F # (eta c) = idfun.
Definition right := forall d, G # (eps d) \o eta (G d) = idfun.
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
  fun h => [hom (G # h) \o (eta A c)].

Definition hom_inv c d : {hom c, G d} -> {hom F c, d} :=
  fun h => [hom (eps A d) \o (F # h)].

Import comps_notation.

Lemma hom_isoK (c : C) (d : D) (f : {hom F c, d}) : hom_inv (hom_iso f) = f.
Proof.
rewrite /hom_inv /hom_iso; apply hom_ext => /=.
by rewrite functor_o -(natural_head (eps _)) triL.
Qed.
Lemma hom_invK (c : C) (d : D) (g : {hom c, G d}) : hom_iso (hom_inv g) = g.
Proof.
rewrite /hom_inv /hom_iso; apply hom_ext => /=.
by rewrite functor_o hom_compA (natural (eta A)) -hom_compA triR.
Qed.

Lemma hom_iso_inj (c : C) (d : D) : injective (@hom_iso c d).
Proof. exact: can_inj (@hom_isoK c d). Qed.
Lemma hom_inv_inj (c : C) (d : D) : injective (@hom_inv c d).
Proof. exact: can_inj (@hom_invK c d). Qed.

Lemma eta_hom_iso (c : C) : eta A c = hom_iso [hom idfun].
Proof. by apply hom_ext; rewrite /hom_iso /= functor_id. Qed.
Lemma eps_hom_inv (d : D) : eps A d = hom_inv [hom idfun].
Proof. by apply hom_ext; rewrite /hom_inv /= functor_id compfid. Qed.

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
Lemma EtaE a : Eta a = G0 # (eta1 (F0 a)) \o (eta0 a) :> (_ -> _).
Proof. by cbn; rewrite HCompId HIdComp. Qed.
Lemma EtaE_hom a : Eta a = [hom G0 # (eta1 (F0 a)) \o (eta0 a)].
Proof. by rewrite hom_ext EtaE. Qed.

Definition Eps : F \O G ~> FId :=
  (eps1)
    \v [NEq F1 \O FId \O G1 , F1 \O G1]
    \v ((NId F1) \h (eps0) \h (NId G1))
    \v [NEq F \O G , (F1 \O (F0 \O G0)) \O G1].
Lemma EpsE a : Eps a = (eps1 _) \o F1 # (eps0 (G1 a)) :> (_ -> _).
Proof. by cbn; rewrite HCompId HIdComp. Qed.
Lemma EpsE_hom a : Eps a = [hom (eps1 _) \o F1 # (eps0 (G1 a))].
Proof. by rewrite hom_ext EpsE. Qed.

Lemma triL : TriangularLaws.left Eta Eps.
Proof.
(* NB(tanaka): This proof does NOT follow the manner of 2-category, for now. *)
move=> c; rewrite EpsE EtaE_hom hom_compA (functor_o F) /F -(functor_o_head F1).
set X := [hom [\o _, _]].
evar (TY : Type).
evar (Y : TY).
have-> : F1 # X = F1 # Y
  by congr (F1 # _); rewrite hom_ext /X /= -(natural eps0); exact: erefl.
rewrite (functor_o_head F1) FIdf.
rewrite -!hom_compA triL1 compidf.
rewrite -[in RHS](functor_id F1) -(functor_o F1); congr (F1 # _).
by rewrite hom_ext /= triL0.
Qed.

Lemma triR : TriangularLaws.right Eta Eps.
Proof.
move=> c.
rewrite EpsE_hom EtaE (functor_o_head G) -(functor_o_head G0 (eta0 _)).
(* FRAGILE!
   simpl here breaks the notation and renders the following set X impossible *)
set X:= [hom [\o _, _]].
evar (TY : Type).
evar (Y : TY).
have-> : G0 # X = G0 # Y
  by congr (G0 # _); rewrite hom_ext /X /= (natural eta1); exact: erefl.
rewrite (functor_o G0) hom_compA FIdf triR0 compfid.
rewrite -[in RHS](functor_id G0) -(functor_o G0); congr (G0 # _).
by rewrite hom_ext /= triR1.
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
  forall a, join a \o ret (M a) = idfun :> (el (M a) -> el (M a)).
Definition right_unit :=
  forall a, join a \o M # ret a = idfun :> (el (M a) -> el (M a)).
Definition associativity :=
  forall a, join a \o M # join a = join a \o join (M a) :> (el (M (M (M a))) -> el (M a)).
End join_laws.
End JoinLaws.

Module BindLaws.
Section bindlaws.
Variables (C : category) (M : C -> C).
Variable b : forall A B, {hom A, M B} -> {hom M A, M B}.
Local Notation "m >>= f" := (b f m).
(*
bind is usually typed in the literature as follows:

Variable b : forall A B, M A -> (A -> M B) -> M B.
Local Notation "m >>= f" := (b m f).

This does not work well since it does not keep the {hom _, _} structure
in the result.
*)
Fact associative_aux x y z (f : {hom x, M y}) (g : {hom y, M z}) :
  (fun w => (f w >>= g)) = (b g \o f).
Proof. by []. Qed.
Definition associative := forall A B C (m : el (M A)) (f : {hom A, M B}) (g : {hom B, M C}),
  (m >>= f) >>= g = m >>= [hom b g \o f].
Definition left_neutral (r : forall A, {hom A, M A}) :=
  forall A B (f : {hom A, M B}), [hom (b f \o r A)] = f.
Definition right_neutral (r : forall A, {hom A, M A}) :=
  forall A (m : el (M A)), m >>= r _ = m.
End bindlaws.

(* TODO: This section is not properly named. *)
Section bindlaws_on_Type.
Variable M : {functor CT -> CT}.
Variable b : forall A B, (A -> M B) -> M A -> M B.
Local Notation "m >>= f" := (b f m).
Definition bind_right_distributive (add : forall B, M B -> M B -> M B) :=
  forall A B (m : M A) (k1 k2 : A -> M B),
    m >>= (fun x => add _ (k1 x) (k2 x)) = add _ (m >>= k1) (m >>= k2).
Definition bind_left_distributive (add : forall B, M B -> M B -> M B) :=
  forall A B (m1 m2 : M A) (k : A -> M B),
    (add _ m1 m2) >>= k = add _ (m1 >>= k) (m2 >>= k).
Definition right_zero (f : forall A, M A) :=
  forall A B (g : M B), g >>= (fun _ => f A) = f A.
Definition left_zero (f : forall A, M A) := forall A B g, f A >>= g = f B.
Definition left_id (r : forall A, M A) (add : forall B, M B -> M B -> M B) :=
  forall A (m : M A), add _ (r _) m = m.
Definition right_id (r : forall A, M A) (add : forall B, M B -> M B -> M B) :=
  forall A (m : M A), add _ m (r _) = m.
End bindlaws_on_Type.
End BindLaws.

Section bind_lemmas.
Variables (C : category) (M : C -> C).
Variable b : forall A B, {hom A, M B} -> {hom M A, M B}.
Local Notation "m >>= f" := (b f m).
Lemma bind_left_neutral_hom_fun (r : forall A, {hom A, M A})
  : BindLaws.left_neutral b r
    <-> forall A B (f : {hom A, M B}), b f \o r A = f.
Proof. by split; move=> H A B f; move: (H A B f); move/hom_ext. Qed.
End bind_lemmas.


(** * Monad *)
(*
The following definition of the structure fails with:
Error: HB: coercion not to Sortclass or Funclass not supported yet.

HB.mixin Record isMonad (C : category) (M : {functor C -> C}) := {
  ret : FId ~> M ;
  join : M \O M ~> M ;
  bind : forall (a b : C), {hom a, M b} -> {hom M a, M b} ;
  fmapE : forall (a b : C) (f : {hom a, b}) (m : el (M a)),
    (M # f) m = bind a b [hom ret b \o f] m ;
  bindE : forall (a b : C) (f : {hom a, M b}) (m : el (M a)),
    bind a b f m = join b ((M # f) m) ;
  joinretM : JoinLaws.left_unit ret join ;
  joinMret : JoinLaws.right_unit ret join ;
  joinA : JoinLaws.associativity join
}.
HB.structure Definition Monad (C : category) := {M of isMonad C M}.
*)

HB.mixin Record isMonad (C : category) (M : C -> C) of @Functor C C M := {
  ret : FId ~> [the {functor C -> C} of M] ;
  join : [the {functor C -> C} of M] \O [the {functor C -> C} of M] ~>
         [the {functor C -> C} of M] ;
  bind : forall (a b : C), {hom a, M b} -> {hom M a, M b} ;
  bindE : forall (a b : C) (f : {hom a, M b}) (m : el (M a)),
    bind a b f m = join b (([the {functor C -> C} of M] # f) m) ;
  joinretM : JoinLaws.left_unit ret join ;
  joinMret : JoinLaws.right_unit ret join ;
  joinA : JoinLaws.associativity join
}.
#[short(type=monad)]
HB.structure Definition Monad (C : category) :=
  {M of isMonad C M & isFunctor C C M}.
Arguments bind {C M a b} : rename, simpl never.
Notation "m >>= f" := (bind f m).

Section monad_interface.
Variable (C : category) (M : monad C).
(* *_head lemmas are for [fun of f] \o ([fun of g] \o ([fun of h] \o ..))*)
Import comps_notation.
Lemma joinretM_head a (c : C) (f : {hom c, M a}) : [\o join _, ret _, f] = f.
Proof. by rewrite compA joinretM. Qed.
Lemma joinMret_head a (c : C) (f : {hom c, M a}) : [\o join _, M # ret _, f] = f.
Proof. by rewrite compA joinMret. Qed.
Lemma joinA_head a (c : C) (f : {hom c, M (M (M a))}) :
  [\o join _, M # join _, f] = [\o join _, join _, f].
Proof. by rewrite compA joinA. Qed.
End monad_interface.

HB.factory Record Monad_of_ret_join (C : category) (M : C -> C)
           of @Functor C C M := {
  ret : FId ~> [the {functor C -> C} of M] ;
  join : [the {functor C -> C} of M] \O [the {functor C -> C} of M] ~> [the {functor C -> C} of M] ;
  joinretM : JoinLaws.left_unit ret join ;
  joinMret : JoinLaws.right_unit ret join ;
  joinA : JoinLaws.associativity join
}.
HB.builders Context C M of Monad_of_ret_join C M.
Let F := [the {functor _ -> _} of M].
Let bind (a b : C) (f : {hom a, M b}) : {hom M a, M b} := [hom join _ \o (F # f)].
Let bindE (a b : C) (f : {hom a, M b}) (m : el (M a)) :
    bind f m = join b (([the {functor C -> C} of M] # f) m).
Proof. by []. Qed.
HB.instance Definition _ := isMonad.Build C M bindE joinretM joinMret joinA.
HB.end.

(* Monads defined by ret and bind; M need not be a priori a functor *)
HB.factory Record Monad_of_ret_bind (C : category) (acto : C -> C) := {
  ret' : forall a, {hom a, acto a} ;
  bind : forall (a b : C), {hom a, acto b} -> {hom acto a, acto b} ;
  bindretf : BindLaws.left_neutral bind ret' ;
  bindmret : BindLaws.right_neutral bind ret' ;
  bindA : BindLaws.associative bind ;
}.
HB.builders Context C M of Monad_of_ret_bind C M.
Let fmap a b  (f : {hom a, b}) := bind [hom ret' b \o f].
Let bindretf_fun : (forall (a b : C) (f : {hom a, M b}),
  bind f \o ret' a = f).
Proof. by apply/bind_left_neutral_hom_fun/bindretf. Qed.
Let fmap_id : FunctorLaws.id fmap.
Proof.
move=> A; apply/hom_ext/funext=>m. rewrite /fmap.
rewrite/idfun/=.
rewrite -[in RHS](bindmret m).
congr (fun f => bind f m).
by rewrite hom_ext.
Qed.
Let fmap_o : FunctorLaws.comp fmap.
Proof.
move=> a b c g h; apply/hom_ext/funext=>m; rewrite /fmap/=.
rewrite bindA/=.
congr (fun f => bind f m); rewrite hom_ext/=.
by rewrite -[in RHS]hom_compA bindretf_fun.
Qed.
HB.instance Definition _ := isFunctor.Build _ _ _ fmap_id fmap_o.
Notation F := [the {functor _ -> _} of M].
Let ret'_naturality : naturality FId F ret'.
Proof. by move=> A B h; rewrite FIdf bindretf_fun. Qed.
(*HB.instance Definition _ := isNatural.Build _ _ FId F _ ret'_naturality.*)
Definition ret := NattransPack ret'_naturality.
Let join' : F \O F ~~> F := fun _ => bind [hom idfun].
Let fmap_bind a b c (f : {hom a,b}) m (g : {hom c,F a}) :
  (fmap f) (bind g m) = bind [hom fmap f \o g] m.
Proof. by rewrite /fmap bindA. Qed.
Let join'_naturality : naturality (F \O F) F join'.
Proof.
move => A B h.
rewrite /join /= funeqE => m /=.
rewrite fmap_bind bindA /=.
congr (fun f => bind f m).
rewrite hom_ext/=.
rewrite -[in RHS]hom_compA.
by rewrite bindretf_fun.
Qed.
Definition join := NattransPack join'_naturality.
Let bind_fmap a b c (f : {hom a, b}) (m : el (F a)) (g : {hom b, F c}) :
  bind g (fmap f m) = bind [hom g \o f] m .
Proof.
rewrite bindA /=; congr (fun f => bind f m); apply hom_ext => /=.
by rewrite -hom_compA bindretf_fun.
Qed.
Lemma bindE (a b : C) (f : {hom a, F b}) (m : el (F a)) :
  bind f m = join b (([the {functor C -> C} of F] # f) m).
Proof.
rewrite /join /=.
rewrite /=bind_fmap/idfun/=.
congr (fun f => bind f m).
by rewrite hom_ext.
Qed.
Lemma joinretM : JoinLaws.left_unit ret join.
Proof. by rewrite /join => A; rewrite bindretf_fun. Qed.
Let bind_fmap_fun a b c (f : {hom a,b}) (g : {hom b, F c}) :
  bind g \o fmap f = bind [hom g \o f].
Proof. rewrite funeqE => ?; exact: bind_fmap. Qed.
Lemma joinMret : JoinLaws.right_unit ret join.
Proof.
rewrite /join => A; rewrite funeqE => ma.
rewrite bind_fmap_fun/= -[in RHS](bindmret ma).
congr (fun f => bind f ma).
by rewrite hom_ext.
Qed.
Lemma joinA : JoinLaws.associativity join.
Proof.
move => A; rewrite funeqE => mmma.
rewrite /join.
rewrite bind_fmap_fun/= bindA/=.
congr (fun f => bind f mmma).
by rewrite hom_ext.
Qed.
HB.instance Definition _ := isMonad.Build C F bindE joinretM joinMret joinA.
HB.end.

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
by rewrite hom_ext /= (natural eps).
Qed.
HB.instance Definition _ := isNatural.Build C C (M \O M) M join naturality_join.
Let joinE : join = fun a => G # (@eps (F a)).
Proof. by []. Qed.
Let join_associativity' a : join a \o join (M a) = join a \o (M # join a).
Proof.
rewrite joinE -2!(functor_o G).
by congr (G # _); rewrite hom_ext /= (natural eps).
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
by rewrite hom_ext/= triL.
Qed.
(* TODO: the following use of factory fails. why?
HB.instance Definition _ :=
  @Monad_of_ret_join.Build C M
                           [the FId ~> M of ret]
                           [the M \O M ~> M of join]
    join_left_unit join_right_unit join_associativity.
*)
Let bind (a b : C) (f : {hom a, M b}) : {hom M a, M b} :=
  [hom join _ \o (M # f)].
Let bindE (a b : C) (f : {hom a, M b}) (m : el (M a)) :
  bind f m = join b (([the {functor C -> C} of M] # f) m).
Proof. by []. Qed.
HB.instance Definition monad_of_adjoint_mixin :=
  isMonad.Build C M bindE join_left_unit join_right_unit join_associativity.
(* TODO: eliminate Warning: non forgetful inheritance detected *)
End def.
Definition build (C D : category)
           (F : {functor C -> D}) (G : {functor D -> C}) (A : F -| G) :=
  Monad.Pack (Monad.Class (monad_of_adjoint_mixin A)).
End _Monad_of_adjoint_functors.
Notation Monad_of_adjoint_functors := _Monad_of_adjoint_functors.build.
(* TODO: Can we turn this into a factory? *)

(** Converter from category.monad to hierarchy.monad *)
Notation monad := Monad.type.
Require Import hierarchy.

Module Monad_of_category_monad.
Section def.
Variable M : category.monad CT.

Definition acto : Type -> Type := M.

Definition actm (A B : Type) (h : A -> B) (x : acto A) : acto B :=
  (M # hom_Type h) x.

Lemma actm_id A : actm id = @id (acto A).
Proof.
rewrite /actm.
have -> : hom_Type id = [hom idfun] by move=> ?; apply hom_ext.
by rewrite category.functor_id.
Qed.

Lemma actm_comp A B C (g : B -> C) (h : A -> B) :
  actm (g \o h) = actm g \o actm h.
Proof.
rewrite {1}/actm.
have -> : hom_Type (g \o h) = [hom hom_Type g \o hom_Type h] by apply hom_ext.
by rewrite category.functor_o.
Qed.

HB.instance Definition _ := hierarchy.isFunctor.Build acto actm_id actm_comp.

Let F := [the functor of acto].

Definition ret_ : forall A, hierarchy.FId A -> F A :=
  fun A (a : A) => @category.ret _ M A a.
(*Definition ret_ (A : Type) (x : A) : acto A := @Monad.Exports.Ret _ M A x.*)

Definition join_ : forall A, [the functor of F \o F] A -> F A :=
  fun A => @category.join _ M A.
(*Definition join_ (A : Type) (x : acto (acto A)) := @Monad.Exports.Join _ M A x.*)

Lemma naturality_ret : hierarchy.naturality _ _ ret_.
Proof. by move=> ? ? ?; rewrite (category.natural (@category.ret _ M)). Qed.

HB.instance Definition _ := hierarchy.isNatural.Build _ _ ret_ naturality_ret.

Definition ret : hierarchy.Nattrans.type hierarchy.FId F :=
  [the nattrans _ _ of ret_].
(*  hierarchy.Natural.Pack (hierarchy.Natural.Mixin ret_nat).*)

Lemma naturality_join : hierarchy.naturality [the functor of F \o F] F join_.
Proof.
move=> A B h; apply funext=> x; rewrite /ret /hierarchy.actm /= /actm.
rewrite -[in LHS]compE (category.natural category.join).
rewrite compE category.FCompE.
suff -> : (M # (M # hom_Type h)) x = (M # hom_Type (F # h)%monae) x by [].
congr ((M # _ ) _).
exact/hom_ext/funext.
Qed.

HB.instance Definition _ := hierarchy.isNatural.Build _ _ join_ naturality_join.

(*Definition join := hierarchy.Natural.Pack (hierarchy.Natural.Mixin join_nat).*)
Definition join := [the nattrans _ _ of join_].

Lemma joinretM : hierarchy.JoinLaws.left_unit ret join.
Proof.
move=> A; apply funext=> x.
rewrite /join /ret /=.
rewrite /join_ /ret_ /=.
by rewrite -[in LHS]compE category.joinretM.
Qed.

Lemma joinMret (A : Type) : @join A \o (F # @ret _)%monae = id.
Proof.
apply funext=> x; rewrite /join /ret /= /hierarchy.actm /=.
rewrite (_ : actm _ x = (M # category.ret _) x).
  rewrite /join_ /ret_ /=.
  by rewrite -[in LHS]compE category.joinMret.
rewrite /actm.
suff -> : @hom_Type A (M A) (category.ret A) = category.ret _ by [].
by apply hom_ext.
Qed.

Lemma joinA (A : Type) : @join A \o (_ # @join A)%monae = @join _ \o @join _.
Proof.
apply funext=> x; rewrite /join /ret /=.
rewrite /join_ /ret_ /=.
rewrite -[in RHS]compE -category.joinA compE.
congr (_ _).
rewrite /hierarchy.actm [in LHS]/= /actm.
suff -> : @hom_Type (M (M A)) (M A) (category.join A) =
         category.join _ by [].
by apply hom_ext.
Qed.

HB.instance Definition _ := @hierarchy.Monad_of_ret_join.Build acto ret join
  joinretM joinMret joinA.
End def.
End Monad_of_category_monad.
HB.export Monad_of_category_monad.
(* TODO: Can we turn this into a factory? *)
