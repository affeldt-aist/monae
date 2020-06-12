From mathcomp Require Import all_ssreflect.
From mathcomp Require Import boolp.
Require Import monae_lib.

(******************************************************************************)
(*                  Formalization of basic category theory                    *)
(*                                                                            *)
(* This file provides definitions of category, functor, monad, as well as     *)
(* basic theorems. It comes as a generalization of monad.v which is           *)
(* specialized to the category of sets.                                       *)
(*                                                                            *)
(*            category == type of categories, a category C is implemented     *)
(*                        with a universe a la Tarski, there is a realizer    *)
(*                        function El that associates to each object A the    *)
(*                        type El A of its elements; this corresponds to the  *)
(*                        definition of concrete categories                   *)
(*          {hom A, B} == the hom-set of morphisms from A to B                *)
(*             [hom f] == morphism corresponding to the function f            *)
(*       Type_category == the category corresponding to the Coq type Type     *)
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
(*                        Module AdjointFunctors)                             *)
(*      Module AdjComp == define a pair of adjoint functors by composition of *)
(*                        two pairs of adjoint functors                       *)
(* Module MonadOfAdjoint == monad defined by adjointness                      *)
(* Monad_of_category_monad.m == turns a monad over the Type category into     *)
(*                        a monad in the sense of monad.v                     *)
(******************************************************************************)

(* Contents:
- Module Category.
- Module Hom.
- Section category_interface.
- Section category_lemmas.
- Section transport_lemmas.
- Section Type_as_a_category.
- Module FunctorLaws./Module Functor.
- various sections about functors
- Module Natural
- Module NEq.
- Section vertical_composition.
- Section horizontal_composition.
- Module TriangularLaws./Module AdjointFunctors.
- Module AdjComp.
- Module JoinLaws.
- Module BindLaws.
- Section monad_interface.
- Module MonadOfAdjoint.
    monad defined by adjointness
- Module Monad_of_bind_ret.
    monad defined by bind and ret
- Module Monad_of_category_monad.
    interface to monad.v
*)

Reserved Notation "F ~~> G" (at level 51).

Declare Scope category_scope.
Delimit Scope category_scope with category.

Local Open Scope category_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Our categories are always concrete; morphisms are just functions. *)
Module Category.
(* universe a la Tarski *)
Record mixin_of (obj : Type) : Type := Mixin {
  el : obj -> Type ; (* "interpretation" operation, "realizer" *)
(*  _ : injective el ; (* NB: do we need this? *)*)
  inhom : forall A B, (el A -> el B) -> Prop ; (* predicate for morphisms *)
  _ : forall A, @inhom A A idfun ; (* id is in hom *)
  _ : forall A B C (f : el A -> el B) (g : el B -> el C),
      inhom f -> inhom g -> inhom (g \o f) (* hom is closed under composition *) }.
Structure type : Type := Pack { carrier : Type ; class : mixin_of carrier }.
Module Exports.
Notation category := type.
Coercion carrier : category >-> Sortclass.
Definition El (C : category) : C -> Type :=
  let: Pack _ (Mixin x _ _ _) := C in x.
Definition InHom (C : category) : forall (A B : C), (El A -> El B) -> Prop :=
  let: Pack _ (Mixin _ x _ _) := C in x.
Definition idfun_in_hom (C : category) : forall A : C, InHom (A:=A) id :=
  let: Pack _ (Mixin _ _ f _) := C in f.
Definition funcomp_in_hom (C : category) : forall (X Y Z : C)
  (f : El X -> El Y) (g : El Y -> El Z), InHom f -> InHom g -> InHom (g \o f) :=
  let: Pack _ (Mixin _ _ _ f) := C in f.
End Exports.
End Category.
Export Category.Exports.

Module Hom.
Section ClassDef.
Variables (C : category) (U V : C).
Structure map (phUV : phant (El U -> El V)) :=
  Pack {apply : El U -> El V; _ : InHom apply}.
Local Coercion apply : map >-> Funclass.
Variables (phUV : phant (El U -> El V)) (f g : El U -> El V) (cF : map phUV).
Definition class := let: Pack _ c as cF' := cF return InHom cF' in c.
Definition clone fA of phant_id g (apply cF) & phant_id fA class :=
  @Pack phUV f fA.
End ClassDef.
Definition map' := map.
Module Exports.
Coercion apply : map >-> Funclass.
Add Printing Coercion apply.
Notation "[ 'fn' f ]" := (apply f)
  (at level 0, format "[ 'fn'  f ]", only printing) : category_scope.
Notation HomPack fA := (Pack (Phant _) fA).
Notation "{ 'hom' U , V }" := (map (Phant (El U -> El V)))
  (at level 0, format "{ 'hom'  U ,  V }") : category_scope.
Arguments map' : simpl never.
Notation "{ 'hom' C ; U , V }" := (@map' C U V (Phant (El U -> El V)))
  (at level 0, format "{ 'hom'  C ;  U ,  V }") : category_scope.
Notation "[ 'hom' f ]" := (@clone _ _ _ _ f f _ _ id id)
  (at level 0, format "[ 'hom'  f ]") : category_scope.
End Exports.
End Hom.
Export Hom.Exports.

Local Open Scope category_scope.

Lemma hom_ext (C : category) (a b : C) (f g : {hom a, b}) : f = g <-> f = g :> (_ -> _).
Proof.
move: f g => [f Hf] [g Hg] /=; split => [[]//|fg /=].
by rewrite fg in Hf *; rewrite (Prop_irrelevance Hf Hg).
Qed.

Section category_interface.
Variable C : category.
Implicit Types a b c : C.

Lemma InHom_idfun c : InHom (@idfun (El c)).
Proof. by case: C c => [? []]. Qed.
Canonical homid0 c := HomPack (InHom_idfun c).

Lemma InHom_compfun a b c (f : {hom b, c}) (g : {hom a, b}) : InHom (f \o g).
Proof. case: C a b c f g => [car [? ? ? x]] a b c [f ?] [g ?]; exact/x. Qed.
Canonical homcomp0 (a b c : C) (f : {hom b, c}) (g : {hom a, b}) :=
  HomPack (InHom_compfun f g).

Let homcomp0E (a b c : C) (g : {hom b, c}) (f : {hom a, b}) :
  homcomp0 g f = [hom g \o f].
Proof. by []. Qed.

End category_interface.

(* Experimental notation [\o f , .. , g , h]:
   The purpose is to pretty print the sequence of hom compositions
   that frequently appear in category theory textbooks. *)
Module comps_notation.
Notation "[ '\o' f , .. , g , h ]" := (f \o .. (g \o h) ..) (at level 0,
  format "[ '[' '\o'  f ,  '/' .. ,  '/' g ,  '/' h ']' ]") : category_scope.
End comps_notation.

Section category_lemmas.
Variable C : category.

Lemma homfunK (a b : C) (f : {hom a, b}) : [hom f] = f.
Proof. by case: f. Qed.

Lemma homcompA (a b c d : C) (h : {hom c, d}) (g : {hom b, c}) (f : {hom a, b}) :
  [hom [hom h \o g] \o f] = [hom h \o [hom g \o f]].
Proof. by move: f g h => [? ?] [? ?] [? ?]; apply hom_ext. Qed.

Lemma homcompE (a b c : C) (g : {hom b, c}) (f : {hom a, b}) :
  [hom g \o f] = g \o f :> (El a -> El c).
Proof. by []. Qed.

Lemma hom_compE (a b c : C) (g : {hom b, c}) (f : {hom a, b}) x :
  g (f x) = (g \o f) x.
Proof. exact: compE. Qed.

Import comps_notation.

(* Restricting the components of a composition to homs and using the lemma
   homcompA, we can avoid the infinite sequence of redundunt compositions
   "_ \o id" or "id \o _" that pops out when we "rewrite !compA".*)
Lemma hom_compA (a b c d : C) (h : {hom c, d}) (g : {hom b, c}) (f : {hom a, b}) :
  (h \o g) \o f = [\o h, g, f] :> (El a -> El d).
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
  transport_codom p (homid0 a).

(* F for factorization *)
Lemma transport_domF (a a' b : C) (p : a = a') (f : {hom a, b}) :
  transport_dom p f = [hom f \o hom_of_eq (esym p)].
Proof. apply hom_ext; by subst a'. Qed.
Lemma transport_codomF (a b b' : C) (p : b = b') (f : {hom a, b}) :
  transport_codom p f = [hom hom_of_eq p \o f].
Proof. apply hom_ext; by subst b'. Qed.
End transport_lemmas.

Section Type_as_a_category.
Definition Type_category_mixin : Category.mixin_of Type :=
  @Category.Mixin Type (fun x : Type => x)
    (fun _ _ _ => True) (fun=> I) (fun _ _ _ _ _ _ _ => I).
Canonical Type_category := Category.Pack Type_category_mixin.
Definition hom_Type (a b : Type) (f : a -> b) : {hom a, b} :=
  HomPack (I : InHom (f : El a -> El b)).
End Type_as_a_category.

Module FunctorLaws.
Section def.
Variable (C D : category).
Variable (M : C -> D) (f : forall A B, {hom A,B} -> {hom M A, M B}).
Definition id := forall A, f [hom idfun] = [hom idfun] :> {hom M A, M A}.
Definition comp := forall A B C (g : {hom B, C}) (h : {hom A, B}),
  f [hom g \o h] = [hom f g \o f h].
End def.
End FunctorLaws.

Module Functor.
Record mixin_of (C D : category) (M : C -> D) : Type := Mixin {
  actm : forall A B, {hom A, B} -> {hom M A, M B} ;
  _ : FunctorLaws.id actm ;
  _ : FunctorLaws.comp actm }.
Structure type (C D : category) : Type :=
  Pack { acto : C -> D ; class : mixin_of acto }.
Module Exports.
Section exports.
Variables (C D : category).
Definition Actm (F : type C D) : forall A B, {hom A, B} -> {hom acto F A, acto F B} :=
  let: Pack _ (Mixin f _ _) := F in f.
Arguments Actm _ [A] [B] : simpl never.
End exports.
Notation "F # f" := (Actm F f) : category_scope.
Notation functor := type.
Coercion acto : functor >-> Funclass.
End Exports.
End Functor.
Export Functor.Exports.

Section functor_lemmas.
Variables (C D : category) (F : functor C D).
Lemma functor_id_hom : FunctorLaws.id (Actm F).
Proof. by case: F => [? []]. Qed.
Lemma functor_o_hom : FunctorLaws.comp (Actm F).
Proof. by case: F => [? []]. Qed.

Lemma functor_id a : F # [hom idfun] = idfun :> (El (F a) -> El (F a)).
Proof. by rewrite functor_id_hom. Qed.
Lemma functor_o a b c (g : {hom b, c}) (h : {hom a, b}) :
  F # [hom g \o h] = F # g \o F # h :> (El (F a) -> El (F c)).
Proof. by rewrite functor_o_hom. Qed.

Lemma functor_ext (G : functor C D) (pm : Functor.acto F =1 Functor.acto G) :
  (forall (A B : C) (f : {hom A, B}),
      transport_hom (pm A) (pm B) (Functor.actm (Functor.class F) f) =
      Functor.actm (Functor.class G) f) -> F = G.
Proof.
move: pm.
case: F => mf cf; case: G => mg cg /= pm.
move: cf cg.
rewrite /transport_hom.
move: (funext pm) => ppm.
subst mg => -[ff idf cf] -[fg idg cg] p.
have pp : ff = fg.
  apply functional_extensionality_dep=> A.
  apply functional_extensionality_dep=> B.
  apply functional_extensionality_dep=> f.
  move: (p A B f).
  have -> // : pm = (fun _ => erefl).
  exact: Prop_irrelevance.
rewrite {p}.
move: idf cf idg cg; rewrite pp => *.
congr (Functor.Pack (Functor.Mixin _ _)); exact/Prop_irrelevance.
Qed.
End functor_lemmas.

Section functor_o_head.
Import comps_notation.
Variable C D : category.
Lemma functor_o_head a b c (g : {hom b, c}) (h : {hom a, b}) d (F : functor C D)
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
Definition FId : functor _ _ := Functor.Pack (Functor.Mixin id_id id_comp).
Lemma FIdf (A B : C) (f : {hom A, B}) : FId # f = f.
Proof. by []. Qed.
End functorid.
Arguments FId {C}.

Section functorcomposition.
Variables (C0 C1 C2 : category) (F : functor C1 C2) (G : functor C0 C1).
Definition functorcomposition a b := fun h : {hom a, b} => F # (G # h).
Lemma functorcomposition_id : FunctorLaws.id functorcomposition.
Proof.
by rewrite /FunctorLaws.id => A; rewrite /functorcomposition 2!functor_id_hom.
Qed.
Lemma functorcomposition_comp : FunctorLaws.comp functorcomposition.
Proof.
rewrite /FunctorLaws.comp => a b c g h; rewrite /functorcomposition.
by rewrite 2!functor_o_hom.
Qed.
Definition FComp : functor C0 C2:=
  Functor.Pack (Functor.Mixin functorcomposition_id functorcomposition_comp).
End functorcomposition.
Arguments FComp : simpl never.

Notation "f \O g" := (FComp f g).

Section functorcomposition_lemmas.
Variables (C0 C1 C2 C3 : category).
Lemma FCompId (F : functor C0 C1) : F \O FId = F.
Proof.
case: F => ? [???]; congr (Functor.Pack (Functor.Mixin _ _));
  exact/Prop_irrelevance.
Qed.
Lemma FIdComp (F : functor C0 C1) : FId \O F = F.
Proof.
case: F => ? [???]; congr (Functor.Pack (Functor.Mixin _ _));
  exact/Prop_irrelevance.
Qed.
Lemma FCompA (F : functor C2 C3) (G : functor C1 C2) (H : functor C0 C1) :
  (F \O G) \O H = F \O (G \O H).
Proof.
move: F G H => [f [???]] [g [???]] [h [???]].
congr (Functor.Pack (Functor.Mixin  _ _)); exact/Prop_irrelevance.
Qed.
Lemma FCompE (F : functor C1 C2) (G : functor C0 C1) a b (k : {hom a, b}) :
  (F \O G) # k = F # (G # k).
Proof. by []. Qed.
End functorcomposition_lemmas.

Notation "F ~~> G" := (forall a, {hom F a ,G a}).

Definition naturality (C D : category) (F G : functor C D) (f : F ~~> G) :=
  forall c0 c1 (h : {hom c0, c1}), (G # h) \o (f c0) = (f c1) \o (F # h).
Arguments naturality [C D].

(* natural transformation *)
Module Natural.
Record mixin_of (C D : category) (F G : functor C D) (f : F ~~> G) :=
  Mixin { _ : naturality F G f }.
Structure type (C D : category) (F G : functor C D) := Pack
  { cpnt : F ~~> G ; class : mixin_of cpnt }.
Module Exports.
Coercion cpnt : type >-> Funclass.
Notation "h ~> g" := (type h g).
Notation Natural p := (Pack (Mixin p)).
End Exports.
End Natural.
Export Natural.Exports.

Section natural_transformation_lemmas.
Variables (C D : category) (F G : functor C D).
Lemma natural (phi : F ~> G) a b (h : {hom a, b}) :
  (G # h) \o (phi a) = (phi b) \o (F # h).
Proof. by case: phi => ? []. Qed.

Import comps_notation.

Lemma natural_head (phi : F ~> G) a b c (h : {hom a, b}) (f : {hom c, F a}) :
  [\o G # h, phi a, f] = [\o phi b, F # h, f].
Proof. by rewrite -!hom_compA natural. Qed.

Lemma nattrans_ext (f g : F ~> G) :
  f = g <-> forall a, (f a = g a :> (_ -> _)).
Proof.
split => [ -> // |]; move: f g => [f Hf] [g Hg] /= fg''.
have fg' : forall a, f a = g a :> {hom _, _} by move=> a; rewrite hom_ext fg''.
move: (functional_extensionality_dep fg') => fg.
by rewrite fg in Hf *; rewrite (Prop_irrelevance Hf Hg).
Qed.

End natural_transformation_lemmas.
Arguments natural [C D F G].
Arguments natural_head [C D F G].

Section id_natural_transformation.
Variables (C D : category) (F : functor C D).
Definition natural_id : naturality _ _ (fun a => homid0 (F a)).
Proof. by []. Qed.
Definition NId : F ~> F := Natural.Pack (Natural.Mixin natural_id).
Lemma NIdE : NId  = (fun a => homid0 (F a)) :> (_ ~~> _).
Proof. by []. Qed.
End id_natural_transformation.

Module NEq.
Section def.
Import comps_notation.
Variables (C D : category) (F G : functor C D).
Variable (Iobj : forall c, F c = G c).
Local Notation tc := (transport_codom (Iobj _)).
Local Notation td := (transport_dom (esym (Iobj _))).
Variable (Imor : forall a b (f : {hom a, b}), tc (F # f) = td (G # f)).
Definition f : F ~~> G := fun (c : C) => tc (homid0 (F c)).
Lemma natural : naturality F G f.
Proof.
move=> a b h.
rewrite /f !transport_codomF 2!homcompE 2!compfid.
have /hom_ext -> : [hom (hom_of_eq (Iobj b) \o F # h)] = [hom tc (F # h)]
  by rewrite transport_codomF.
by rewrite homfunK Imor transport_domF homfunK /= esymK.
Qed.
Definition n : F ~> G := Natural.Pack (Natural.Mixin natural).
End def.
Module Exports.
Arguments n [C D] : simpl never.
Notation NEq := n.
Lemma NEqE C D F G Iobj Imor :
  @NEq C D F G Iobj Imor =
  (fun a => transport_codom (Iobj _) (homid0 (F a))) :> (_ ~~> _).
Proof. by []. Qed.
End Exports.
End NEq.
Export NEq.Exports.

Notation "[ 'NEq' F , G ]" :=
  (NEq F G (fun a => erefl) (fun a b f => erefl))
    (at level 0, format "[ 'NEq'  F ,  G ]") : category_scope.

Section vertical_composition.
Variables (C D : category) (F G H : functor C D).
Variables (g : G ~> H) (f : F ~> G).
Definition ntcomp := fun a => [hom g a \o f a].
Definition natural_vcomp : naturality _ _ ntcomp.
Proof. by move=> A B h; rewrite compA (natural g) -compA (natural f). Qed.
Definition VComp : F ~> H := Natural.Pack (Natural.Mixin natural_vcomp).
End vertical_composition.
Notation "f \v g" := (VComp f g).

Section vcomp_lemmas.
Variables (C D : category) (F G H I : functor C D).
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
Variables (C D E : category) (F G : functor C D) (F' G' : functor D E).
Variables (s : F ~> G) (t : F' ~> G').
Lemma natural_hcomp :
  naturality (F' \O F) (G' \O G) (fun c => [hom t (G c) \o F' # s c]).
Proof.
move=> c0 c1 h.
rewrite [in LHS]compA (natural t) -[in LHS]compA -[in RHS]compA; congr (_ \o _).
rewrite [in RHS]FCompE -2!functor_o; congr (F' # _); apply hom_ext => /=.
by rewrite (natural s).
Qed.
Definition HComp : (F' \O F) ~> (G' \O G) :=
  Natural.Pack (Natural.Mixin natural_hcomp).
End horizontal_composition.
Notation "f \h g" := (locked (HComp g f)).

Section hcomp_extensionality_lemmas.
Variables (C D E : category) (F G : functor C D) (F' G' : functor D E).
Variables (s : F ~> G) (t : F' ~> G').
Lemma HCompE_def : t \h s = HComp s t. Proof. by unlock. Qed.
Lemma HCompE c : (t \h s) c = t (G c) \o F' # s c :> (_ -> _).
Proof. by unlock. Qed.
Lemma HCompE_alt c : (t \h s) c = G' # (s c) \o t (F c) :> (_ -> _).
Proof. by rewrite HCompE natural. Qed.
End hcomp_extensionality_lemmas.

Section hcomp_id_assoc_lemmas.
Import comps_notation.
Variables (C D E Z : category).
Variables (F G : functor C D) (F' G' : functor D E) (F'' G'' : functor E Z).
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
Variables (F G : functor C D) (F' G' : functor D E).
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
Variables (H : functor C D) (H' : functor D E).
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
Variables (C D : category) (F : functor C D) (G : functor D C).
Variables (eta : FId ~> G \O F) (eps : F \O G ~> FId).
Definition left := forall c, eps (F c) \o F # (eta c) = idfun.
Definition right := forall d, G # (eps d) \o eta (G d) = idfun.
End triangularlaws.
End TriangularLaws.

Module AdjointFunctors.
Section def.
Variables (C D : category) (F : functor C D) (G : functor D C).
Record t := mk {
  eta : FId ~> G \O F ;
  eps : F \O G ~> FId ;
  triL : TriangularLaws.left eta eps ;
  triR : TriangularLaws.right eta eps
}.
End def.
Section lemmas.
Local Notation "F -| G" := (t F G).
Variables (C D : category) (F : functor C D) (G : functor D C).
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

Lemma eta_hom_iso (c : C) : eta A c = hom_iso (homid0 (F c)).
Proof. by apply hom_ext; rewrite /hom_iso homfunK /= functor_id. Qed.
Lemma eps_hom_inv (d : D) : eps A d = hom_inv (homid0 (G d)).
Proof. by apply hom_ext; rewrite /hom_inv homfunK /= functor_id compfid. Qed.

Lemma ext (B : F -| G) : eta A = eta B -> eps A = eps B -> A = B.
Proof.
move: A B => [? ? ? ?] [? ? ? ?] /= ? ?; subst.
congr mk; exact/Prop_irrelevance.
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
Variables (C0 C1 C2 : category).
Variables (F0 : functor C0 C1) (G0 : functor C1 C0).
Variables (F1 : functor C1 C2) (G1 : functor C2 C1).
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
move=> c; rewrite EpsE_hom EtaE (functor_o_head G) -(functor_o_head G0 (eta0 _)); cbn.
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
Variables (F : functor C0 C1) (G : functor C1 C0) (A0 : F -| G).
Variables (F' : functor C1 C2) (G' : functor C2 C1) (A1 : F' -| G').
Definition adj_comp := AdjointFunctors.mk
  (triL (AdjointFunctors.triL A0) (AdjointFunctors.triL A1))
  (triR (AdjointFunctors.triR A0) (AdjointFunctors.triR A1)).
End adj_comp.
End Exports.
End AdjComp.
Export AdjComp.Exports.

(* monad *)
Module JoinLaws.
Section join_laws.
Variables (C : category) (M : functor C C) .
Variables (ret : FId ~~> M)
          (join : M \O M ~~> M).

Definition ret_naturality := naturality FId M ret.

Definition join_naturality := naturality (M \O M) M join.

Definition left_unit :=
  forall a, join a \o ret (M a) = idfun :> (El (M a) -> El (M a)).

Definition right_unit :=
  forall a, join a \o M # ret a = idfun :> (El (M a) -> El (M a)).

Definition associativity :=
  forall a, join a \o M # join a = join a \o join (M a) :> (El (M (M (M a))) -> El (M a)).
End join_laws.
End JoinLaws.

Module BindLaws.
Section bindlaws.
Variables (C : category) (M : C -> C).

Variable b : forall A B, {hom A, M B} -> {hom M A, M B}.
Local Notation "m >>= f" := (b f m).
(*
I am not convinced if the above typing of `bind' makes sense from the
category-theoretical point of view.  It is rather an ad hoc change needed for
stating the associavitity below.  I am not sure either if it works well in
further formalizations.  Both should be checked with careful thoughts and
examples.

Original and usual definition is :
Variable b : forall A B, M A -> (A -> M B) -> M B.
Local Notation "m >>= f" := (b m f).

This original definition seems to be valid only in closed categories, which
would be a mix-in structure over categories.
*)

Fact associative_aux x y z (f : {hom x, M y}) (g : {hom y, M z}) :
  (fun w => (f w >>= g)) = (b g \o f).
Proof. by []. Qed.

Definition associative := forall A B C (m : El (M A)) (f : {hom A, M B}) (g : {hom B, M C}),
  (m >>= f) >>= g = m >>= [hom b g \o f].

Definition left_neutral (r : forall A, {hom A, M A}) :=
  forall A B (f : {hom A, M B}), [hom (b f \o r A)] = f.

Definition right_neutral (r : forall A, {hom A, M A}) :=
  forall A (m : El (M A)), m >>= r _ = m.
End bindlaws.

Section bindlaws_on_Type.
Variable M : functor Type_category Type_category.

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

Module Monad.
Section monad.
Variable (C : category).
Record mixin_of (M : functor C C) : Type := Mixin {
  ret : forall A, {hom A, M A} ;
  join : forall A, {hom M (M A), M A} ;
  _ : JoinLaws.ret_naturality ret ;
  _ : JoinLaws.join_naturality join ;
  _ : JoinLaws.left_unit ret join ;
  _ : JoinLaws.right_unit ret join ;
  _ : JoinLaws.associativity join }.
Record class_of (M : C -> C) := Class {
  base : Functor.mixin_of M ; mixin : mixin_of (Functor.Pack base) }.
Structure type : Type := Pack { acto : C -> C ; class : class_of acto }.
Definition baseType (M : type) := Functor.Pack (base (class M)).
End monad.
Module Exports.
Definition Ret (C : category) (M : type C) : forall A, {hom A, acto M A} :=
  let: Pack _ (Class _ (Mixin ret _ _ _ _ _ _) ) := M return forall A, {hom A, acto M A} in ret.
Arguments Ret {C M A} : simpl never.
Definition Join (C : category) (M : type C) : forall A ,{hom acto M (acto M A), acto M A} :=
  let: Pack _ (Class _ (Mixin _ join _ _ _ _ _)) := M in join.
Arguments Join {C M A} : simpl never.
Notation monad := type.
Coercion baseType : monad >-> functor.
Canonical baseType.
End Exports.
End Monad.
Export Monad.Exports.

Section monad_interface.
Variable (C : category) (M : monad C).
Lemma ret_naturality : JoinLaws.ret_naturality (@Ret C M).
Proof. by case: M => ? [? []]. Qed.
Lemma join_naturality : JoinLaws.join_naturality (@Join C M).
Proof. by case: M => ? [? []]. Qed.
Lemma joinretM : JoinLaws.left_unit (@Ret C M) (@Join C M).
Proof. by case: M => ? [? []]. Qed.
Lemma joinMret : JoinLaws.right_unit (@Ret C M) (@Join C M).
Proof. by case: M => ? [? []]. Qed.
Lemma joinA : JoinLaws.associativity (@Join C M).
Proof. by case: M => ? [? []]. Qed.

(* *_head lemmas are for [fun of f] \o ([fun of g] \o ([fun of h] \o ..))*)
Import comps_notation.
Definition ret_naturality_head :=
  natural_head (Natural ret_naturality).
Definition join_naturality_head :=
  natural_head (Natural join_naturality).
Lemma joinretM_head a (c : C) (f : {hom c, M a}) : [\o Join, Ret, f] = f.
Proof. by rewrite compA joinretM. Qed.
Lemma joinMret_head a (c : C) (f : {hom c, M a}) : [\o Join, M # Ret, f] = f.
Proof. by rewrite compA joinMret. Qed.
Lemma joinA_head a (c : C) (f : {hom c, M (M (M a))}) :
  [\o Join, M # Join, f] = [\o Join, Join, f].
Proof. by rewrite compA joinA. Qed.
End monad_interface.

Section from_join_laws_to_bind_laws.
Variable (C : category) (F : functor C C).
Variable (ret : forall A, {hom A, F A}) (join : forall A, {hom F (F A), F A}).

Hypothesis ret_naturality : JoinLaws.ret_naturality ret.
Hypothesis join_naturality : JoinLaws.join_naturality join.
Hypothesis joinretM : JoinLaws.left_unit ret join.
Hypothesis joinMret : JoinLaws.right_unit ret join.
Hypothesis joinA : JoinLaws.associativity join.

Import comps_notation.

Let ret_naturality_head := natural_head (Natural ret_naturality).
Let join_naturality_head := natural_head (Natural join_naturality).
Let joinretM_head a (c : C) (f : {hom c,F a}) : [\o @join _, @ret _, f] = f.
Proof. by rewrite compA joinretM. Qed.
Let joinMret_head a (c : C) (f : {hom c,F a}) : [\o @join _, F # @ret _, f] = f.
Proof. by rewrite compA joinMret. Qed.
Let joinA_head a (c : C) (f : {hom c, F (F (F a))}) :
  [\o @join _, F # @join _, f] = [\o @join _, @join _, f].
Proof. by rewrite compA joinA. Qed.

Let bind (A B : C) (f : {hom A, F B}) : {hom F A, F B} := [hom (@join B) \o (F # f)].

Lemma bindretf_derived : BindLaws.left_neutral bind ret.
Proof.
move=> A B f; apply hom_ext=>/=.
by rewrite hom_compA ret_naturality joinretM_head.
Qed.

Lemma bindmret_derived : BindLaws.right_neutral bind ret.
Proof. by move=> A m; rewrite /bind /= !hom_compE joinMret. Qed.

Lemma bindA_derived : BindLaws.associative bind.
Proof.
move=>a b c m f g; rewrite /bind.
cbn; rewrite 4!hom_compE; congr (_ m).
rewrite 2!functor_o !hom_compA.
by rewrite join_naturality_head joinA_head.
Qed.
End from_join_laws_to_bind_laws.

Section monad_lemmas.
Variable (C : category) (M : monad C).

Definition Bind A B (f : {hom A, M B}) : {hom M A, M B} := [hom Join \o (M # f)].
Arguments Bind {A B} : simpl never.
Local Notation "m >>= f" := (Bind f m).
Lemma bindE (A B:C) : Bind = fun (f : {hom A,M B}) => [hom Join \o M # f].
Proof. by []. Qed.
Lemma bindretf : BindLaws.left_neutral (@Bind) (@Ret C M).
Proof. apply: bindretf_derived; [exact: ret_naturality | exact: joinretM]. Qed.
Lemma bindretf_fun :
  (forall (A B : C) (f : {hom A,M B}),
      (@Bind) A B f \o (@Ret C M) A = f).
Proof. exact/bind_left_neutral_hom_fun/bindretf. Qed.
Lemma bindmret : BindLaws.right_neutral (@Bind) (@Ret C M).
Proof. apply: bindmret_derived; exact: joinMret. Qed.
Lemma bindA : BindLaws.associative (@Bind).
Proof. apply bindA_derived; [exact: join_naturality | exact: joinA]. Qed.

Lemma bindE_ext A B : forall x (f : {hom A, M B}), x >>= f = Join ((M # f) x).
Proof. by []. Qed.
End monad_lemmas.
Arguments Bind {C M A B} : simpl never.
Notation "m >>= f" := (Bind f m).

Module MonadOfAdjoint.
Section monad_of_adjoint.
Import comps_notation.
Variables C D : category.
Variables (F : functor C D) (G : functor D C).
Variable A : F -| G.
Definition eps := AdjointFunctors.eps A.
Definition eta := AdjointFunctors.eta A.
Definition M := G \O F.
Definition join a : {hom M (M a), M a} := G # (eps (F a)).
Definition ret a : {hom a, M a} := eta a.
Let triL := AdjointFunctors.triL A.
Let triR := AdjointFunctors.triR A.
Let joinE : join = fun a => G # (@eps (F a)).
Proof. by []. Qed.
Lemma join_natural : JoinLaws.join_naturality join.
Proof.
rewrite !joinE => a b h.
rewrite /M !FCompE -2!(functor_o G); congr (G # _).
by rewrite hom_ext /= (natural eps).
Qed.
Let join_associativity' a : join a \o join (M a) = join a \o (M # join a).
Proof.
rewrite joinE -2!(functor_o G).
by congr (Actm G); rewrite hom_ext /= (natural eps).
Qed.
Lemma join_associativity : JoinLaws.associativity join.
Proof. by move=> a; rewrite join_associativity'. Qed.
Lemma ret_natural : JoinLaws.ret_naturality ret.
Proof. by move=> *; rewrite (natural eta). Qed.
Lemma join_left_unit : JoinLaws.left_unit ret join.
Proof. by move=> a; rewrite joinE triR. Qed.
Lemma join_right_unit : JoinLaws.right_unit ret join.
Proof.
move=> a; rewrite joinE. rewrite /M FCompE.
rewrite /= -functor_o -[in RHS]functor_id.
congr (Actm G).
by rewrite hom_ext/= triL.
Qed.
Definition monad_of_adjoint_mixin : Monad.mixin_of M :=
  Monad.Mixin ret_natural join_natural
              join_left_unit join_right_unit join_associativity.
End monad_of_adjoint.
Module Exports.
Definition Monad_of_adjoint C D
           (F : functor C D) (G : functor D C)
           (A : F -| G) :=
  Monad.Pack (Monad.Class (monad_of_adjoint_mixin A)).
End Exports.
End MonadOfAdjoint.
Export MonadOfAdjoint.Exports.

(* monad defined by bind and ret *)
Module Monad_of_bind_ret.
Section monad_of_bind_ret.
Import comps_notation.
Variables C : category.
Variable M : C -> C.
Variable bind : forall A B, {hom A,M B} -> {hom M A,M B}.
Variable ret : forall A, {hom A, M A}.
Hypothesis bindretf : BindLaws.left_neutral bind ret.
Hypothesis bindmret : BindLaws.right_neutral bind ret.
Hypothesis bindA : BindLaws.associative bind.

Lemma bindretf_fun : (forall (A B : C) (f : {hom A,M B}),
  bind f \o ret A = f).
Proof. exact/bind_left_neutral_hom_fun. Qed.

Definition fmap A B (f : {hom A,B}) := bind [hom ret B \o f].
Lemma fmap_id : FunctorLaws.id fmap.
Proof.
move=> A; apply/hom_ext/funext=>m. rewrite /fmap.
rewrite/idfun/=.
rewrite -[in RHS](bindmret m).
congr (fun f => bind f m).
by rewrite hom_ext.
Qed.
Lemma fmap_o : FunctorLaws.comp fmap.
Proof.
move=> a b c g h; apply/hom_ext/funext=>m; rewrite /fmap/=.
rewrite bindA/=.
congr (fun f => bind f m); rewrite hom_ext/=.
by rewrite -[in RHS]hom_compA bindretf_fun.
Qed.
Definition functor_mixin := Functor.Mixin fmap_id fmap_o.
Let M' := Functor.Pack functor_mixin.

Let ret' : forall A, {hom A, M' A} := ret.
Definition join A : {hom M' (M' A), M' A} := bind [hom idfun].

Let bind_fmap a b c (f : {hom a, b}) (m : El (M a)) (g : {hom b, M c}) :
  bind g (fmap f m) = bind [hom g \o f] m .
Proof.
rewrite bindA /=; congr (fun f => bind f m); apply hom_ext => /=.
by rewrite -hom_compA bindretf_fun.
Qed.

Lemma bind_fmap_fun a b c (f : {hom a,b}) (g : {hom b, M c}) :
  bind g \o fmap f = bind [hom g \o f].
Proof. rewrite funeqE => ?; exact: bind_fmap. Qed.

Lemma ret_naturality : naturality FId M' ret.
Proof. by move=> A B h; rewrite FIdf bindretf_fun. Qed.

Let bindE A B (f : {hom A, M' B}) : bind f = [hom (join B) \o (M' # f)].
Proof.
rewrite /join.
apply/hom_ext/funext => m.
rewrite /=bind_fmap/idfun/=.
congr (fun f => bind f m).
by rewrite hom_ext.
Qed.

Let fmap_bind a b c (f : {hom a,b}) m (g : {hom c,M a}) :
  (fmap f) (bind g m) = bind [hom fmap f \o g] m.
Proof. by rewrite /fmap bindA bindE. Qed.

Lemma join_naturality : naturality (FComp M' M') M' join.
Proof.
move => A B h.
rewrite /join /= funeqE => m /=.
rewrite fmap_bind bindA /=.
congr (fun f => bind f m).
rewrite hom_ext/=.
rewrite -[in RHS]hom_compA.
by rewrite bindretf_fun.
Qed.

Lemma joinretM : JoinLaws.left_unit ret' join.
Proof. by rewrite /join => A; rewrite bindretf_fun. Qed.

Lemma joinMret : JoinLaws.right_unit ret' join.
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

Definition monad_mixin := Monad.Mixin
  ret_naturality join_naturality joinretM joinMret joinA.
End monad_of_bind_ret.
Module Exports.
Definition Monad_of_bind_ret C M bind ret a b c :=
  Monad.Pack (Monad.Class (@monad_mixin C M bind ret a b c)).
End Exports.
End Monad_of_bind_ret.
Export Monad_of_bind_ret.Exports.

(* interface to monad.v *)
Require hierarchy.
Module Monad_of_category_monad.
Section def.
Variable (M : monad Type_category).
Definition m'' : Type -> Type := M.
Definition f (A B : Type) (h : A -> B) (x : m'' A) : m'' B :=
  (M # hom_Type h) x.
Lemma fid A : f id = id :> (m'' A -> m'' A).
Proof.
rewrite /f.
have -> : hom_Type id = [hom idfun] by move=> ?; apply hom_ext.
by rewrite functor_id.
Qed.
Lemma fcomp A B C (g : B -> C) (h : A -> B) :
  f (g \o h) = f g \o f h :> (m'' A -> m'' C).
Proof.
rewrite {1}/f.
have -> : hom_Type (g \o h) = [hom hom_Type g \o hom_Type h] by apply hom_ext.
by rewrite functor_o.
Qed.
Definition m' := hierarchy.Functor.Pack (hierarchy.Functor.Mixin fid fcomp).

Import hierarchy.Functor.Exports.

Definition ret (A : Type) (x : A) : m' A := (@Ret _ M A x).
Definition join (A : Type) (x : m' (m' A)) := (@Join _ M A x).

Lemma joinE A (x : m' (m' A)) : join x = @Join _ M A x.
Proof. by []. Qed.

Lemma ret_nat : hierarchy.naturality hierarchy.FId m' ret.
Proof. move=> ? ? ?; exact: (ret_naturality M). Qed.
Definition _ret_nat : hierarchy.Natural.type hierarchy.FId m' := hierarchy.Natural.Pack (hierarchy.Natural.Mixin ret_nat).
Lemma join_nat : hierarchy.naturality (hierarchy.FComp m' m') m' join.
Proof.
move=> A B h; apply funext=> x; rewrite /ret /Actm /= /f.
rewrite -[in LHS]compE join_naturality.
rewrite compE FCompE.
suff -> : (M # (M # hom_Type h)) x = (M # hom_Type (Actm m' h)) x
  by [].
congr ((M # _ ) _).
by apply/hom_ext/funext.
Qed.
Definition _join_nat := hierarchy.Natural.Pack (hierarchy.Natural.Mixin join_nat).
Lemma joinretM : hierarchy.JoinLaws.left_unit _ret_nat _join_nat.
Proof.
by move=> A; apply funext=> x; rewrite /join /ret /= -[in LHS]compE joinretM.
Qed.
Lemma joinMret (A : Type) : @join _ \o (Actm m' (@ret _)) = id :> (m' A -> m' A).
Proof.
apply funext=> x; rewrite /join /ret /Actm /=.
suff -> : @f A (m'' A) [eta (@Ret Type_category M A)] x =
         (M # Ret) x
  by rewrite -[in LHS]compE joinMret.
rewrite /f /m'' /=.
suff -> : @hom_Type A (M A) [eta (@Ret Type_category M A)] = Ret by [].
by apply hom_ext.
Qed.
Lemma joinA (A : Type) :
  @join _ \o Actm m' (@join _) = @join _ \o @join _ :> (m' (m' (m' A)) -> m' A).
Proof.
apply funext=> x; rewrite /join /ret /Actm /=.
rewrite -[in RHS]compE -joinA compE.
congr (_ _).
rewrite /f /m'' /=.
suff -> : (@hom_Type (M (M A)) (M A)
                    [eta (@Join Type_category M A)]) = Join by [].
by apply hom_ext.
Qed.

Definition m : hierarchy.Monad.type := hierarchy.Monad.Pack
 (hierarchy.Monad.Class (hierarchy.Monad.Mixin joinretM joinMret joinA)).
End def.
Module Exports.
Notation Monad_of_category_monad := m.
End Exports.
End Monad_of_category_monad.
Export Monad_of_category_monad.Exports.
