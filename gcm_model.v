(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2020 monae authors, license: LGPL-2.1-or-later               *)
Require Import Reals.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import boolp classical_sets.
From mathcomp Require Import finmap.
From infotheo Require Import Reals_ext classical_sets_ext ssrR ssr_ext.
From infotheo Require Import fdist fsdist convex necset.
Require Import monae_lib.
From HB Require Import structures.
Require Import category.

(******************************************************************************)
(*             Construction of the geometrically convex monad                 *)
(*                                                                            *)
(* This file defines the functor P_delta and shows that it is a monad.        *)
(* The proof uses the adjointness relations depicted as follows:              *)
(*                                                                            *)
(* Functors:  |       FC            F0           F1                           *)
(*            |     ---->          ---->        ---->                         *)
(* Categories:| Type     choiceType     convType     semiCompSemiLattConvType *)
(*            |             (CC)          (CV)                (CS)            *)
(*            |     <----          <----        <----                         *)
(* Forgetful  |       UC             U0           U1                          *)
(* Functors:  |                                                               *)
(*                                                                            *)
(* FC -| UC:                                                                  *)
(*                  CC := [the category of choiceType]                        *)
(*     free_choiceType := [the {functor CT -> CC} of choice_of_Type]          *)
(*                        (notation FC)                                       *)
(*   forget_choiceType := [the {functor CC -> CT} of idfun]                   *)
(*                        (notation UC)                                       *)
(*                epsC == counit FC \O UC ~> 1                                *)
(*                etaC == unit 1 ~> UC \O FC                                  *)
(* F0 -| U0:                                                                  *)
(*                  CV := [the category of convType]                          *)
(*                        (morphisms are affine functions)                    *)
(*       free_convType := [the {functor CC -> CV} of                          *)
(*                         (fun a : CC => [the convType of {dist a}])]        *)
(*                        (notation F0)                                       *)
(*     forget_convType := [the {functor CV -> CC} of idfun]                   *)
(*                eps0 == counit F0 \O U0 ~> 1                                *)
(*                eta0 == unit 1 ~> U0 \O F0                                  *)
(*        triL0, triR0 == triangular laws                                     *)
(* F1 -| U1:                                                                  *)
(*                  CS := [the category of semiCompSemiLattConvType]          *)
(*                        the category of semi-complete semi-lattice convex   *)
(*                        spaces, morphisms are biglubmorph and affine        *)
(* free_semiCompSemiLattConvType := [the {functor CV -> CS} of                *)
(*                        (fun a : CV => {necset a})]]                        *)
(*                        (notation F1)                                       *)
(* forget_semiCompSemiLattConvType := [the {functor CS -> CV} of idfun]       *)
(*                        (notation U1)                                       *)
(*                eps1 == counit F1 \O U1 ~> FId                              *)
(*                eta1 == unit FId ~> U1 \O F1                                *)
(*        triL1, triR1 == triangular laws                                     *)
(*                                                                            *)
(*               join1 == eps1 : necset (necset C) -> necset C where C is a   *)
(*                        convType                                            *)
(*                        | F1                                                *)
(*        P_delta_left == | F0                                                *)
(*                        | FC                                                *)
(*                        | UC                                                *)
(*       P_delta_right == | U0                                                *)
(*                        | U1                                                *)
(*             P_delta == functor CT CT, P_delta_right \O P_delta_left.       *)
(*                 eps == P_delta_left \O P_delta_right ~> FId                *)
(*                 ret == FId ~> P_delta                                      *)
(*                join == P_delta \O P_delta ~> P_delta                       *)
(*                 gcm == geometrically convex monad in the context of        *)
(*                        monad.v                                             *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope proba_scope.
Local Open Scope category_scope.

Section choiceType_as_a_category.

HB.instance Definition _ :=
  isCategory.Build choiceType (fun x : choiceType => Choice.sort x)
    (fun _ _ _ => True) (fun=> I) (fun _ _ _ _ _ _ _ => I).

Definition hom_choiceType
           (a b : [the category of choiceType]) (f : a -> b) : {hom a, b} :=
  Hom.Pack (Hom.Class (isHom.Axioms_ a b f I)).

End choiceType_as_a_category.
Notation CC := [the category of choiceType].

Require monad_model.
Section free_choiceType_functor.
Local Notation m := monad_model.choice_of_Type.

Definition free_choiceType_mor (T U : CT) (f : {hom T, U}) :
  {hom m T, m U} := hom_choiceType (f : m T -> m U).

Let free_choiceType_mor_id : FunctorLaws.id free_choiceType_mor.
Proof. by move=> a; rewrite hom_ext. Qed.

Let free_choiceType_mor_comp : FunctorLaws.comp free_choiceType_mor.
Proof. by move=> a b c g h; rewrite hom_ext. Qed.

HB.instance Definition _ := isFunctor.Build CT CC _
  free_choiceType_mor_id free_choiceType_mor_comp.

Definition free_choiceType := [the {functor CT -> CC} of m].

Lemma free_choiceType_mor_comp_fun (a b c : Type) (g : {hom b, c})
      (h : {hom a, b}):
  free_choiceType_mor [hom g \o h] =
  (free_choiceType_mor g) \o (free_choiceType_mor h) :> (_ -> _).
Proof. by rewrite free_choiceType_mor_comp. Qed.

End free_choiceType_functor.

Section forget_choiceType_functor.

Let m : CC -> CT := idfun.

Let h (a b : CC) (f : {hom a, b}) : {hom CT; m a, m b} :=
  Hom.Pack (Hom.Class (isHom.Axioms_ (a : CT) (b : _) (FId # f) I)).

Lemma h_id : FunctorLaws.id h. Proof. by move=> *; apply hom_ext. Qed.

Lemma h_comp : FunctorLaws.comp h. Proof. by move=> *; apply hom_ext. Qed.

HB.instance Definition _ := isFunctor.Build _ _ _ h_id h_comp.

Definition forget_choiceType := [the {functor CC -> CT} of m].

Lemma forget_choiceTypeE : (forall a : CC, forget_choiceType a = a) /\
  (forall (a b : CC) (f : {hom CC; a , b}), forget_choiceType # f = f :> (a -> b)).
Proof. by []. Qed.

End forget_choiceType_functor.

Section epsC_etaC.
Local Notation FC := free_choiceType.
Local Notation UC := forget_choiceType.

Let epsC' : FC \O UC ~~> FId := fun A : CC => Hom.Pack (Hom.Class
  (isHom.Axioms_ ((FC \O UC) A) (FId A) idfun I)).

Lemma epsC'_natural : naturality _ _ epsC'. Proof. by []. Qed.

HB.instance Definition _ := isNatural.Build _ _ _ _ _ epsC'_natural.

Definition epsC := locked [the _ ~> _ of epsC'].

Lemma epsCE (T : choiceType) : epsC T = idfun :> (_ -> _).
Proof. by rewrite /epsC; unlock. Qed.

Let etaC' : FId ~~> UC \O FC :=
      fun (_ : CT) => Hom.Pack (Hom.Class (isHom.Axioms_ (FId _) ((UC \O FC) _) idfun I)).

Lemma etaC'_natural : naturality _ _ etaC'.
Proof. by []. Qed.

HB.instance Definition _ := isNatural.Build _ _ _ _ _ etaC'_natural.

Definition etaC := locked [the _ ~> _ of etaC'].

Lemma etaCE (T : Type) : etaC T = idfun :> (_ -> _).
Proof. by rewrite /etaC; unlock. Qed.

Import comps_notation.

Lemma triLC : TriangularLaws.left etaC epsC.
Proof. by move=> c; rewrite etaCE epsCE. Qed.

Lemma triRC : TriangularLaws.right etaC epsC.
Proof. by move=> c; rewrite etaCE epsCE. Qed.

End epsC_etaC.

Section convType_as_a_category.
Local Obligation Tactic := idtac.

Let affine_idfun' (U : convType) : affine (@idfun U). Proof. by []. Qed.

Let affine_comp' (a b c : convType) (f : a -> b) (g : b -> c) :
  affine f -> affine g -> affine (g \o f).
Proof. by move=> hf hg ? ? ? /=; rewrite hf hg. Qed.

HB.instance Definition _ := isCategory.Build convType (fun A : convType => A)
  _ affine_idfun' affine_comp'.

End convType_as_a_category.
Notation CV := [the category of convType].

Section conv_hom_is_affine.

Fact conv_hom_is_affine (a b : CV) (f : {hom a, b}) : affine f.
Proof. by case: f=> ? [] []. Qed.

HB.instance Definition _ (A B : convType) (f : {hom A, B}) :=
  isAffine.Build _ _ _ (conv_hom_is_affine f).

End conv_hom_is_affine.

Section free_convType_functor.
Let acto (a : CC) : CV := [the convType of {dist a}].

Definition free_convType_mor (A B : CC) (f : {hom A, B})
    : {hom acto A, acto B} :=
  Hom.Pack (Hom.Class (isHom.Axioms_ (acto A) (acto B)
                                     (fsdistmap f) (fsdistmap_affine f))).

Lemma mem_finsupp_free_convType_mor (A B : CC) (f : A -> B)
    (d : {dist A}) (x : finsupp d) :
  f (fsval x) \in finsupp (free_convType_mor (hom_choiceType f) d).
Proof.
by rewrite /= supp_fsdistmap; apply/imfsetP => /=; exists (fsval x).
Qed.

(* free_convType_mor induces maps between supports *)
Definition free_convType_mor_supp
  (A B : CC) (f : A -> B(*{hom A , B}*)) (d : {dist A}) (x : finsupp d)
  : finsupp ((free_convType_mor (hom_choiceType f)) d) :=
  FSetSub (mem_finsupp_free_convType_mor f x).
Global Arguments free_convType_mor_supp [A B] f d.

Lemma fsval_free_convType_mor_supp (A B : choiceType) (f : {hom A , B}) d i :
  fsval (free_convType_mor_supp f d i) = f (fsval i).
Proof. by case: i. Qed.

Let free_convType_mor_id : FunctorLaws.id free_convType_mor.
Proof.
by move=> a; rewrite hom_ext funeqE=> x /=; rewrite fsdistmap_id.
Qed.

Let free_convType_mor_comp : FunctorLaws.comp free_convType_mor.
Proof. by move=> a b c g h; apply/hom_ext; exact: fsdistmap_comp. Qed.

HB.instance Definition _ :=
  isFunctor.Build CC CV acto free_convType_mor_id free_convType_mor_comp.

Definition free_convType := [the {functor CC -> CV} of acto].

Lemma free_convType_mor_comp_fun (A B C : CC) (g : {hom B, C}) (h : {hom A, B}) :
  free_convType_mor [hom g \o h] =
  (free_convType_mor g) \o (free_convType_mor h) :> (_ -> _).
Proof. by rewrite free_convType_mor_comp. Qed.

End free_convType_functor.

Section forget_convType_functor.

Let m1 : CV -> CC := idfun.

Let h1 := fun (a b : CV) (f : {hom CV; a, b}) =>
  Hom.Pack (Hom.Class (isHom.Axioms_ (m1 a) (m1 b) f I)).

Let h1_id : FunctorLaws.id h1. Proof. by move=> *; apply hom_ext. Qed.

Let h1_comp : FunctorLaws.comp h1. Proof. by move=> *; apply hom_ext. Qed.

HB.instance Definition _ := isFunctor.Build _ _ _ h1_id h1_comp.

Definition forget_convType := [the {functor CV -> CC} of m1].

Lemma forget_convTypeE : (forall a : CV, forget_convType a = a) /\
  (forall (a b : CV) (f : {hom CV; a , b}), forget_convType # f = f :> (a -> b)).
Proof. by []. Qed.

End forget_convType_functor.

(*
  eps0 is the counit of the adjunction (free_convType -| forget_convType), and
  it is essentially Convn (p.164).
*)
Section eps0_eta0.
Local Open Scope fset_scope.
Local Open Scope R_scope.
Local Open Scope convex_scope.
Local Notation F0 := free_convType.
Local Notation U0 := forget_convType.

Let eps0' : F0 \O U0 ~~> FId := fun a =>
  Hom.Pack (Hom.Class (isHom.Axioms_ ((F0 \O U0) a) (FId a)
    (@Convn_of_fsdist a) (@Convn_of_fsdist_affine (FId a)))).

Let eps0'_natural : naturality _ _ eps0'.
Proof.
move=> C D f; rewrite FCompE /= /id_f; apply funext => d /=.
by rewrite Convn_of_fsdistmap.
Qed.

HB.instance Definition _ := isNatural.Build _ _ _ _ _ eps0'_natural.
Definition eps0 := locked [the _ ~> _ of eps0'].

Lemma eps0E (C : convType) : eps0 C = @Convn_of_fsdist C :> (_ -> _).
Proof. by rewrite /eps0; unlock. Qed.

Let eta0' : FId ~~> U0 \O F0 := fun T =>
  Hom.Pack (Hom.Class (isHom.Axioms_ (FId T) ((U0 \O F0) T) (@fsdist1 _) I)).

Lemma eta0'_natural : naturality _ _ eta0'.
Proof.
by move=> a b h; rewrite funeqE=> x; rewrite FIdf /eta0' /= fsdistmap1.
Qed.

HB.instance Definition _ := isNatural.Build _ _ _ _ _ eta0'_natural.
Definition eta0 := locked [the _ ~> _ of eta0'].

Lemma eta0E (T : choiceType) : eta0 T = @fsdist1 _ :> (_ -> _).
Proof. by rewrite /eta0; unlock. Qed.

Import comps_notation.
Local Open Scope fset_scope.
Local Open Scope R_scope.

Lemma triL0 : TriangularLaws.left eta0 eps0.
Proof.
by move=> c; apply funext=> x /=; rewrite eps0E eta0E triangular_laws_left0.
Qed.

Lemma triR0 : TriangularLaws.right eta0 eps0.
Proof.
by move=> c; rewrite eps0E eta0E funeqE => a /=; rewrite Convn_of_fsdist1.
Qed.

End eps0_eta0.

(* the join operator for Dist is ((coercion) \o eps0) *)
Section eps0_correct.
Import category.
Local Open Scope R_scope.
Local Open Scope convex_scope.
Variables (A : choiceType) (D : {dist {dist A}}).

Lemma eps0_correct : eps0 _ D = fsdistjoin D.
Proof. by rewrite eps0E Convn_of_fsdistjoin. Qed.

End eps0_correct.

Section semiCompSemiLattConvType_as_a_category.
Import category.
Local Obligation Tactic := idtac.

Definition biglub_affine (a b : semiCompSemiLattConvType) (f : a -> b) :=
  biglubmorph f /\ affine f.

Let comp_is_biglub_affine (a b c : semiCompSemiLattConvType)
    (f : a -> b) (g : b -> c) :
  biglub_affine f -> biglub_affine g -> biglub_affine (g \o f).
Proof.
move=> [bf af] [bg ag]; split => x/=.
  rewrite bf bg/=;congr (biglub _).
  by apply/neset_ext => /=; rewrite image_comp.
by move=> ? ? /=; rewrite af ag.
Qed.

Let idfun_is_biglub_affine (a : semiCompSemiLattConvType) :
  biglub_affine (@idfun a).
Proof. by split => //; exact: biglub_morph. Qed.

HB.instance Definition _ := isCategory.Build semiCompSemiLattConvType
  (fun U : semiCompSemiLattConvType => U) biglub_affine idfun_is_biglub_affine
  comp_is_biglub_affine.

End semiCompSemiLattConvType_as_a_category.
Notation CS := [the category of semiCompSemiLattConvType].

Local Open Scope classical_set_scope.
Local Open Scope latt_scope.

Section scsl_hom_is_biglub_affine.
Import category.
Local Open Scope convex_scope.
Variables (K L : CS) (f : {hom K , L}).

Fact scsl_hom_is_biglub_affine : biglub_affine f.
Proof. by split; move=> ?; case: f=> ? [] [] []. Qed.

(* TODO: The following three lemmas should be inferred from the above one. *)
(* NB: HB.instance? *)
(* Canonical SCSL_hom_biglub_affine (A B : CS)
  (f : {hom A, B}) := BiglubAffine (scsl_hom_is_biglub_affine f). *)
Fact scsl_hom_is_affine : affine f.
Proof. by case: scsl_hom_is_biglub_affine. Qed.

(* NB(rei): this can actually maybe be removed *)
HB.instance Definition SCSL_hom_affine :=
  isAffine.Build _ _ _ scsl_hom_is_affine.
(* Canonical SCSL_hom_affine (K L : CS) (f : {hom K , L}) :=
  Affine (scsl_hom_is_affine f). *)

Fact scsl_hom_is_biglubmorph : biglubmorph f.
Proof. by case: scsl_hom_is_biglub_affine. Qed.

HB.instance Definition SCSL_hom_biglubmorph :=
  isBiglubMorph.Build _ _ _ scsl_hom_is_biglubmorph.
(* Canonical SCSL_hom_biglubmorph (K L : CS)
  (f : {hom K, L}) := BiglubMorph (scsl_hom_is_biglubmorph f). *)

Fact scsl_hom_is_lubmorph : lub_morph f. Proof. exact: biglub_lub_morph. Qed.

End scsl_hom_is_biglub_affine.

Section free_semiCompSemiLattConvType_functor.
Import category.
Local Open Scope convex_scope.

Let acto (a : CV) : CS := {necset a}.

(* the morphism part of necset *)
Section free_semiCompSemiLattConvType_mor.
Variables (A B : convType) (f : {hom A , B}).

Local Notation affine_f :=
  (Affine.Pack (Affine.Class (isAffine.Build _ _ _ (conv_hom_is_affine f)))).

Local Notation pack_imfx X := (NECSet.Pack (NECSet.Class
    (isConvexSet.Build _ _ (is_convex_set_image affine_f X))
    (isNESet.Build _ _ (neset_image_neq0 _ _)))).

Definition free_semiCompSemiLattConvType_mor' (X : acto A) : acto B := pack_imfx X.

(* the results of free_semiCompSemiLattConvType_mor are
   semiLattConvType-morphisms, i.e., are
   affine and preserve semilatt operations *)
Lemma free_semiCompSemiLattConvType_mor'_affine :
  affine free_semiCompSemiLattConvType_mor'.
Proof.
move=> p a0 a1; apply necset_ext => /=; rewrite predeqE => b0; split.
- case=> a [] a0' a0a0'; rewrite conv_pt_setE=> -[] a1' a1a1' <- <- /=.
  by rewrite affine_conv /=; exact: conv_in_conv_set.
- move=> /conv_in_conv_set' [] x [] y [] [] a0' a0a0' <- [] [] a1' a1a1' <- ->.
  rewrite affine_image_conv_set /=.
  by apply conv_in_conv_set; apply imageP.
Qed.

Lemma bigsetU_affine (X : neset (necset A)) : (f @` (\bigcup_(x in X) x) =
  \bigcup_(x in free_semiCompSemiLattConvType_mor' @` X) x)%classic.
Proof.
rewrite funeqE => b; rewrite propeqE; split.
- case => a [x Xx xa] <-{b}.
  exists (pack_imfx x) => /=; last by exists a.
  by exists x => //=; exact/necset_ext.
- by case => b0 [a0 Xa0 <-{b0}] [a a0a <-{b}]; exists a => //; exists a0.
Qed.

Lemma free_semiCompSemiLattConvType_mor'_biglub_morph :
  biglubmorph free_semiCompSemiLattConvType_mor'.
Proof.
move=> /= X; apply necset_ext => /=; rewrite funeqE => b.
by rewrite image_preserves_convex_hull bigsetU_affine.
Qed.

Definition free_semiCompSemiLattConvType_mor : {hom acto A, acto B} :=
  locked (Hom.Pack (Hom.Class (isHom.Axioms_
    (acto A) (acto B)
    free_semiCompSemiLattConvType_mor'
    (conj free_semiCompSemiLattConvType_mor'_biglub_morph
          free_semiCompSemiLattConvType_mor'_affine)))).

Lemma free_semiCompSemiLattConvType_morE (X : acto A) :
  free_semiCompSemiLattConvType_mor X = f @` X :> neset _.
Proof.
by rewrite /free_semiCompSemiLattConvType_mor; unlock; apply neset_ext.
Qed.

Lemma free_semiCompSemiLattConvType_morE' (X : acto A) :
  free_semiCompSemiLattConvType_mor X = f @` X :> set _.
Proof. by rewrite /free_semiCompSemiLattConvType_mor; unlock. Qed.

End free_semiCompSemiLattConvType_mor.

Lemma free_semiCompSemiLattConvType_mor_id :
  FunctorLaws.id free_semiCompSemiLattConvType_mor.
Proof.
move=> a; rewrite hom_ext funeqE=> /= x /=; apply necset_ext => /=.
by rewrite free_semiCompSemiLattConvType_morE' /= image_id.
Qed.

Lemma free_semiCompSemiLattConvType_mor_comp :
  FunctorLaws.comp free_semiCompSemiLattConvType_mor.
Proof.
move=> a b c [] g affine_g [] h affine_h; rewrite hom_ext funeqE => /= x /=.
apply necset_ext => /=.
rewrite 2!free_semiCompSemiLattConvType_morE' /= -image_comp.
by rewrite free_semiCompSemiLattConvType_morE'.
Qed.

HB.instance Definition _ := isFunctor.Build _ _ acto
  free_semiCompSemiLattConvType_mor_id free_semiCompSemiLattConvType_mor_comp.

(* F1 *)
Definition free_semiCompSemiLattConvType := [the {functor CV -> CS} of acto].

End free_semiCompSemiLattConvType_functor.

Section forget_semiCompSemiLattConvType_functor.

Let m2 : CS -> CV := idfun.

Let h2 := fun (a b : CS) (f : {hom CS; a, b}) => Hom.Pack (Hom.Class
  (isHom.Axioms_ (m2 a) (m2 b) f (scsl_hom_is_affine f))).

Let h2_id : FunctorLaws.id h2. Proof. by move=> *; apply hom_ext. Qed.

Let h2_comp : FunctorLaws.comp h2. Proof. by move=> *; apply hom_ext. Qed.

HB.instance Definition _ := isFunctor.Build _ _ m2 h2_id h2_comp.

Definition forget_semiCompSemiLattConvType := [the {functor CS -> CV} of m2].

Local Notation U1 := forget_semiCompSemiLattConvType.

(* TODO: document the removal of forget_semiCompSemiLattConvTypeE *)
(*
Lemma forget_semiCompSemiLattConvTypeE : (forall a : CS, forget_convType a = a)
  /\ (forall (a b : CS) (f : {hom CS; a , b}), U1 # f = f :> (a -> b)).
Proof. by []. Qed.
*)
End forget_semiCompSemiLattConvType_functor.

Section eps1_eta1.
Import category.
Local Open Scope classical_set_scope.
Local Open Scope convex_scope.
Local Notation F1 := free_semiCompSemiLattConvType.
Local Notation U1 := forget_semiCompSemiLattConvType.
Implicit Types L : semiCompSemiLattConvType.

Let eps1'' L := (fun X : {necset L} => |_| X).

Lemma eps1''_biglubmorph L : biglubmorph (@eps1'' L).
Proof.
move=> F.
transitivity (|_| (biglub @` ((fun X : {necset L} => (X : neset _)) @` F))%:ne).
  transitivity (|_| (hull (\bigcup_(x in F) x))%:ne).
    by congr (|_| _); apply neset_ext.
  by rewrite biglub_hull biglub_bigcup.
congr (|_| _).
apply/neset_ext; rewrite eqEsubset; split => x [] x0 Fx0 <-.
+ by case: Fx0 => x1 Fx1 <-; exists x1.
+ by exists x0 => // ; exists x0.
Qed.

Lemma eps1''_affine L : affine (@eps1'' L).
Proof.
move=> p X Y; rewrite -biglub_conv_setD.
by congr (|_| _%:ne); apply/neset_ext => /=.
Qed.

Let eps1' : F1 \O U1 ~~> FId := fun L => Hom.Pack (Hom.Class (isHom.Axioms_
  ((F1 \O U1) L) (FId L) (@eps1'' L)
  (conj (@eps1''_biglubmorph L) (@eps1''_affine L)))).

Lemma eps1'_natural : naturality _ _ eps1'.
Proof.
move=> K L f /=; rewrite funeqE => X /=.
rewrite biglub_morph; congr (|_| _).
by rewrite free_semiCompSemiLattConvType_morE.
Qed.

HB.instance Definition _ := isNatural.Build _ _ _ _ _ eps1'_natural.

Definition eps1 := locked [the _ ~> _ of eps1'].

Lemma eps1E (L : semiCompSemiLattConvType) :
  eps1 L = (fun X => |_| X) :> (_ -> _).
Proof. by rewrite /eps1; unlock. Qed.

Lemma necset1_affine (C : convType) : affine (set1 : C -> necset C).
Proof.
move=> p a b /=; apply/necset_ext; rewrite eqEsubset; split=> x /=.
- move->; rewrite necset_convType.convE.
  by apply conv_in_conv_set.
- by case/conv_in_conv_set'=> a0 [] b0 [] -> [] -> ->.
Qed.

Let eta1' : FId ~~> U1 \O F1 := fun C => Hom.Pack (Hom.Class
  (isHom.Axioms_ (FId C) ((U1 \O F1) C) set1 (@necset1_affine C))).

Lemma eta1'_natural : naturality _ _ eta1'.
Proof.
move=> a b h; rewrite funeqE => x; apply necset_ext => /=.
by rewrite free_semiCompSemiLattConvType_morE' /= image_set1.
Qed.

HB.instance Definition _ := isNatural.Build _ _ _ _ _ eta1'_natural.

Definition eta1 := locked [the _ ~> _ of eta1'].

Lemma eta1E (C : convType) : eta1 C = (set1 : C -> necset C) :> (_ -> _).
Proof. by rewrite /eta1; unlock. Qed.

Import comps_notation.

Lemma triL1 : TriangularLaws.left eta1 eps1.
Proof.
move=> c; apply funext => x /=; apply/necset_ext => /=.
rewrite eps1E /= free_semiCompSemiLattConvType_morE' /=.
rewrite -[in RHS](hull_cset x); congr hull.
rewrite eqEsubset eta1E; split=> a.
- by case=> y [] b xb <- ->.
- by move=> xa; exists [set a]; [exists a | ].
Qed.

Lemma triR1 : TriangularLaws.right eta1 eps1.
Proof. by move=> c; apply funext=> /= x; rewrite eps1E eta1E /= biglub1. Qed.

End eps1_eta1.

Section join1.
Import category.
Local Open Scope convex_scope.
Local Open Scope classical_set_scope.
Variable C : convType.

Definition join1' (s : necset (necset C)) : {convex_set C} :=
  ConvexSet.Pack (ConvexSet.Class (isConvexSet.Build C _
    (hull_is_convex (\bigcup_(x in s) if x \in s then x : set _ else set0)))).

Lemma join1'_neq0 (s : necset {necset C}) : join1' s != set0 :> set _.
Proof.
rewrite hull_eq0 set0P.
case/set0P: (neset_neq0 s) => y.
case/set0P: (neset_neq0 y) => x yx sy.
by exists x; exists y => //; move: sy; rewrite -in_setE => ->.
Qed.

Definition join1 (s : necset {necset C}) : necset C :=
  NECSet.Pack (NECSet.Class (isConvexSet.Build _ _ (hull_is_convex _))
                            (isNESet.Build _ _ (join1'_neq0 s))).

Lemma eps1_correct (s : necset {necset C}) : @eps1 _ s = join1 s.
Proof.
rewrite eps1E; apply/necset_ext => /=; congr (hull _).
rewrite /bigcup; rewrite funeqE => c; rewrite propeqE; split.
- by case=> X sX Xc; exists X => //; rewrite -in_setE in sX; rewrite sX.
- case=> X sX; rewrite -in_setE in sX; rewrite sX => Xc; exists X => //.
  by rewrite -in_setE.
Qed.

End join1.

Section P_delta_functor.
Import category.

Definition P_delta_left :=
  free_semiCompSemiLattConvType \O free_convType \O free_choiceType.

Definition P_delta_right :=
  forget_choiceType \O forget_convType \O forget_semiCompSemiLattConvType.

(* action on objects *)
Definition P_delta_acto (T : Type) : Type := P_delta_left T.

Definition P_delta : {functor CT -> CT} := P_delta_right \O P_delta_left.

Lemma P_deltaE (A B : Type) (f : {hom A, B}) :
  P_delta # f = P_delta_left # f :> (_ -> _).
Proof. exact: funext. Qed.

Lemma eps0_Dist1 (A : Type) (d : P_delta_acto A) : eps0 _ (fsdist1 d) = d.
Proof. by rewrite eps0E Convn_of_fsdist1. Qed.

End P_delta_functor.

(* TODO: move? *)
Require monad_lib.
Require Import hierarchy.

Local Notation choice_of_Type := monad_model.choice_of_Type.

Section P_delta_category_monad.
Import category.
Definition AC := AdjointFunctors.mk triLC triRC.
Definition A0 := AdjointFunctors.mk triL0 triR0.
Definition A1 := AdjointFunctors.mk triL1 triR1.
Definition Aprob := adj_comp AC A0.
Definition Agcm := adj_comp Aprob A1.
Definition Mgcm := Monad_of_adjoint_functors Agcm.
Definition gcm :=
  [the hierarchy.Monad.Exports.monad of Monad_of_category_monad.acto Mgcm].

Section gcm_opsE.
Import hierarchy.

Lemma gcm_retE (T : Type) (x : choice_of_Type T) :
  Ret x = [set (fsdist1 x)] :> gcm T.
Proof.
rewrite /= /ret_ /Monad_of_category_monad.ret /=.
rewrite !HCompId !HIdComp /=.
rewrite /id_f /= /etaC.
unlock => /=.
by rewrite eta0E eta1E.
Qed.

Local Notation F1 := free_semiCompSemiLattConvType.
Local Notation F0 := free_convType.
Local Notation FC := free_choiceType.
Local Notation UC := forget_choiceType.
Local Notation U0 := forget_convType.
Local Notation U1 := forget_semiCompSemiLattConvType.

Variables (T : Type) (X : gcm (gcm T)).

Import category.
Local Open Scope convex_scope.

Lemma gcm_joinE : Join X = necset_join X.
Proof.
apply/necset_ext.
rewrite /= /join_ /= /Monad_of_category_monad.join /= !HCompId !HIdComp eps1E.
rewrite functor_o NEqE functor_id compfid.
rewrite 2!VCompE_nat HCompId HIdComp.
set E := epsC _; have->: E = [hom idfun] by apply/hom_ext; rewrite epsCE.
rewrite functor_id_hom.
rewrite !functor_o functor_id !compfid.
set F1J := F1 # _.
have-> : F1J = @necset_join.F1join0 _ :> (_ -> _).
- apply funext=> x; apply necset_ext=> /=.
  rewrite /F1J /= /necset_join.F1join0' /=.
  cbn.
  rewrite /free_semiCompSemiLattConvType_mor; unlock=> /=.
  by rewrite eps0E.
congr hull; apply: classical_sets.eq_bigcup; first by rewrite -eqEsubset.
by move=> x nXx; case: ifPn => // /negP; rewrite in_setE.
Qed.

End gcm_opsE.
End P_delta_category_monad.

Require proba_monad_model.

Section probMonad_out_of_F0U0.
Import category.
(* probability monad built directly *)
Definition M := proba_monad_model.MonadProbModel.t.
(* probability monad built using adjunctions *)
Definition N := [the hierarchy.Monad.Exports.monad of
  Monad_of_category_monad.acto (Monad_of_adjoint_functors Aprob)].

Lemma actmE T : N T = M T. Proof. by []. Qed.

Import comps_notation hierarchy.
Local Open Scope monae_scope.

Lemma JoinE T : (Join : (N \o N) T -> N T) = (Join : (M \o M) T -> M T).
Proof.
apply funext => t /=.
rewrite /join_.
rewrite [in LHS]/= HCompId HIdComp [X in _ (X t)]/=.
rewrite /actm [in LHS]/=.
rewrite epsCE.
rewrite eps0_correct.
rewrite /fsdistjoin /fsdistmap /= fsdistbindA /=.
congr fsdistbind.
by apply funext => x; rewrite fsdist1bind.
Qed.

Lemma RetE T : (Ret : idfun T -> N T) = (Ret : FId T -> M T).
Proof.
apply funext => t /=.
rewrite /ret_.
rewrite [in LHS]/=.
by rewrite HCompId HIdComp [X in _ (X t)]/= eta0E etaCE.
Qed.

End probMonad_out_of_F0U0.
