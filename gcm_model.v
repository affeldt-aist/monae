(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2020 monae authors, license: LGPL-2.1-or-later               *)
Require Import Reals.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import boolp classical_sets.
From mathcomp Require Import finmap.
From infotheo Require Import Reals_ext classical_sets_ext Rbigop ssrR.
From infotheo Require Import fdist fsdist convex necset.
Require Import monae_lib.
From HB Require Import structures.
Require category.

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
(* choiceType_category == the category of Type, notation CC                   *)
(*     free_choiceType == functor CT CC, notation FC (= choice_of_Type)       *)
(*   forget_choiceType == functor CC CT, notation UC                          *)
(*                epsC == counit FC \O UC ~> 1                                *)
(*                etaC == unit 1 ~> UC \O FC                                  *)
(* F0 -| U0:                                                                  *)
(*   convType_category == the category of convType, morphisms are affine      *)
(*                        functions, notation CV                              *)
(*       free_convType == functor CC CV, notation F0 (= FSDist)               *)
(*     forget_convType == functor CV CC                                       *)
(*                eps0 == counit F0 \O U0 ~> 1                                *)
(*                eta0 == unit 1 ~> U0 \O F0                                  *)
(*        triL0, triR0 == triangular laws                                     *)
(* F1 -| U1:                                                                  *)
(* semiCompSemiLattConvType_category == the category of semi-complete         *)
(*                          semi-lattice convex spaces, notation CS           *)
(* free_semiCompSemiLattConvType == functor CV CS, notation F1 (= necset)     *)
(* forget_semiCompSemiLattConvType == functor CS CV, notation U1              *)
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

Section TODO_move_to_other_file.
Section misc_convex.
Local Open Scope convex_scope.
Variables (A : convType).

Lemma eq_dep_convn n (g : 'I_n -> A) (d : {fdist 'I_n})
      n0 (g0 : 'I_n0 -> A) (d0 : {fdist 'I_n0}) (Hn : n = n0)
      (Hg : eq_rect n (fun m => 'I_m -> A) g n0 Hn = g0)
      (Hd : eq_rect n (fun m => {fdist 'I_m}) d n0 Hn = d0) :
  <|>_d g = <|>_d0 g0.
Proof.
refine (match Hd with erefl => _ end).
refine (match Hg with erefl => _ end).
refine (match Hn with erefl => _ end).
reflexivity.
Qed.

Lemma convn1Eq' n (g : 'I_n -> A) (d : {fdist 'I_n}) (Hn1 : n = 1) :
  <|>_d g = eq_rect n (fun n => 'I_n -> A) g 1 Hn1 ord0.
Proof.
set d' := eq_rect n (fun n0 => {fdist 'I_n0}) d 1 Hn1.
set g' := eq_rect n (fun n0 => 'I_n0 -> A) g 1 Hn1.
suff -> : <|>_d g = <|>_d' g' by rewrite convn1E.
by eapply eq_dep_convn.
Qed.

Lemma convn1Eq n (g : 'I_n -> A) (d : {fdist 'I_n})
      (Hn1 : n = 1) (i : 'I_n) : <|>_d g = g i.
Proof.
rewrite convn1Eq'.
have-> /= : eq_rect n (fun n0 : nat => 'I_n0 -> A) g 1 Hn1 =
            g \o eq_rect 1 (fun n0 => 'I_1 -> 'I_n0) idfun n (esym Hn1)
  by subst n.
have /(_ i) I_n_contr : forall a b : 'I_n, a = b
    by rewrite Hn1=> a b; rewrite (ord1 a) (ord1 b).
by rewrite -(I_n_contr ((eq_rect 1 (fun n0 : nat => 'I_1 -> 'I_n0) idfun n (esym Hn1) ord0))).
Qed.
Global Arguments convn1Eq [n g d Hn1].
End misc_convex.
End TODO_move_to_other_file.

Local Open Scope category_scope.

Section choiceType_as_a_category.
Import category.
Definition choiceType_category_mixin : Category.mixin_of choiceType :=
  @Category.Mixin choiceType (fun x : choiceType => Choice.sort x)
    (fun _ _ _ => True) (fun=> I) (fun _ _ _ _ _ _ _ => I).
Canonical choiceType_category := Category.Pack choiceType_category_mixin.
Definition hom_choiceType (A B : choiceType) (f : A -> B) : {hom A, B} :=
  HomPack A B f I.
End choiceType_as_a_category.

Notation CC := choiceType_category.

Section free_choiceType_functor.
Import category.
Local Notation m := choice_of_Type.

Definition free_choiceType_mor (T U : CT) (f : {hom T, U}) :
  {hom m T, m U} := hom_choiceType (f : m T -> m U).

Lemma free_choiceType_mor_id : FunctorLaws.id free_choiceType_mor.
Proof. by move=> a; rewrite hom_ext. Qed.

Lemma free_choiceType_mor_comp : FunctorLaws.comp free_choiceType_mor.
Proof. by move=> a b c g h; rewrite hom_ext. Qed.

Definition free_choiceType : {functor CT -> CC} :=
  Functor free_choiceType_mor_id free_choiceType_mor_comp.

Lemma free_choiceType_mor_comp_fun (a b c : Type) (g : {hom b, c})
      (h : {hom a, b}):
  free_choiceType_mor [hom g \o h] =
  (free_choiceType_mor g) \o (free_choiceType_mor h) :> (_ -> _).
Proof. by rewrite free_choiceType_mor_comp. Qed.

Let h (a b : CC) (f : {hom a, b}) : {hom CT; a, b} :=
  HomPack (a : CT) (b : _) (FId # f) I.

Lemma h_id : FunctorLaws.id h. Proof. by move=> *; apply hom_ext. Qed.

Lemma h_comp : FunctorLaws.comp h. Proof. by move=> *; apply hom_ext. Qed.

Definition forget_choiceType : {functor CC -> CT} := Functor h_id h_comp.

Lemma forget_choiceTypeE :
  (forall a : CC, forget_choiceType a = a)
  /\ (forall (a b : CC) (f : {hom CC; a , b}), forget_choiceType # f = f :> (a -> b)).
Proof. by []. Qed.

End free_choiceType_functor.

Section epsC_etaC.
Import category.
Local Notation FC := free_choiceType.
Local Notation UC := forget_choiceType.

Let epsC' : FC \O UC ~~> FId := fun A : CC => HomPack ((FC \O UC) A) (FId A) idfun I.

Lemma epsC'_natural : naturality _ _ epsC'.
Proof. by []. Qed.

Definition epsC : FC \O UC ~> FId := locked (Natural epsC'_natural).

Lemma epsCE (T : choiceType) : epsC T = idfun :> (_ -> _).
Proof. by rewrite /epsC; unlock. Qed.

Let etaC' : FId ~~> UC \O FC := fun (_ : CT) => HomPack (FId _) ((UC \O FC) _) idfun I.

Lemma etaC'_natural : naturality _ _ etaC'.
Proof. by []. Qed.

Definition etaC : FId ~> UC \O FC := locked (Natural etaC'_natural).

Lemma etaCE (T : Type) : etaC T = idfun :> (_ -> _).
Proof. by rewrite /etaC; unlock. Qed.

Import comps_notation.
Lemma triLC : TriangularLaws.left etaC epsC.
Proof. by move=> c; rewrite etaCE epsCE. Qed.
Lemma triRC : TriangularLaws.right etaC epsC.
Proof. by move=> c; rewrite etaCE epsCE. Qed.
End epsC_etaC.

Section convType_as_a_category.
Import category.
Local Obligation Tactic := idtac.
Program Definition convType_category_mixin : Category.mixin_of convType :=
  @Category.Mixin convType (fun A : convType => A) Affine.axiom idfun_is_affine _.
Next Obligation.
by move=> ? ? ? f g af ag; exact: (comp_is_affine (Affine ag) (Affine af)).
Qed.
Canonical convType_category := Category.Pack convType_category_mixin.
End convType_as_a_category.

Notation CV := convType_category.

Section free_convType_functor.
Import category.

Definition free_convType_mor (A B : CC) (f : {hom A, B}) : {hom {dist A}, {dist B}} :=
  HomPack {dist A} {dist B} (FSDistfmap f) (FSDistfmap_affine f).

Lemma mem_finsupp_free_convType_mor (A B : CC) (f : A -> B)
    (d : {dist A}) (x : finsupp d) :
  f (fsval x) \in finsupp (free_convType_mor (hom_choiceType f) d).
Proof.
rewrite /= FSDistBind.supp imfset_id.
apply/bigfcupP; exists (FSDist1.d (f (fsval x))).
- by rewrite andbT; exact/in_imfset/fsvalP.
- by rewrite mem_finsupp FSDist1.dE inE eqxx; exact/eqP/R1_neq_R0.
Qed.

(* free_convType_mor induces maps between supports *)
Definition free_convType_mor_supp
  (A B : CC) (f : A -> B(*{hom A , B}*)) (d : {dist A}) (x : finsupp d)
  : [finType of finsupp ((free_convType_mor (hom_choiceType f)) d)] :=
  FSetSub (mem_finsupp_free_convType_mor f x).
Global Arguments free_convType_mor_supp [A B] f d.
Lemma fsval_free_convType_mor_supp (A B : choiceType) (f : {hom A , B}) d i :
  fsval (free_convType_mor_supp f d i) = f (fsval i).
Proof. by case: i. Qed.

Lemma free_convType_mor_id : FunctorLaws.id free_convType_mor.
Proof.
by move=> a; rewrite hom_ext funeqE=> x /=; rewrite/idfun FSDistfmap_id.
Qed.
Lemma free_convType_mor_comp : FunctorLaws.comp free_convType_mor.
Proof. by move=> a b c g h; rewrite hom_ext /= FSDistfmap_comp. Qed.

Definition free_convType : {functor CC -> CV} :=
  Functor free_convType_mor_id free_convType_mor_comp.

Lemma free_convType_mor_comp_fun (A B C : CC) (g : {hom B, C}) (h : {hom A, B}) :
  free_convType_mor [hom g \o h] =
  (free_convType_mor g) \o (free_convType_mor h) :> (_ -> _).
Proof. by rewrite free_convType_mor_comp. Qed.

Let m1 : CV -> CC := idfun.
Let h1 := fun (a b : CV) (f : {hom CV; a, b}) => HomPack (m1 a) (m1 b) f I.
Lemma h1_id : FunctorLaws.id h1. Proof. by move=> *; apply hom_ext. Qed.
Lemma h1_comp : FunctorLaws.comp h1. Proof. by move=> *; apply hom_ext. Qed.
Definition forget_convType : {functor CV -> CC} :=
  Functor h1_id h1_comp.
Lemma forget_convTypeE :
  (forall a : CV, forget_convType a = a)
  /\ (forall (a b : CV) (f : {hom CV; a , b}), forget_convType # f = f :> (a -> b)).
Proof. by []. Qed.
End free_convType_functor.

(*
  eps0 is the counit of the adjunction (free_convType -| forget_convType), and
  it is essentially Convn (p.164).
*)
Section eps0_eta0.
Import category.

Fact hom_affine (A B : convType) (f : {hom A, B}) : affine f.
Proof. by case: f. Qed.
Canonical Affine_hom_affine (A B : convType) (f : {hom A, B}) :=
  Affine (hom_affine f).

Import ScaledConvex.
Local Open Scope fset_scope.
Local Open Scope R_scope.
Local Open Scope convex_scope.
Local Notation F0 := free_convType.
Local Notation U0 := forget_convType.

Let eps0' : F0 \O U0 ~~> FId :=
  fun a => HomPack ((F0 \O U0) a) (FId a) (@Convn_of_FSDist a) (@Convn_of_FSDist_affine (FId a)).

Let eps0'_natural : naturality _ _ eps0'.
Proof.
move=> C D f; rewrite FCompE /= /id_f; apply funext => d /=.
by rewrite Convn_of_FSDist_FSDistfmap.
Qed.

Definition eps0 : F0 \O U0 ~> FId := locked (Natural eps0'_natural).

Lemma eps0E (C : convType) : eps0 C = @Convn_of_FSDist C :> (_ -> _).
Proof. by rewrite /eps0; unlock. Qed.

Let eta0' : FId ~~> U0 \O F0 :=
  fun T => HomPack (FId T) ((U0 \O F0) T) (fun x => FSDist1.d x) I.

Lemma eta0'_natural : naturality _ _ eta0'.
Proof.
by move=> a b h; rewrite funeqE=> x; rewrite FIdf /eta0' /= FSDistfmap1.
Qed.

Definition eta0 : FId ~> U0 \O F0 := locked (Natural eta0'_natural).

Lemma eta0E (T : choiceType) : eta0 T = @FSDist1.d _ :> (_ -> _).
Proof. by rewrite /eta0; unlock. Qed.

Import comps_notation.
Import ScaledConvex.
Local Open Scope fset_scope.
Local Open Scope R_scope.
Lemma triL0 : TriangularLaws.left eta0 eps0.
Proof.
by move=> c; apply funext=> x /=; rewrite eps0E eta0E triangular_laws_left0.
Qed.
Lemma triR0 : TriangularLaws.right eta0 eps0.
Proof.
by move=> c; rewrite eps0E eta0E funeqE => a /=; rewrite Convn_of_FSDist_FSDist1.
Qed.
End eps0_eta0.

(* the join operator for Dist is ((coercion) \o eps0) *)
Section eps0_correct.
Import category.
Import ScaledConvex.
Local Open Scope R_scope.
Variables (A : choiceType) (D : {dist {dist A}}).

Lemma eps0_correct : eps0 _ D = FSDistjoin D.
Proof.
rewrite /eps0; unlock=> /=; apply FSDist_ext => a; rewrite -[LHS]Scaled1RK.
rewrite (S1_proj_Convn_finType (Affine (FSDist_eval_affine a))) big_scaleR.
rewrite FSDistjoinE big_seq_fsetE; apply eq_bigr => -[d dD] _.
by rewrite (scaleR_scalept _ (FDist.ge0 _ _)) fdist_of_FSDistE Scaled1RK.
Qed.

End eps0_correct.

Section semiCompSemiLattConvType_as_a_category.
Import category.
Local Obligation Tactic := idtac.
Program Definition semiCompSemiLattConvType_category_mixin :
    Category.mixin_of semiCompSemiLattConvType :=
  @Category.Mixin semiCompSemiLattConvType (fun U : semiCompSemiLattConvType => U)
  BiglubAffine.class_of idfun_is_biglub_affine _.
Next Obligation.
move=> A B C f g bf bg.
exact: (comp_is_biglub_affine (BiglubAffine bg) (BiglubAffine bf)(*TODO: notation?*)).
Qed.
Canonical semiCompSemiLattConvType_category :=
  Category.Pack semiCompSemiLattConvType_category_mixin.
End semiCompSemiLattConvType_as_a_category.

Notation CS := semiCompSemiLattConvType_category.

Local Open Scope classical_set_scope.
Local Open Scope latt_scope.

Section hom_biglubmorph.
Import category.
Local Open Scope convex_scope.
Fact hom_biglubmorph (K L : semiCompSemiLattConvType) (f : {hom K , L}) :
  biglubmorph f.
Proof. by move=> X; case: f => f [?]. Qed.
Canonical BiglubMorph_hom_biglubmorph (A B : semiCompSemiLattConvType)
  (f : {hom A, B}) := BiglubMorph (hom_biglubmorph f).
End hom_biglubmorph.

Section free_semiCompSemiLattConvType_functor.
Import category.
Local Open Scope convex_scope.

(* the morphism part of necset *)
Section free_semiCompSemiLattConvType_mor.
Variables (A B : convType) (f : {hom A , B}).

Definition free_semiCompSemiLattConvType_mor' (X : {necset A}) : {necset B} :=
  NECSet.Pack (NECSet.Class
    (CSet.Mixin (is_convex_set_image [affine of f] X))
    (NESet.Mixin (neset_image_neq0 _ _))).

(* the results of free_semiCompSemiLattConvType_mor are
   semiLattConvType-morphisms, i.e., are
   affine and preserve semilatt operations *)
Lemma free_semiCompSemiLattConvType_mor'_affine :
  affine free_semiCompSemiLattConvType_mor'.
Proof.
move=> p a0 a1; apply necset_ext => /=; rewrite predeqE => b0; split.
- rewrite !necset_convType.convE.
  case=> a [] a0' a0a0'; rewrite conv_pt_setE=> -[] a1' a1a1' <- <- /=.
  by case: f=> f' /= ->; apply conv_in_conv_set; apply imageP.
- rewrite !necset_convType.convE => /conv_in_conv_set' [] x [] y [] [] a0' a0a0' <- [] [] a1' a1a1' <- ->.
  rewrite affine_image_conv_set /=.
  by apply conv_in_conv_set; apply imageP.
Qed.

Lemma bigsetU_affine (X : neset (necset A)) :
  (f @` (\bigcup_(x in X) x) =
    \bigcup_(x in free_semiCompSemiLattConvType_mor' @` X) x)%classic.
Proof.
rewrite funeqE => b; rewrite propeqE; split.
- case => a [x Xx xa] <-{b}.
  exists (NECSet.Pack (NECSet.Class
      (CSet.Mixin (is_convex_set_image [affine of f] x))
      (NESet.Mixin (neset_image_neq0 f x)))) => /=; last by exists a.
  by exists x => //=; exact/necset_ext.
- by case => b0 [a0 Xa0 <-{b0}] [a a0a <-{b}]; exists a => //; exists a0.
Qed.

Lemma free_semiCompSemiLattConvType_mor'_biglub_morph :
  biglubmorph free_semiCompSemiLattConvType_mor'.
Proof.
move=> /= X; apply necset_ext => /=; rewrite funeqE => b.
by rewrite image_preserves_convex_hull bigsetU_affine.
Qed.

Definition free_semiCompSemiLattConvType_mor : {hom {necset A}, {necset B}} :=
  locked (HomPack
    {necset A} {necset B}
    free_semiCompSemiLattConvType_mor'
    (BiglubAffine.Class free_semiCompSemiLattConvType_mor'_affine
                       free_semiCompSemiLattConvType_mor'_biglub_morph)).

Lemma free_semiCompSemiLattConvType_morE (X : necset A) :
  NECSet.mixinType (free_semiCompSemiLattConvType_mor X) = image_neset f X.
Proof.
by rewrite /free_semiCompSemiLattConvType_mor; unlock; apply neset_ext.
Qed.

Lemma free_semiCompSemiLattConvType_morE' (X : necset A) :
  NESet.car (NECSet.mixinType (free_semiCompSemiLattConvType_mor X)) = image_neset f X.
Proof. by rewrite /free_semiCompSemiLattConvType_mor; unlock. Qed.
End free_semiCompSemiLattConvType_mor.

Lemma free_semiCompSemiLattConvType_mor_id :
  FunctorLaws.id free_semiCompSemiLattConvType_mor.
Proof.
move=> a; rewrite hom_ext funeqE=> /= x /=.
apply necset_ext => /=.
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

Definition free_semiCompSemiLattConvType : {functor CV -> CS} :=
  Functor free_semiCompSemiLattConvType_mor_id
          free_semiCompSemiLattConvType_mor_comp.

Local Notation F1 := free_semiCompSemiLattConvType.

Lemma free_semiCompSemiLattConvType_mor_comp_fun (a b c : convType)
    (g : {hom b, c}) (h : {hom a, b}):
  (F1 # [hom g \o h]) = (F1 # g) \o (F1 # h) :> (_ -> _).
Proof. by rewrite /Actm /= free_semiCompSemiLattConvType_mor_comp. Qed.

Let m2 : CS -> CV := id.
Let h2 := fun (a b : CS) (f : {hom CS; a, b}) => HomPack (m2 a) (m2 b) f (BiglubAffine.base (Hom.class f)).
Lemma h2_id : FunctorLaws.id h2. Proof. by move=> *; apply hom_ext. Qed.
Lemma h2_comp : FunctorLaws.comp h2. Proof. by move=> *; apply hom_ext. Qed.
Definition forget_semiCompSemiLattConvType : {functor CS -> CV} :=
  Functor h2_id h2_comp.

Local Notation U1 := forget_semiCompSemiLattConvType.

Lemma forget_semiCompSemiLattConvTypeE : (forall a : CS, forget_convType a = a)
  /\ (forall (a b : CS) (f : {hom CS; a , b}), U1 # f = f :> (a -> b)).
Proof. by []. Qed.
End free_semiCompSemiLattConvType_functor.

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
transitivity (|_| (biglub @` ((fun X : {necset L} => (X : neset _)) @` F))%:ne); last first.
  congr (|_| _).
  apply/neset_ext; rewrite eqEsubset; split => x [] x0 Fx0 <-.
  + by case: Fx0 => x1 Fx1 <-; exists x1.
  + by exists x0 => // ; exists x0.
transitivity (|_| (hull (\bigcup_(x in F) x))%:ne).
  by congr (|_| _); apply neset_ext.
by rewrite biglub_hull biglub_bigcup.
Qed.

Lemma eps1''_affine L : affine (@eps1'' L).
Proof.
move=> p X Y; rewrite -biglub_conv_setD.
congr (|_| _%:ne); apply/neset_ext => /=.
by rewrite necset_convType.convE.
Qed.

Let eps1' : F1 \O U1 ~~> FId :=
  fun L => HomPack ((F1 \O U1) L) (FId L) (@eps1'' L)
    (BiglubAffine.Class (@eps1''_affine L) (@eps1''_biglubmorph L)).

Lemma eps1'_natural : naturality _ _ eps1'.
Proof.
move=> K L f /=; rewrite funeqE => X /=.
rewrite biglub_morph; congr (|_| _).
by rewrite free_semiCompSemiLattConvType_morE.
Qed.

Definition eps1 : F1 \O U1 ~> FId := locked (Natural eps1'_natural).

Lemma eps1E (L : semiCompSemiLattConvType) :
  eps1 L = (fun X => |_| X) :> (_ -> _).
Proof. by rewrite /eps1; unlock. Qed.

Lemma necset1_affine (C : convType) : affine (@necset1 C).
Proof.
move=> p a b /=; apply/necset_ext; rewrite eqEsubset; split=> x /=.
- move->; rewrite necset_convType.convE.
  by apply conv_in_conv_set.
- rewrite necset_convType.convE /necset1 /=.
  by case/conv_in_conv_set'=> a0 [] b0 [] -> [] -> ->.
Qed.

Let eta1' : FId ~~> U1 \O F1 :=
  fun C => HomPack (FId C) ((U1 \O F1) C) (@necset1 C) (@necset1_affine C).

Lemma eta1'_natural : naturality _ _ eta1'.
Proof.
move=> a b h; rewrite funeqE => x; apply necset_ext => /=.
by rewrite free_semiCompSemiLattConvType_morE' /= image_set1.
Qed.

Definition eta1 : FId ~> U1 \O F1 := locked (Natural eta1'_natural).

Lemma eta1E (C : convType) : eta1 C = @necset1 _ :> (_ -> _).
Proof. by rewrite /eta1; unlock. Qed.

Import comps_notation.

Lemma necset1E (T : convType) (t : T) : necset1 t = [set t] :> set T.
Proof. by []. Qed.

Lemma triL1 : TriangularLaws.left eta1 eps1.
Proof.
move=> c; apply funext => x /=; apply/necset_ext => /=.
rewrite eps1E /= free_semiCompSemiLattConvType_morE' /=.
rewrite -[in RHS](hull_cset x); congr hull.
rewrite eqEsubset eta1E; split=> a.
- by case=> y [] b xb <-; rewrite necset1E => ->.
- by move=> xa; exists (necset1 a); [exists a | rewrite necset1E].
Qed.

Lemma triR1 : TriangularLaws.right eta1 eps1.
Proof. by move=> c; apply funext=> /= x; rewrite eps1E eta1E /= biglub1. Qed.

End eps1_eta1.

Section join1.
Import category.
Local Open Scope convex_scope.
Local Open Scope classical_set_scope.
Variable C : convType.

Definition join1' (s : necset {necset C}) : {convex_set C} :=
  CSet.Pack (CSet.Mixin
    (hull_is_convex (classical_sets.bigsetU s (fun x => if x \in s then (x : set _) else cset0 _)))).

Lemma join1'_neq0 (s : necset {necset C}) : join1' s != set0 :> set _.
Proof.
rewrite hull_eq0 set0P.
case/set0P: (neset_neq0 s) => y.
case/set0P: (neset_neq0 y) => x yx sy.
by exists x; exists y => //; move: sy; rewrite -in_setE => ->.
Qed.

Definition join1 (s : necset {necset C}) : necset C :=
  NECSet.Pack (NECSet.Class (CSet.Mixin (hull_is_convex _))
                            (NESet.Mixin (join1'_neq0 s))).

Lemma eps1_correct (s : necset {necset C}) : @eps1 _ s = join1 s.
Proof.
rewrite eps1E; apply/necset_ext => /=; congr (hull _).
rewrite /bigsetU; rewrite funeqE => c; rewrite propeqE; split.
- by case=> X sX Xc; exists X => //; rewrite -in_setE in sX; rewrite sX.
- by case=> X sX; rewrite -in_setE in sX; rewrite sX => Xc; exists X => //; rewrite -in_setE.
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

Lemma eps0_Dist1 (A : Type) (d : P_delta_acto A) : eps0 _ (FSDist1.d d) = d.
Proof. by rewrite eps0E Convn_of_FSDist_FSDist1. Qed.
End P_delta_functor.

(* TODO: move *)
Require monad_lib.
Require Import hierarchy proba_hierarchy.

Section P_delta_category_monad.
Import category.
Definition AC := AdjointFunctors.mk triLC triRC.
Definition A0 := AdjointFunctors.mk triL0 triR0.
Definition A1 := AdjointFunctors.mk triL1 triR1.
Definition Aprob := adj_comp AC A0.
Definition Agcm := adj_comp Aprob A1.
Definition Mgcm := Monad_of_adjoint Agcm.
Definition gcm := [the hierarchy.monad of Monad_of_category_monad.acto Mgcm].

Section gcm_opsE.
Import hierarchy.

Lemma gcm_retE (T : Type) (x : choice_of_Type T) :
  Ret x = necset1 (FSDist1.d x) :> gcm T.
Proof.
rewrite /= /ret_ /Monad_of_category_monad.ret /= /Hom.apply /=.
rewrite !HCompId !HIdComp /=.
rewrite /id_f /= /etaC.
unlock => /=.
by rewrite eta0E eta1E.
Qed.

Section move_to_classical_sets_ext.
Lemma eq_bigcup_cond :
  forall (T U : Type) (P Q : set U) (X Y : U -> set T),
  P = Q -> (forall i, P i -> X i = Y i) ->
  \bigcup_(i in P) X i = \bigcup_(i in Q) Y i.
Proof.
move=> ? ? P Q X Y pq XY.
by rewrite eqEsubset; split=> x; case=> j; rewrite -?pq=> ?; rewrite -?XY // => ?;
  eexists j; rewrite -?pq // -XY //.
Qed.
End move_to_classical_sets_ext.

Local Notation F1 := free_semiCompSemiLattConvType.
Local Notation F0 := free_convType.
Local Notation FC := free_choiceType.
Local Notation UC := forget_choiceType.
Local Notation U0 := forget_convType.
Local Notation U1 := forget_semiCompSemiLattConvType.

Variables (T : Type) (X : gcm (gcm T)).

Lemma gcm_joinE : Join X = necset_join X.
Proof.
Import category.
Local Open Scope convex_scope.
apply/necset_ext.
rewrite /= /join_ /= /Monad_of_category_monad.join /= !HCompId !HIdComp eps1E.
rewrite functor_o NEqE functor_id compfid.
rewrite 2!VCompE_nat HCompId HIdComp.
set E := epsC _; have->: E = (homid0 _) by apply/hom_ext; rewrite epsCE.
rewrite functor_id_hom homfunK.
rewrite !functor_o functor_id !compfid /=.
set F1J := free_semiCompSemiLattConvType_mor _.
have-> : F1J = @necset_join.F1join0 _ :> (_ -> _).
- apply funext=> x; apply necset_ext=> /=.
  rewrite /F1J /= /necset_join.F1join0' /=.
  rewrite /free_semiCompSemiLattConvType_mor; unlock=> /=.
  by rewrite eps0E /=.
congr hull; apply eq_bigcup_cond=> //= x nXx.
by case/boolP: (x \in necset_join.F1join0 X)=> [|/negP]; rewrite in_setE.
Qed.

End gcm_opsE.
End P_delta_category_monad.

Require proba_monad_model.

Section probMonad_out_of_F0U0.
Import category.
(* probability monad built directly *)
Definition M := proba_monad_model.MonadProbModel.t.
(* probability monad built using adjunctions *)
Definition N :=
 [the hierarchy.monad of Monad_of_category_monad.acto (Monad_of_adjoint Aprob)].

Lemma actmE T : N T = M T.
Proof. by []. Qed.

Import comps_notation hierarchy.
Local Open Scope monae_scope.
Lemma JoinE T :
  (Join : (N \O N) T -> N T) = (Join : (M \O M) T -> M T).
Proof.
apply funext => t /=.
rewrite /join_.
rewrite [in LHS]/= HCompId HIdComp [X in _ (X t)]/=.
rewrite /Actm [in LHS]/=.
rewrite epsCE.
(* TODO: rewrite with FSDistfmap_id *)
rewrite eps0_correct.
rewrite /FSDistjoin /FSDistfmap /= FSDistBindA /=.
congr FSDistBind.d.
by apply funext => x; rewrite FSDistBind1f.
Qed.

Lemma RetE T : (Ret : FId T -> N T) = (Ret : FId T -> M T).
Proof.
apply funext => t /=.
rewrite /ret_.
rewrite [in LHS]/=.
by rewrite HCompId HIdComp [X in _ (X t)]/= eta0E etaCE.
Qed.
End probMonad_out_of_F0U0.
