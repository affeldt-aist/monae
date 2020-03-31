Require Import Reals.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import boolp classical_sets.
From mathcomp Require Import finmap.
From infotheo Require Import Reals_ext classical_sets_ext Rbigop ssrR ssr_ext.
From infotheo Require Import fdist fsdist convex_choice necset.
Require Import monae_lib.
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

Section choiceType_as_a_category.
Import category.
Definition choiceType_category_mixin : Category.mixin_of choiceType :=
  @Category.Mixin choiceType (fun x : choiceType => Choice.sort x)
    (fun _ _ _ => True) (fun=> I) (fun _ _ _ _ _ _ _ => I).
Canonical choiceType_category := Category.Pack choiceType_category_mixin.
Definition hom_choiceType (A B : choiceType) (f : A -> B) : {hom A, B} :=
  HomPack (I : InHom (f : El A -> El B)).
End choiceType_as_a_category.

Section free_choiceType_functor.
Import category.
Local Notation m := choice_of_Type.
Local Notation CC := choiceType_category.
Local Notation CT := Type_category.

Definition free_choiceType_mor (T U : CT) (f : {hom T, U}) :
  {hom m T, m U} := hom_choiceType (f : m T -> m U).
Lemma free_choiceType_mor_id : FunctorLaws.id free_choiceType_mor.
Proof. by move=> a; rewrite hom_ext. Qed.
Lemma free_choiceType_mor_comp : FunctorLaws.comp free_choiceType_mor.
Proof. by move=> a b c g h; rewrite hom_ext. Qed.
Definition free_choiceType : functor CT CC :=
  Functor.Pack (Functor.Mixin free_choiceType_mor_id free_choiceType_mor_comp).

Lemma free_choiceType_mor_comp_fun (a b c : Type) (g : {hom b, c})
      (h : {hom a, b}):
  [fun of free_choiceType_mor [hom of [fun of g] \o [fun of h]]] =
  [fun of free_choiceType_mor g] \o [fun of free_choiceType_mor h].
Proof. by rewrite free_choiceType_mor_comp. Qed.

Let h (a b : CC) (f : {hom CC; a, b}) : {hom CT; Choice.sort a , Choice.sort b} :=
  HomPack (I : InHom (FId # f : El (C:=CT) a -> El b)).
Lemma h_id : FunctorLaws.id h. Proof. by move=> *; apply hom_ext. Qed.
Lemma h_comp : FunctorLaws.comp h. Proof. by move=> *; apply hom_ext. Qed.
Definition forget_choiceType : functor CC CT :=
  Functor.Pack (Functor.Mixin h_id h_comp).
Lemma forget_choiceTypeE :
  (forall a : CC, forget_choiceType a = a)
  /\ (forall a b (f : {hom CC; a , b}), forget_choiceType # f = f :> (a -> b)).
Proof. by []. Qed.
End free_choiceType_functor.

Section epsC_etaC.
Import category.
Local Notation CC := choiceType_category.
Local Notation CT := Type_category.
Local Notation FC := free_choiceType.
Local Notation UC := forget_choiceType.
Definition epsC'' {T : choiceType} : FC T -> T := idfun.
Definition epsC' : FC \O UC ~~> FId :=
  fun T => @Hom.Pack CC _ _ _ (@epsC'' T) I.
Lemma epsC'_natural : naturality _ _ epsC'.
Proof. by []. Qed.
Definition epsC : FC \O UC ~> FId :=
  locked (Natural.Pack (Natural.Class epsC'_natural)).
Lemma epsCE (T : choiceType) : epsC T = idfun :> (_ -> _).
Proof. by rewrite /epsC; unlock. Qed.

Definition etaC': FId ~~> UC \O FC :=
  fun _ => @Hom.Pack CT _ _ _ idfun I.
Lemma etaC'_natural : naturality _ _ etaC'.
Proof. by []. Qed.
Definition etaC: FId ~> UC \O FC :=
  locked (Natural.Pack (Natural.Class etaC'_natural)).
Lemma etaCE (T : Type) : etaC T = idfun :> (_ -> _).
Proof. by rewrite /etaC; unlock. Qed.

Import homcomp_notation.
Lemma triLC : TriangularLaws.left etaC epsC.
Proof. by move=> c; rewrite etaCE epsCE. Qed.
Lemma triRC : TriangularLaws.right etaC epsC.
Proof. by move=> c; rewrite etaCE epsCE. Qed.
End epsC_etaC.

Section convType_as_a_category.
Import category.
Definition convType_category_mixin : Category.mixin_of convType :=
  @Category.Mixin convType (fun A : convType => A) AffineFunction.axiom
    affine_function_id_proof affine_function_comp_proof'.
Canonical convType_category := Category.Pack convType_category_mixin.
End convType_as_a_category.

Section free_convType_functor.
Import category.
Local Notation CC := choiceType_category.
Local Notation CV := convType_category.

(* morphism part of FSDist *)
Definition free_convType_mor (A B : choiceType) (f : {hom A, B}) :
  {hom FSDist_convType A, FSDist_convType B}.
refine (@Hom.Pack CV _ _ _ (FSDistfmap f) _).
(* TODO: try to use a variant of FSDistfmap_affine? *)
exact: (fun x y t => ConvFSDist.bind_left_distr t x y (fun a : A => FSDist1.d ([fun of f] a))).
Defined.

Lemma mem_finsupp_free_convType_mor (A B : choiceType) (f : A -> B) (d : {dist A}) (x : finsupp d) :
  f (fsval x) \in finsupp ([fun of free_convType_mor (hom_choiceType f)] d).
Proof.
rewrite /= FSDistBind.supp imfset_id.
apply/bigfcupP; exists (FSDist1.d (f (fsval x))).
- rewrite andbT.
  apply (in_imfset _ (fun x => FSDist1.d (f x))) => /=.
  exact/fsvalP.
- rewrite mem_finsupp FSDist1.dE inE eqxx; exact/eqP/R1_neq_R0.
Qed.

(* free_convType_mor induces maps between supports *)
Definition free_convType_mor_supp
  (A B : choiceType) (f : A -> B(*{hom A , B}*)) (d : {dist A}) (x : finsupp d)
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

Definition free_convType : functor CC CV :=
  Functor.Pack (Functor.Mixin free_convType_mor_id free_convType_mor_comp).

Lemma free_convType_mor_comp_fun (A B C : choiceType) (g : {hom B, C})
      (h : {hom A, B}):
  [fun of free_convType_mor [hom of [fun of g] \o [fun of h]]] =
  [fun of free_convType_mor g] \o [fun of free_convType_mor h].
Proof. by rewrite free_convType_mor_comp. Qed.

Let m1 : CV -> CC := idfun.
Let h1 := fun (a b : CV) (f : {hom CV; a, b}) =>
  @Hom.Pack CC a b _ f I : {hom CC; m1 a , m1 b}.
Lemma h1_id : FunctorLaws.id h1. Proof. by move=> *; apply hom_ext. Qed.
Lemma h1_comp : FunctorLaws.comp h1. Proof. by move=> *; apply hom_ext. Qed.
Definition forget_convType : functor CV CC :=
  Functor.Pack (Functor.Mixin h1_id h1_comp).
Lemma forget_convTypeE :
  (forall a : CV, forget_convType a = a)
  /\ (forall a b (f : {hom CV; a , b}), forget_convType # f = f :> (a -> b)).
Proof. by []. Qed.
End free_convType_functor.

(*
  eps0 is the counit of the adjunction (free_convType -| forget_convType), and
  it is just Convn (p.164).
*)
Section eps0_eta0.
Import category.
Import ScaledConvex.
Local Open Scope fset_scope.
Local Open Scope R_scope.
Local Open Scope convex_scope.
Local Notation F0 := free_convType.
Local Notation U0 := forget_convType.
Local Notation CC := choiceType_category.
Local Notation CV := convType_category.

Definition eps0'' {C : convType} (d : {dist C}) : C := Convn_of_FSDist d.

Lemma eps0''_affine (C : convType) : affine_function (@eps0'' C).
Proof. exact: Convn_of_FSDist_affine. Qed.

Lemma eps0''_natural (C D : convType) (f : {hom C, D}) :
  f \o eps0'' = eps0'' \o (F0 \O U0) # f.
Proof.
rewrite FCompE /= /id_f /eps0''; apply funext => d /=.
rewrite Convn_of_FSDist_FSDistfmap //; by case: f.
Qed.

Definition eps0' : F0 \O U0 ~~> FId :=
  fun a => @Hom.Pack CV _ _ _ eps0'' (eps0''_affine (C := FId a)).

Lemma eps0'E (C : convType) (d : {dist C}) : eps0' C d = Convn_of_FSDist d.
Proof. by []. Qed.

Lemma eps0'_natural : naturality _ _ eps0'.
Proof. by move=> C D f; rewrite eps0''_natural. Qed.

Definition eps0 : F0 \O U0 ~> FId :=
  locked (Natural.Pack (Natural.Class eps0'_natural)).

Lemma eps0E (C : convType) : eps0 C = Convn_of_FSDist (C:=C) :> (_ -> _).
Proof. by rewrite /eps0; unlock. Qed.

Definition eta0' : FId ~~> U0 \O F0 :=
  fun C => @Hom.Pack CC _ _ _ (fun x : C => FSDist1.d x) I.
Lemma eta0'_natural : naturality _ _ eta0'.
Proof.
by move=> a b h; rewrite funeqE=> x; rewrite FIdf /eta0' /= FSDistfmap1.
Qed.

Definition eta0 : FId ~> U0 \O F0 :=
  locked (Natural.Pack (Natural.Class eta0'_natural)).
Lemma eta0E' : eta0 = Natural eta0'_natural.
Proof. by rewrite /eta0; unlock. Qed.
Lemma eta0E (T : choiceType) : eta0 T = (@FSDist1.d _) :> (_ -> _).
Proof. by rewrite /eta0; unlock. Qed.

Import homcomp_notation.
Import ScaledConvex.
Local Open Scope fset_scope.
Local Open Scope R_scope.
Lemma triL0 : TriangularLaws.left eta0 eps0.
Proof.
by move=> c; apply funext=> x /=; rewrite eps0E eta0E triangular_laws_left0.
Qed.
Lemma triR0 : TriangularLaws.right eta0 eps0.
Proof.
move=> c; by rewrite eps0E eta0E funeqE => a /=; rewrite Convn_of_FSDist_FSDist1.
Qed.
End eps0_eta0.

(* the join operator for Dist is ((coercion) \o eps0) *)
Section eps0_correct.
Import category.
Import ScaledConvex.
Local Open Scope R_scope.
Variables (A : choiceType) (D : {dist {dist A}}).

Let eps0''_correct  : eps0'' D = FSDistjoin D.
Proof.
apply FSDist_ext => a; rewrite -[LHS]Scaled1RK /eps0''.
rewrite (S1_proj_Convn_finType (FSDist_eval_affine a)) big_scaleR.
rewrite FSDistjoinE big_seq_fsetE; apply eq_bigr => -[d dD] _.
by rewrite (scaleR_scalept _ (FDist.ge0 _ _)) fdist_of_FSDistE Scaled1RK.
Qed.

Lemma eps0_correct : eps0 _ D = FSDistjoin D.
Proof. rewrite /eps0; unlock=> /=; exact: eps0''_correct. Qed.
End eps0_correct.

Section semiCompSemiLattConvType_as_a_category.
Import category.
Definition semiCompSemiLattConvType_category_mixin :
    Category.mixin_of semiCompSemiLattConvType :=
  @Category.Mixin semiCompSemiLattConvType (fun U : semiCompSemiLattConvType => U)
  LubOpAffine.class_of lub_op_affine_id_proof lub_op_affine_comp_proof.
Canonical semiCompSemiLattConvType_category :=
  Category.Pack semiCompSemiLattConvType_category_mixin.
End semiCompSemiLattConvType_as_a_category.

Local Open Scope classical_set_scope.

Local Open Scope latt_scope.

Section apply_affine.
Import category.
Lemma apply_affine (K L : semiCompSemiLattConvType) (f : {hom K , L})
  (X : necset_semiCompSemiLattConvType K) :
  f (|_| X) = |_| (f @` X)%:ne.
Proof. by case: f => f [? /= ->]. Qed.
End apply_affine.

Section free_semiCompSemiLattConvType_functor.
Import category.
Local Open Scope convex_scope.
Local Notation CV := convType_category.
Local Notation CS := semiCompSemiLattConvType_category.

Lemma hom_affine_function (A B : convType) (f : {hom A, B}) : affine_function [fun of f].
Proof. by case: f. Qed.

(* the morphism part of necset *)
Section free_semiCompSemiLattConvType_mor.
Variables (A B : convType) (f : {hom A , B}).

Definition free_semiCompSemiLattConvType_mor' (X : necset_convType A) :
  necset_convType B :=
  NECSet.Pack (NECSet.Class
    (CSet.Class (is_convex_set_image' (hom_affine_function f) X))
    (NESet.Mixin (neset_image_neq0 _ _))).

(* the results of free_semiCompSemiLattConvType_mor are
   semiLattConvType-morphisms, i.e., are
   affine and preserve semilatt operations *)
Lemma free_semiCompSemiLattConvType_mor'_affine :
  affine_function free_semiCompSemiLattConvType_mor'.
Proof.
move=> a0 a1 p; apply necset_ext => /=; rewrite predeqE => b0; split.
- case=> a; rewrite necset_convType.convE => -[a0' [a1' [H0 [H1 ->{a}]]]] <-{b0}.
  rewrite necset_convType.convE; exists (f a0'); exists (f a1'); split.
    by rewrite in_setE /=; exists a0' => //; rewrite -in_setE.
  split; last by case: f => f' /= Hf; rewrite Hf.
  by rewrite in_setE /=; exists a1' => //; rewrite -in_setE.
- rewrite necset_convType.convE => -[b0' [b1']].
  rewrite !in_setE /= => -[[a0' H0] <-{b0'}] -[[a1' h1] <-{b1'}] ->{b0}.
  exists (a0' <|p|> a1').
  rewrite necset_convType.convE; exists a0', a1'; split; first by rewrite in_setE.
  by split => //; rewrite in_setE.
  by case: f => f' /= Hf; rewrite Hf.
Qed.

Lemma bigsetU_affine (X : neset (necset A)) :
  (f @` (\bigcup_(x in X) x) =
   \bigcup_(x in free_semiCompSemiLattConvType_mor' @` X) x)%classic.
Proof.
rewrite funeqE => b; rewrite propeqE; split.
- case => a [x Xx xa] <-{b}.
  have Hf : affine_function f by case: f.
  exists (NECSet.Pack
            (NECSet.Class
               (CSet.Class (@is_convex_set_image' _ _ f Hf x))
               (NESet.Mixin (neset_image_neq0 f x)))) => /=; last by exists a.
  by exists x => //=; exact/necset_ext.
- by case => b0 [a0 Xa0 <-{b0}] [a a0a <-{b}]; exists a => //; exists a0.
Qed.

Lemma free_semiCompSemiLattConvType_mor'_scsl_op_morph :
  lub_op_morph free_semiCompSemiLattConvType_mor'.
Proof.
move=> /= X; apply necset_ext => /=; rewrite funeqE => b.
rewrite image_preserves_convex_hull'; last by case: f.
congr (hull _ b) => {b}.
exact: bigsetU_affine.
Qed.

Definition free_semiCompSemiLattConvType_mor :
  {hom necset_semiCompSemiLattConvType A, necset_semiCompSemiLattConvType B} :=
  locked (@Hom.Pack CS _ _ _ free_semiCompSemiLattConvType_mor'
    (LubOpAffine.Class free_semiCompSemiLattConvType_mor'_affine
                       free_semiCompSemiLattConvType_mor'_scsl_op_morph)).

Lemma free_semiCompSemiLattConvType_morE (X : necset_convType A) :
  NECSet.mixinType (free_semiCompSemiLattConvType_mor X) = image_neset f X.
Proof. by rewrite /free_semiCompSemiLattConvType_mor; unlock; apply neset_ext. Qed.

Lemma free_semiCompSemiLattConvType_morE' (X : necset_convType A) :
  NESet.car (NECSet.mixinType (free_semiCompSemiLattConvType_mor X)) = image_neset f X.
Proof. by rewrite /free_semiCompSemiLattConvType_mor; unlock. Qed.
End free_semiCompSemiLattConvType_mor.

Lemma free_semiCompSemiLattConvType_mor_id : FunctorLaws.id free_semiCompSemiLattConvType_mor.
Proof.
move=> a; rewrite hom_ext funeqE=> /= x /=.
apply necset_ext => /=.
by rewrite free_semiCompSemiLattConvType_morE' /= image_idfun.
Qed.
Lemma free_semiCompSemiLattConvType_mor_comp : FunctorLaws.comp free_semiCompSemiLattConvType_mor.
Proof.
move=> a b c [] g affine_g [] h affine_h; rewrite hom_ext funeqE => /= x /=.
apply necset_ext => /=.
rewrite 2!free_semiCompSemiLattConvType_morE' /= -imageA.
congr image.
by rewrite free_semiCompSemiLattConvType_morE'.
Qed.

Definition free_semiCompSemiLattConvType : functor CV CS :=
  Functor.Pack (Functor.Mixin free_semiCompSemiLattConvType_mor_id
                              free_semiCompSemiLattConvType_mor_comp).

Local Notation F1 := free_semiCompSemiLattConvType.

Lemma free_semiCompSemiLattConvType_mor_comp_fun (a b c : convType)
    (g : {hom b, c}) (h : {hom a, b}):
  [fun of F1 # [hom of [fun of g] \o [fun of h]]] = [fun of F1 # g] \o [fun of F1 # h].
Proof. by rewrite /Fun /= free_semiCompSemiLattConvType_mor_comp. Qed.

Let m2 : CS -> CV := id.
Let h2 := fun (a b : CS) (f : {hom CS; a, b}) =>
  @Hom.Pack CV a b _ f (LubOpAffine.base (Hom.class f)) : {hom CV; m2 a , m2 b}.
Lemma h2_id : FunctorLaws.id h2. Proof. by move=> *; apply hom_ext. Qed.
Lemma h2_comp : FunctorLaws.comp h2. Proof. by move=> *; apply hom_ext. Qed.
Definition forget_semiCompSemiLattConvType : functor CS CV :=
  Functor.Pack (Functor.Mixin h2_id h2_comp).

Local Notation U1 := forget_semiCompSemiLattConvType.

Lemma forget_semiCompSemiLattConvTypeE : (forall a : CS, forget_convType a = a)
  /\ (forall a b (f : {hom CS; a , b}), U1 # f = f :> (a -> b)).
Proof. by []. Qed.
End free_semiCompSemiLattConvType_functor.

Section eps1_eta1.
Import category.
Local Open Scope classical_set_scope.
Local Open Scope convex_scope.
Local Notation F1 := free_semiCompSemiLattConvType.
Local Notation U1 := forget_semiCompSemiLattConvType.
Local Notation CV := convType_category.
Local Notation CS := semiCompSemiLattConvType_category.

Definition eps1'' {L : semiCompSemiLattConvType}
  (X : necset_semiCompSemiLattConvType L) : L := |_| X.

Lemma eps1''_lub_op_morph L : lub_op_morph (@eps1'' L).
Proof.
move=> F.
rewrite /eps1''.
transitivity (|_| (lub_op @` ((fun X : necset_semiCompSemiLattType L => (X : neset _)) @` F))%:ne); last first.
- congr (|_| _).
  apply/neset_ext/eqEsubset => x [] x0 Fx0 <-.
  + by case: Fx0 => x1 Fx1 <-; exists x1.
  + by exists x0 => // ; exists x0.
transitivity (|_| (hull (\bigcup_(x in F) x))%:ne);
  first by congr (|_| _); apply neset_ext.
by rewrite lub_op_hull lub_op_bigcup.
Qed.

Lemma eps1''_affine L : affine_function (@eps1'' L).
Proof.
move=> X Y p.
rewrite /affine_function_at /eps1''.
transitivity (|_| (X :<| p |>: Y)%:ne); last by rewrite lub_op_conv_setD.
congr (|_| _%:ne); apply/neset_ext => /=.
rewrite conv_setE necset_convType.convE.
apply eqEsubset=> u.
- case=> x [] y [] xX [] yY ->.
  exists x; first by rewrite -in_setE.
  by rewrite conv_pt_setE; exists y; first by rewrite -in_setE.
- case=> x Xx; rewrite conv_pt_setE => -[] y Yy <-.
  by exists x, y; rewrite !in_setE.
Qed.

Lemma eps1''_natural (K L : semiCompSemiLattConvType) (f : {hom K , L}) :
  f \o eps1'' = eps1'' \o (F1 \O U1) # f.
Proof.
rewrite FCompE /= /id_f.
rewrite funeqE => X /=; rewrite apply_affine.
congr (|_| _); by rewrite free_semiCompSemiLattConvType_morE.
Qed.

Definition eps1' : F1 \O U1 ~~> FId :=
  fun L => @Hom.Pack CS _ _ _ (@eps1'' L)
    (LubOpAffine.Class (@eps1''_affine L) (@eps1''_lub_op_morph L)).

Lemma eps1'_natural : naturality _ _ eps1'.
Proof. by move=> K L f; rewrite eps1''_natural. Qed.

Definition eps1 : F1 \O U1 ~> FId :=
  locked (Natural.Pack (Natural.Class eps1'_natural)).

Lemma eps1E': eps1 = Natural eps1'_natural.
Proof. by rewrite /eps1; unlock. Qed.
Lemma eps1E (L : semiCompSemiLattConvType) :
  eps1 L = (fun X => |_| X) :> (_ -> _).
Proof. by rewrite /eps1; unlock. Qed.

Definition eta1'' (C : convType) (x : C) : necset_convType C := necset1 x.
Lemma eta1''_affine (C : convType) : affine_function (@eta1'' C).
Proof.
move=> a b p; rewrite /affine_function_at /eta1'' /=.
apply/necset_ext/eqEsubset=> x /=.
- move->; rewrite necset_convType.convE.
  by exists a, b; rewrite !inE !asboolE /necset1 /=.
- rewrite necset_convType.convE => -[] a0 [] b0.
  by rewrite !inE !asboolE /necset1 /= => -[] -> [] -> ->.
Qed.
Definition eta1' : FId ~~> U1 \O F1 :=
  fun C => @Hom.Pack CV _ _ _ (@eta1'' C) (@eta1''_affine C).
Lemma eta1'_natural : naturality _ _ eta1'.
Proof.
move=> a b h; rewrite funeqE=> x; apply necset_ext => /=.
by rewrite /eta1' /= /id_f free_semiCompSemiLattConvType_morE'/= image_set1.
Qed.
Definition eta1 : FId ~> U1 \O F1 :=
  locked (Natural.Pack (Natural.Class eta1'_natural)).
Lemma eta1E' : eta1 = Natural eta1'_natural.
Proof. by rewrite /eta1; unlock. Qed.
Lemma eta1E (C : convType) : eta1 C = (@necset1 _) :> (_ -> _).
Proof. by rewrite /eta1; unlock. Qed.
Lemma eta1E'' (C : convType) (x : C) : eta1 C x = necset1 x.
Proof. by rewrite /eta1; unlock. Qed.

Import homcomp_notation.
Lemma necset1E (T : convType) (t : T) : necset1 t = [set t] :> set T.
Proof. by []. Qed.
Lemma triL1 : TriangularLaws.left eta1 eps1.
Proof.
move=> c; apply funext=> x /=; apply/necset_ext=> /=.
rewrite eps1E eta1E' /= free_semiCompSemiLattConvType_morE' /= /eta1'' /=.
rewrite -[in RHS](hull_cset x); congr hull.
apply/eqEsubset=> a /=.
- case=> y [] b xb <-.
  by rewrite necset1E => ->.
- move=> xa.
  exists (necset1 a); last by rewrite necset1E.
  by exists a.
Qed.
Lemma triR1 : TriangularLaws.right eta1 eps1.
Proof.
move=> c; apply funext=> /= x.
by rewrite eps1E eta1E /= lub_op1.
Qed.
End eps1_eta1.

Section join1.
Import category.
Local Open Scope convex_scope.
Local Open Scope classical_set_scope.

Definition join1' (C : convType) (s : necset (necset_convType C)) : {convex_set C} :=
  CSet.Pack (CSet.Class (hull_is_convex (classical_sets.bigsetU s (fun x => if x \in s then (x : set _) else cset0 _)))).

Lemma join1'_neq0 (C : convType) (s : necset (necset_convType C)) : join1' s != set0 :> set _.
Proof.
rewrite hull_eq0 set0P.
case/set0P: (neset_neq0 s) => y.
case/set0P: (neset_neq0 y) => x yx sy.
exists x; exists y => //.
rewrite -in_setE in sy.
by rewrite sy.
Qed.

Definition join1 (C : convType) (s : necset (necset_convType C)) : necset C :=
  NECSet.Pack (NECSet.Class (CSet.Class (hull_is_convex _))
                            (NESet.Mixin (join1'_neq0 s))).

Lemma eps1''_correct (C : convType) (s : necset (necset_convType C)) :
  eps1'' s = join1 s.
Proof.
rewrite /eps1'' /join1 /=; apply/necset_ext => /=; congr (hull _).
rewrite /bigsetU; rewrite funeqE => c; rewrite propeqE; split.
- by case=> X sX Xc; exists X => //; rewrite -in_setE in sX; rewrite sX.
- by case=> X sX; rewrite -in_setE in sX; rewrite sX => Xc; exists X => //; rewrite -in_setE.
Qed.

Lemma eps1_correct (C : convType) (s : necset (necset_convType C)) :
  eps1 _ s = join1 s.
Proof.
rewrite /eps1; unlock=> /=.
exact: eps1''_correct.
Qed.

End join1.

Section P_delta_functor.
Import category.
Local Notation CT := Type_category.

Definition P_delta_left :=
  free_semiCompSemiLattConvType \O free_convType \O free_choiceType.

Definition P_delta_right :=
  forget_choiceType \O forget_convType \O forget_semiCompSemiLattConvType.

(* action on objects *)
Definition P_delta_acto (T : Type) : Type := P_delta_left T.

Definition P_delta : functor CT CT := P_delta_right \O P_delta_left.

Lemma P_deltaE (A B : Type) (f : {hom A, B}) :
  P_delta # f = P_delta_left # f :> (_ -> _).
Proof. exact: funext. Qed.

Lemma eps0_Dist1 (A : Type) (d : P_delta_acto A) : eps0 _ (FSDist1.d d) = d.
Proof. by rewrite eps0E Convn_of_FSDist_FSDist1. Qed.
End P_delta_functor.

(* TODO: move *)
Require monad_lib.
Require Import hierarchy.

Section P_delta_category_monad.
Import category.
Definition AC := AdjointFunctors.mk triLC triRC.
Definition A0 := AdjointFunctors.mk triL0 triR0.
Definition A1 := AdjointFunctors.mk triL1 triR1.
Definition Agcm := adj_comp AC (adj_comp A0 A1).
Definition Mgcm := Monad_of_adjoint Agcm.
Definition gcm := Monad_of_category_monad Mgcm.

Section gcm_opsE.
Import hierarchy.

Lemma gcm_retE (T : Type) (x : choice_of_Type T) :
  Ret x = necset1 (FSDist1.d x) :> gcm T.
Proof.
rewrite /= /Monad_of_category_monad.ret /= /Hom.apply /=.
rewrite !HCompId !HIdComp /= !HCompId !HIdComp /=.
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
Variable T : Type.
Variable X : gcm (gcm T).
Lemma gcm_joinE : Join X = necset_join X.
Import category.
apply/necset_ext.
rewrite /= /Monad_of_category_monad.join /= !HCompId !HIdComp eps1E.
have-> : [fun of AdjComp.F F0 F1
                # epsC
                    (AdjComp.G U0 U1
                       (necset_semiCompSemiLattConvType
                          (FSDist_convType (choice_of_Type T))))] = idfun.
- by rewrite -[in RHS]functor_id; congr Fun; apply/hom_ext; rewrite epsCE.
have-> : [fun of F1
              # eps0
              (U1
                 (necset_semiCompSemiLattConvType (FSDist_convType (choice_of_Type T))))] =
         @necset_join.F1join0 _.
- apply funext=> x; apply necset_ext.
  rewrite /= /necset_join.F1join0' /=.
  rewrite /free_semiCompSemiLattConvType_mor; unlock=> /=.
  by rewrite eps0E /=.
rewrite -(bigcup_image
            _ _ _ _
            (fun x => if x \in necset_join.F1join0 X then NECSet.car x else set0) idfun).
simpl.
congr hull.
rewrite /bigsetU.
apply/eqEsubset => y [i Xi iy].
- exists i; last exact: iy.
  exists i => //.
  move/asboolP in Xi.
  by rewrite inE Xi.
- move: Xi iy => [z /asboolP Xz].
  rewrite inE Xz => <- zy.
  exists z => //.
  by apply/asboolP.
Qed.
End gcm_opsE.
End P_delta_category_monad.
