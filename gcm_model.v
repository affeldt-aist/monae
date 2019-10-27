Require Import Reals.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import boolp classical_sets.
From mathcomp Require Import finmap.
From infotheo Require Import Reals_ext classical_sets_ext Rbigop ssrR ssr_ext.
From infotheo Require Import proba fsdist convex_choice necset.
Require Import monae_lib.
Require category.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* This file defines the functor P_delta and shows that it is a monad

P_delta =def= P_delta_right \O P_delta_left

where P_delta_right and P_delta_left are the following compositions:

             | FC = free_choiceType (= choice_of_Type)
P_delta_left:| F0 = free_convType (= FSDist)
             | F1 = free_semiCompSemiLattConvType (= necset)

              | UC = forget_choiceType
P_delta_right:| U0 = forget_convType
              | U1 = forget_semiCompSemiLattConvType

The proof uses the adjointness relations depicted as follows:

Functors:  |       FC              F0            F1
           |     ----->          ----->        ----->
Categories:| Type      choiceType      convType      semiCompSemiLattConvType
           |             (CC)            (CV)                (CS)
           |     <-----          <----         <-----
Forgetful  |       UC              U0            U1
Functors:  |

etaC/epsC : unit/counit of FC -| UC
eta0/eps0 : unit/counit of F0 -| U0
eta1/eps1 : unit/counit of F1 -| U1

*)
Section TODO_move_to_other_file.
Section misc_convex.
Local Open Scope proba_scope.
Local Open Scope convex_scope.
Variables (A : convType).

Lemma eq_dep_convn n (g : 'I_n -> A) (d : {fdist 'I_n})
      n0 (g0 : 'I_n0 -> A) (d0 : {fdist 'I_n0}) (Hn : n = n0)
      (Hg : eq_rect n (fun m => 'I_m -> A) g n0 Hn = g0)
      (Hd : eq_rect n (fun m => {fdist 'I_m}) d n0 Hn = d0) :
  \Conv_d g = \Conv_d0 g0.
Proof.
refine (match Hd with erefl => _ end).
refine (match Hg with erefl => _ end).
refine (match Hn with erefl => _ end).
reflexivity.
Qed.

Lemma convn1Eq' n (g : 'I_n -> A) (d : {fdist 'I_n}) (Hn1 : n = 1) :
  \Conv_d g = eq_rect n (fun n => 'I_n -> A) g 1 Hn1 ord0.
Proof.
set d' := eq_rect n (fun n0 => {fdist 'I_n0}) d 1 Hn1.
set g' := eq_rect n (fun n0 => 'I_n0 -> A) g 1 Hn1.
suff -> : \Conv_d g = \Conv_d' g' by rewrite convn1E.
by eapply eq_dep_convn.
Qed.

Lemma convn1Eq n (g : 'I_n -> A) (d : {fdist 'I_n})
      (Hn1 : n = 1) (i : 'I_n) : \Conv_d g = g i.
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
Definition choiceType_category_class : Category.class_of choiceType :=
  @Category.Class choiceType id (fun _ _ _ => True) (fun _ => I) (fun _ _ _ _ _ _ _ => I).
Canonical choiceType_category := Category.Pack choiceType_category_class.
Definition hom_choiceType (a b : choiceType) (f : a -> b) : {hom a, b} :=
  Hom (I : hom (f : El a -> El b)).
End choiceType_as_a_category.

Section free_choiceType_functor.
Import category.

Local Notation m := choice_of_Type.
Local Notation CC := choiceType_category.

Definition free_choiceType_mor (T U : Type_category) (f : {hom T, U}) :
  {hom m T, m U} := hom_choiceType (f : m T -> m U).
Lemma free_choiceType_mor_id : FunctorLaws.id free_choiceType_mor.
Proof. by move=> a; rewrite hom_ext. Qed.
Lemma free_choiceType_mor_comp : FunctorLaws.comp free_choiceType_mor.
Proof. by move=> a b c g h; rewrite hom_ext. Qed.
Definition free_choiceType : functor Type_category CC :=
  Functor.Pack (Functor.Class free_choiceType_mor_id free_choiceType_mor_comp).

Lemma free_choiceType_mor_comp_fun (a b c : Type) (g : {hom b, c})
      (h : {hom a, b}):
  [fun of free_choiceType_mor [hom of [fun of g] \o [fun of h]]] =
  [fun of free_choiceType_mor g] \o [fun of free_choiceType_mor h].
Proof. by rewrite free_choiceType_mor_comp. Qed.

Local Notation CT := Type_category.
Let m := Choice.sort.
Let h := fun (a b : CC) (f : {hom CC; a, b}) =>
             @Hom.Pack CT a b _ (FId # f) I : {hom CT; m a , m b}.
Lemma h_id : FunctorLaws.id h. Proof. by move=> *; apply hom_ext. Qed.
Lemma h_comp : FunctorLaws.comp h. Proof. by move=> *; apply hom_ext. Qed.
Definition forget_choiceType : functor CC CT :=
  Functor.Pack (Functor.Class h_id h_comp).
Lemma forget_choiceTypeE :
  (forall a : CC, forget_choiceType a = a)
  /\ (forall a b (f : {hom CC; a , b}), forget_choiceType # f = f :> (a -> b)).
Proof. by []. Qed.
End free_choiceType_functor.

Section epsC_etaC.
Import category.
Definition epsC'' {C : choiceType} : free_choiceType C -> C := idfun.
Definition epsC' : free_choiceType \O forget_choiceType ~~> FId :=
  fun T => @Hom.Pack choiceType_category _ _ _ (@epsC'' T) I.
Lemma epsC'_natural : naturality _ _ epsC'.
Proof. by []. Qed.
Definition epsC : free_choiceType \O forget_choiceType ~> FId :=
  locked (Natural.Pack (Natural.Class epsC'_natural)).
Lemma epsCE (T : choiceType) : epsC T = idfun :> (_ -> _).
Proof. by rewrite /epsC; unlock. Qed.

Definition etaC': FId ~~> forget_choiceType \O free_choiceType :=
  fun _ => @Hom.Pack Type_category _ _ _ idfun I.
Lemma etaC'_natural : naturality _ _ etaC'.
Proof. by []. Qed.
Definition etaC: FId ~> forget_choiceType \O free_choiceType :=
  locked (Natural.Pack (Natural.Class etaC'_natural)).
Lemma etaCE (T : Type) : etaC T = idfun :> (_ -> _).
Proof. by rewrite /etaC; unlock. Qed.

Import homcomp_notation.
Local Notation FC := free_choiceType.
Local Notation UC := forget_choiceType.
Lemma triLC : TriangularLaws.left etaC epsC.
Proof. by move=> c; rewrite etaCE epsCE. Qed.
Lemma triRC : TriangularLaws.right etaC epsC.
Proof. by move=> c; rewrite etaCE epsCE. Qed.
End epsC_etaC.

Section convType_as_a_category.
Import category.
Lemma affine_function_comp_proof' (A B C : convType) (f : A -> B) (g : B -> C) :
  affine_function f -> affine_function g -> affine_function (g \o f).
Proof. by move=> Hf Hg a b t; rewrite /affine_function_at compE Hf Hg. Qed.
Definition convType_category_class : Category.class_of convType :=
  Category.Class affine_function_id_proof affine_function_comp_proof'.
Canonical convType_category := Category.Pack convType_category_class.
End convType_as_a_category.

Section semiCompSemiLattConvType_as_a_category.
Import category.
Lemma Joet_affine_id_proof (A : semiCompSemiLattConvType) : JoetAffine.class_of (@id A).
Proof.
apply JoetAffine.Class; first exact: affine_function_id_proof.
by move=> x; congr Joet; apply neset_ext; rewrite /= image_idfun.
Qed.
Lemma Joet_affine_comp_proof (A B C : semiCompSemiLattConvType) (f : A -> B) (g : B -> C) :
  JoetAffine.class_of f -> JoetAffine.class_of g ->
  JoetAffine.class_of (g \o f).
Proof.
case => af jf [] ag jg.
apply JoetAffine.Class; first exact: affine_function_comp_proof'.
move=> x; cbn.
rewrite jf jg.
congr Joet; apply neset_ext =>/=.
by rewrite imageA.
Qed.
Definition semiCompSemiLattConvType_category_class :
  Category.class_of semiCompSemiLattConvType :=
  Category.Class Joet_affine_id_proof Joet_affine_comp_proof.
Canonical semiCompSemiLattConvType_category :=
  Category.Pack semiCompSemiLattConvType_category_class.
End semiCompSemiLattConvType_as_a_category.

Section apply_affine.
Import category.
Lemma apply_affine (K L : semiCompSemiLattConvType) (f : {hom K , L})
  (X : necset_semiCompSemiLattConvType K) :
  f (Joet `NE X) = Joet `NE (f @` X).
Proof. by case: f => f [? /= ->]. Qed.
End apply_affine.

Section free_convType_functor.
Import category.
(*
Definition affine_hom (T U : convType) (f : {affine T -> U}) : {hom T, U}.
apply (@Hom.Pack convType_category _ _ _ f).
rewrite /Hom.axiom /=.
by case: f.
Defined.
*)

(* morphism part of FSDist *)
Definition free_convType_mor (A B : choiceType) (f : {hom A, B}) :
  {hom (FSDist_convType A), (FSDist_choiceType B)}.
refine (@Hom.Pack convType_category _ _ _ (FSDistfmap f) _).
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
Definition free_convType_mor_supp (A B : choiceType) (f : A -> B(*{hom A , B}*)) (d : {dist A})
  (x : finsupp d) : [finType of finsupp ((free_convType_mor (hom_choiceType f)) d)] :=
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

Definition free_convType : functor choiceType_category convType_category :=
  Functor.Pack (Functor.Class free_convType_mor_id free_convType_mor_comp).

Lemma free_convType_mor_comp_fun (a b c : choiceType) (g : {hom b, c})
      (h : {hom a, b}):
  [fun of free_convType_mor [hom of [fun of g] \o [fun of h]]] =
  [fun of free_convType_mor g] \o [fun of free_convType_mor h].
Proof. by rewrite free_convType_mor_comp. Qed.

Local Notation CV := convType_category.
Local Notation CC := choiceType_category.
Let m1 : CV -> CC := [eta FId].
Let h1 := fun (a b : CV) (f : {hom CV; a, b}) =>
  @Hom.Pack CC a b _ (FId # f) I : {hom CC; m1 a , m1 b}.
Lemma h1_id : FunctorLaws.id h1. Proof. by move=> *; apply hom_ext. Qed.
Lemma h1_comp : FunctorLaws.comp h1. Proof. by move=> *; apply hom_ext. Qed.
Definition forget_convType : functor CV CC :=
  Functor.Pack (Functor.Class h1_id h1_comp).
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

Definition eps0'' {C : convType} (d : {dist C}) : C :=
  Convn_indexed_over_finType (fdist_of_Dist d) (fun x : finsupp d => fsval x).

Lemma eps0''_affine (C : convType) : affine_function (@eps0'' C).
Proof.
move => x y p.
rewrite /affine_function_at.
case/boolP : (p == `Pr 0) => [|pn0]; first by move/eqP ->; rewrite !conv0.
case/boolP : (p == `Pr 1) => [|pn1]; first by move/eqP ->; rewrite !conv1.
move: (pn1) => /onem_neq0 opn0.
apply S1_inj.
rewrite S1_conv.
rewrite !S1_Convn_indexed_over_finType.
transitivity (\ssum_(i : fdist_of_FSDist.D (x <|p|> y))
              scalept ((x <|p|> y) (fsval i)) (S1 (fsval i)));
  first by apply eq_bigr => i; rewrite fdist_of_FSDistE.
rewrite -(@big_seq_fsetE
            _ _ _ _ _ xpredT
            (fun i => scalept ((x <|p|> y) i) (S1 i))
         ) /=.
transitivity (\ssum_(i <- finsupp (x <|p|> y))
  ((scalept (x i) (S1 i) : Scaled_convType C) <|p|> scalept (y i) (S1 i))); first by apply eq_bigr => i _; rewrite FSDist_scalept_conv.
rewrite big_seq_fsetE big_scalept_conv_split /=.
rewrite -(@big_seq_fsetE _ _ _ _ _ xpredT (fun i => scalept (x i) (S1 i))).
rewrite -(@big_seq_fsetE _ _ _ _ _ xpredT (fun i => scalept (y i) (S1 i))) /=.
have -> : \ssum_i scalept (fdist_of_Dist x i) (S1 (fsval i)) =
         \ssum_(i <- finsupp x) scalept (x i) (S1 i)
  by rewrite big_seq_fsetE /=; apply eq_bigr => i _; rewrite fdist_of_FSDistE.
have -> : \ssum_i scalept (fdist_of_Dist y i) (S1 (fsval i)) =
         \ssum_(i <- finsupp y) scalept (y i) (S1 i)
  by rewrite big_seq_fsetE /=; apply eq_bigr => i _; rewrite fdist_of_FSDistE.
have -> : \ssum_(i <- finsupp x) scalept (x i) (S1 i) =
         \ssum_(i <- finsupp (x <|p|> y)) scalept (x i) (S1 i).
- rewrite [in RHS](bigID (fun i => i \in finsupp x)) /=.
  have -> : (\ssum_(i <- finsupp (x <|p|> y) | i \notin finsupp x) scalept (x i) (S1 i)) = Zero C
    by rewrite big1 //= => i Hi; rewrite fsfun_dflt // scalept0.
  rewrite addpt0 [in RHS]big_fset_condE /=.
  suff H : finsupp x = [fset i | i in finsupp (x <|p|> y) & i \in finsupp x]
    by rewrite [in LHS]H.
  + have -> : [fset i | i in finsupp (x <|p|> y) & i \in finsupp x]
              = [fset i | i in finsupp x & i \in finsupp (x <|p|> y)]
      by apply eq_imfset => //; move => i /=; rewrite !inE andbC.
    apply/eqP; rewrite eqEfsubset; apply/andP; split; last by apply fset_sub.
    apply/fsubsetP => i Hi.
    move/fsubsetP: (ConvFSDist.incl_finsupp_conv2fsdist x y pn0).
    move/(_ i Hi) => Hi'.
    by rewrite !inE Hi Hi'.
suff -> : \ssum_(i <- finsupp y) scalept (y i) (S1 i) =
         \ssum_(i <- finsupp (x <|p|> y)) scalept (y i) (S1 i) by [].
rewrite [in RHS](bigID (fun i => i \in finsupp y)) /=.
have -> : (\ssum_(i <- finsupp (x <|p|> y) | i \notin finsupp y) scalept (y i) (S1 i)) = Zero C
  by rewrite big1 //= => i Hi; rewrite fsfun_dflt // scalept0.
rewrite addpt0 [in RHS]big_fset_condE /=.
suff H : finsupp y = [fset i | i in finsupp (x <|p|> y) & i \in finsupp y]
  by rewrite [in LHS]H.
+ have -> : [fset i | i in finsupp (x <|p|> y) & i \in finsupp y] =
           [fset i | i in finsupp y & i \in finsupp (x <|p|> y)]
    by apply eq_imfset => //; move => i /=; rewrite !inE andbC.
  apply/eqP; rewrite eqEfsubset; apply/andP; split; last by apply fset_sub.
  apply/fsubsetP => i Hi.
  by rewrite !inE /= Hi finsupp_Conv // inE Hi orbT.
Qed.

Lemma eps0''_natural (C D : convType) (f : {hom C, D}) :
  f \o eps0'' = eps0'' \o (free_convType \O forget_convType) # f.
Proof.
rewrite FCompE /= /id_f.
apply funext => d; apply S1_inj => /=.
rewrite S1_proj_Convn_indexed_over_finType; last by case: f.
rewrite S1_Convn_indexed_over_finType.
evar (Y : fdist_of_FSDist.D ((FSDistfmap f) d) -> scaled_pt D).
transitivity (\ssum_i Y i); last first.
- apply eq_bigr => i _ /=.
  rewrite fdist_of_FSDistE /= FSDistBind.dE imfset_id /=.
  have -> : fsval i \in (\bigcup_(d0 <- [fset FSDist1.d (f a) | a in finsupp d]) finsupp d0)
    by case: i => v; rewrite FSDistBind.supp imfset_id.
  have H : scalept R0 (S1 (fsval i)) = Zero D by rewrite scalept0.
  have H0 : forall a : C, 0 <= d a * (FSDist1.d (f a)) (fsval i)
      by move=> a; apply mulR_ge0.
  rewrite big_scaleptl'; [| done | done] => {H} {H0}.
  rewrite (bigID (fun i0 => fsval i == f i0)) /=.
  have -> : \ssum_(i0 <- finsupp d | fsval i != f i0)
             scalept (d i0 * (FSDist1.d (f i0)) (fsval i)) (S1 (fsval i)) =
           Zero _
    by rewrite big1 // => c /negbTE Hc; rewrite FSDist1.dE inE Hc mulR0 scalept0.
  rewrite addpt0.
  rewrite big_seq_fsetE /=.
  exact: erefl.
rewrite /Y => {Y}.
set f' := free_convType_mor_supp f d.
transitivity (\ssum_i scalept (fdist_of_Dist d i) (S1 (fsval (f' i)))).
  by apply eq_bigr => *; rewrite fsval_free_convType_mor_supp.
rewrite (@partition_big
           _ _ _ _ (fdist_of_FSDist.D ((FSDistfmap f) d)) _ f' xpredT) /f' //=.
apply eq_bigr => -[i Hi] _ /=.
transitivity (\ssum_(i0 | free_convType_mor_supp f d i0 == [` Hi])
               scalept (d (fsval i0) * (FSDist1.d (f (fsval i0))) i) (S1 i)).
- apply eq_bigr => i0 /eqP.
  move/(congr1 (@fsval _ _)); rewrite fsval_free_convType_mor_supp /= => Hi0.
  by rewrite fdist_of_FSDistE FSDist1.dE -Hi0 inE eqxx mulR1.
apply eq_bigl => i0.
apply/eqP/eqP; first by move/(congr1 (@fsval _ _)) => /= <-.
by move=> ?; exact/val_inj.
Qed.

Definition eps0' : free_convType \O forget_convType ~~> FId :=
  fun a => @Hom.Pack convType_category _ _ _ eps0'' (eps0''_affine (C:=FId a)).

Lemma eps0'E (C : convType) (d : {dist C}) :
  eps0' C d = Convn_indexed_over_finType (fdist_of_Dist d) (fun x : finsupp d => fsval x).
Proof. by []. Qed.

Lemma eps0'_natural : naturality _ _ eps0'.
Proof. by move=> C D f; rewrite eps0''_natural. Qed.

Definition eps0 : free_convType \O forget_convType ~> FId :=
  locked (Natural.Pack (Natural.Class eps0'_natural)).

Lemma eps0E (C : convType) : eps0 C =
  (fun d => Convn_indexed_over_finType (fdist_of_Dist d) (fun x : finsupp d => (fsval x))) :> (_ -> _).
Proof. by rewrite /eps0; unlock. Qed.

Definition eta0' : FId ~~> forget_convType \O free_convType :=
  fun C => @Hom.Pack choiceType_category _ _ _ (fun x : C => FSDist1.d x) I.
Lemma eta0'_natural : naturality _ _ eta0'.
Proof.
by move=> a b h; rewrite funeqE=> x; rewrite FIdf /eta0' /= FSDistfmap1.
Qed.

Definition eta0 : FId ~> forget_convType \O free_convType :=
  locked (Natural.Pack (Natural.Class eta0'_natural)).
Lemma eta0E' : eta0 = Natural eta0'_natural.
Proof. by rewrite /eta0; unlock. Qed.
Lemma eta0E (T : choiceType) : eta0 T = (@FSDist1.d _) :> (_ -> _).
Proof. by rewrite /eta0; unlock. Qed.

Import homcomp_notation.
Import ScaledConvex.
Local Open Scope fset_scope.
Local Open Scope R_scope.
Local Notation F0 := free_convType.
Local Notation U0 := forget_convType.
Lemma triL0 : TriangularLaws.left eta0 eps0.
Proof.
move=> c; apply funext => x /=.
rewrite eps0E eta0E; apply: (@S1_inj _ _ x).
rewrite S1_Convn_indexed_over_finType /=.
pose cast (y : finsupp x) : FId c := let: FSetSub a _ := y in a.
have Y0 : forall (i : finsupp (FSDistfmap (@FSDist1.d _) x)),
  {a : finsupp x | fsval i = FSDist1.d (cast a)}.
  case=> i /= Hi; apply cid; move: Hi.
  by rewrite supp_FSDistfmap => /imfsetP[c0 /= c0x Hi]; exists (FSetSub c0x).
pose Y i := projT1 (Y0 i).
rewrite (eq_bigr (fun i => scalept (x (cast (Y i))) (S1 (fsval i)))); last first.
  move=> i _; rewrite fdist_of_FSDistE /F0 /Y; case: (Y0 _)=> a /= ia /=.
  rewrite {1}ia FSDistfmapE (fbig_pred1_inj _ _ _ (@FSDist1_inj _)) //; exact/fsvalP.
have HY' (i : finsupp x) :
  FSDist1.d (fsval i) \in finsupp (FSDistfmap (@FSDist1.d c) x).
  by rewrite supp_FSDistfmap; apply/imfsetP => /=; exists (fsval i).
set Y' := fun x0 => FSetSub (HY' x0).
have Y'K : cancel Y' Y.
  by move=> i; apply val_inj => /=; rewrite /Y; case: (Y0 _) => ? /= /FSDist1_inj.
have YK : cancel Y Y' by move=> i; apply val_inj; rewrite /= /Y; case: (Y0 _).
set dxy := fdist_of_finFSDist.d (FSDist_lift_supp.d (FSDist_crop0.d x) Y'K).
have Hdxy : x \o cast \o Y =1 dxy.
  move=> i; rewrite fdist_of_finFSDist.dE /= FSDist_lift_supp.dE /=.
  apply/eqP; case: ifPn.
    by move/imfsetP => -[j Hj ->]; rewrite fsfunE ffunE ifT // inE.
  apply/contraNT => x0; apply/imfsetP; exists (Y i) => //=.
  by rewrite mem_finsupp fsfunE ffunE ifT // inE.
clearbody dxy.
rewrite (eq_bigr (fun i => scalept (dxy i) (S1 (fsval i)))); last first.
  move=> i; by rewrite /= -Hdxy.
rewrite -S1_Convn_indexed_over_finType; congr S1.
apply FSDist_ext => a /=.
rewrite /Convn_indexed_over_finType convn_convnfsdist /= ConvnFSDist.dE fsfunE /=.
case: ifPn => Ha.
- rewrite /Convn_indexed_over_finType.d_enum /=.
  have ax : a \in finsupp x.
    case/bigfcupP : Ha => i /andP[/= _].
    rewrite /Convn_indexed_over_finType.d_enum ffunE -Hdxy /Y /=.
    case: (Y0 _) => -x0 /= -> _; rewrite FSDist1.supp inE => /eqP ->; exact/fsvalP.
  transitivity (\sum_(a0 <- finsupp x) x a0 * (FSDist1.d (FSDist1.d a0)) (FSDist1.d a)); last first.
    rewrite (big_fsetID _ (xpred1 a)) /=.
    rewrite -2!big_fset_condE [in X in _ + X = _]big1 ?addR0; last first.
      move=> c0 /negbTE c0a.
      by rewrite FSDist1.dE inE (inj_eq (@FSDist1_inj _)) eq_sym c0a mulR0.
    by rewrite fbig_pred1_inj // FSDist1.dE inE eqxx mulR1.
  rewrite (reindex_onto enum_rank enum_val) /=; last by move=> *; exact: enum_valK.
  rewrite -(@eq_big _ _ _ _ _ xpredT _ (fun j => x (cast (Y j)) * fsval j a)); last 2 first.
    by move=> i; rewrite enum_rankK eqxx.
    by move=> i _; rewrite ffunE -Hdxy enum_rankK.
  rewrite [in RHS]big_seq_fsetE /= (reindex Y') /=; last first.
    by exists Y => i _; [rewrite Y'K | rewrite YK].
  apply eq_bigr => i _ /=.
  rewrite !FSDist1.dE !inE Y'K inj_eq //; exact: FSDist1_inj.
- apply/esym/eqP; apply: contraNT Ha => xa0.
  rewrite -mem_finsupp in xa0.
  pose x' := Y' (FSetSub xa0).
  have x'a : finsupp (fsval x') `<=` finsupp x.
    apply/fsubsetP => i /=.
    by rewrite FSDist1.supp inE => /eqP ->.
  apply/bigfcupP; exists (enum_rank x').
    rewrite /index_enum -enumT mem_enum /= /Convn_indexed_over_finType.d_enum ffunE -Hdxy /=.
    rewrite enum_rankK /Y /=.
    case: (Y0 _) => //= x0 /FSDist1_inj <-.
    by apply/ltRP/FSDist.gt0.
  rewrite mem_finsupp /= enum_rankK.
  rewrite /= FSDist1.dE inE eqxx; exact/eqP/R1_neq_R0.
Qed.

Lemma triR0 : TriangularLaws.right eta0 eps0.
Proof.
move=> c.
rewrite eps0E eta0E funeqE => /= a /=.
have supp1 : #|fdist_of_FSDist.D (FSDist1.d a)| = 1%N
  by rewrite fdist_of_FSDistDE FSDist1.supp /= -cardfE cardfs1.
have suppE : fdist_of_FSDist.D (FSDist1.d a) = [finType of [fset a]]
  by rewrite fdist_of_FSDistDE FSDist1.supp /=.
have suppE' : finsupp (@FSDist1.d c a) = [fset a] by rewrite FSDist1.supp.
set i := eq_rect _ (fun n => 'I_n) ord0 _ (esym supp1).
rewrite /Convn_indexed_over_finType (convn1Eq i) //=.
have aP : a \in finsupp (FSDist1.d a) by rewrite FSDist1.supp inE.
change a with (fsval (FSetSub aP)).
congr fsval.
rewrite (enum_val_nth (FSetSub aP)).
move: i; rewrite supp1 => i.
rewrite (ord1 i) /=.
Fail case: (enum xpredT).
case: (@enum_mem
        (@fset_sub_finType (ConvexSpace.car c)
           (@FinSupp.fs (ConvexSpace.car c) R_eqType
              (fun _ : Choice.sort (ConvexSpace.car c) => IZR Z0)
              (@FSDist.f (ConvexSpace.car c)
                 (@FSDist1.d (ConvexSpace.car c) a))))
        (@mem
           (@fset_sub_type (ConvexSpace.car c)
              (@FinSupp.fs (ConvexSpace.car c) R_eqType
                 (fun _ : Choice.sort (ConvexSpace.car c) => IZR Z0)
                 (@FSDist.f (ConvexSpace.car c)
                    (@FSDist1.d (ConvexSpace.car c) a))))
           (predPredType
              (@fset_sub_type (ConvexSpace.car c)
                 (@FinSupp.fs (ConvexSpace.car c) R_eqType
                    (fun _ : Choice.sort (ConvexSpace.car c) => IZR Z0)
                    (@FSDist.f (ConvexSpace.car c)
                       (@FSDist1.d (ConvexSpace.car c) a)))))
           (fun
              _ : @fset_sub_type (ConvexSpace.car c)
                    (@FinSupp.fs (ConvexSpace.car c) R_eqType
                       (fun _ : Choice.sort (ConvexSpace.car c) => IZR Z0)
                       (@FSDist.f (ConvexSpace.car c)
                          (@FSDist1.d (ConvexSpace.car c) a))) => true))) => //=.
move: aP; rewrite suppE' => aP a' _.
apply val_inj=> /=.
by case: a' => a' /=; rewrite inE=> /eqP.
Qed.
End eps0_eta0.

(* the join operator for Dist is ((coercion) \o eps0) *)
Section eps0_correct.
Import category.
Import ScaledConvex.
Local Open Scope R_scope.

Lemma eps0''_correct (A : choiceType) (D : {dist (FSDist_convType A)}) : eps0'' D = FSDistjoin D.
Proof.
apply FSDist_ext => a; rewrite -[LHS]Scaled1RK /eps0''.
rewrite (S1_proj_Convn_indexed_over_finType (FSDist_eval_affine a)) big_scaleR.
rewrite FSDistjoinE big_seq_fsetE; apply eq_bigr => -[d dD] _.
by rewrite (scaleR_scalept _ (FDist.ge0 _ _)) fdist_of_FSDistE Scaled1RK.
Qed.

Lemma eps0_correct  (A : choiceType) (D : {dist (FSDist_convType A)}) : eps0 _ D = FSDistjoin D.
Proof.
rewrite /eps0; unlock=> /=.
exact: eps0''_correct.
Qed.
End eps0_correct.

Section free_semiCompSemiLattConvType_functor.
Import category.
Local Open Scope convex_scope.

Lemma hom_affine_function (A B : convType) (f : {hom A, B}) : affine_function [fun of f].
Proof. by case: f. Qed.

(* the morphism part of necset *)
Section free_semiCompSemiLattConvType_mor.
Variables (A B : convType) (f : {hom A , B}).

Definition free_semiCompSemiLattConvType_mor' (X : necset_convType A) :
  necset_convType B :=
  NECSet.Pack (NECSet.Class
    (CSet.Class (is_convex_set_image' (hom_affine_function f) X))
    (NESet.Class (neset_image_neq0 _ _))).

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
               (NESet.Class (neset_image_neq0 f x)))) => /=; last by exists a.
  by exists x => //=; exact/necset_ext.
- by case => b0 [a0 Xa0 <-{b0}] [a a0a <-{b}]; exists a => //; exists a0.
Qed.

Lemma free_semiCompSemiLattConvType_mor'_Joet_morph :
  Joet_morph free_semiCompSemiLattConvType_mor'.
Proof.
move=> /= X; apply necset_ext => /=; rewrite funeqE => b.
rewrite image_preserves_convex_hull'; last by case: f.
congr (hull _ b) => {b}.
exact: bigsetU_affine.
Qed.

Definition free_semiCompSemiLattConvType_mor :
  {hom necset_semiCompSemiLattConvType A, necset_semiCompSemiLattConvType B} :=
  locked (@Hom.Pack semiCompSemiLattConvType_category _ _ _ free_semiCompSemiLattConvType_mor' (JoetAffine.Class free_semiCompSemiLattConvType_mor'_affine free_semiCompSemiLattConvType_mor'_Joet_morph)).

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

Definition free_semiCompSemiLattConvType :
  functor convType_category semiCompSemiLattConvType_category :=
  Functor.Pack (Functor.Class free_semiCompSemiLattConvType_mor_id free_semiCompSemiLattConvType_mor_comp).

Lemma free_semiCompSemiLattConvType_mor_comp_fun (a b c : convType) (g : {hom b, c})
      (h : {hom a, b}):
  [fun of free_semiCompSemiLattConvType_mor [hom of [fun of g] \o [fun of h]]] =
  [fun of free_semiCompSemiLattConvType_mor g] \o [fun of free_semiCompSemiLattConvType_mor h].
Proof. by rewrite free_semiCompSemiLattConvType_mor_comp. Qed.

Local Notation CS := semiCompSemiLattConvType_category.
Local Notation CV := convType_category.

Let m2 : CS -> CV := [eta FId].
Let h2 := fun (a b : CS) (f : {hom CS; a, b}) =>
  @Hom.Pack CV a b _ (FId # f) (JoetAffine.base (Hom.class (FId # f))) : {hom CV; m2 a , m2 b}.
Lemma h2_id : FunctorLaws.id h2. Proof. by move=> *; apply hom_ext. Qed.
Lemma h2_comp : FunctorLaws.comp h2. Proof. by move=> *; apply hom_ext. Qed.
Definition forget_semiCompSemiLattConvType : functor CS CV :=
  Functor.Pack (Functor.Class h2_id h2_comp).

Lemma forget_semiCompSemiLattConvTypeE :
  (forall a : CS, forget_convType a = a)
  /\ (forall a b (f : {hom CS; a , b}), forget_semiCompSemiLattConvType # f = f :> (a -> b)).
Proof. by []. Qed.
End free_semiCompSemiLattConvType_functor.

(*
  eps1 is the counit of the adjunction
  (free_semiCompSemiLattConvType -| forget_semiCompSemiLattConvType),
  (forget_* is from semiCompSemiLattConvType to convType)
*)
Section eps1_eta1.
Import category.
Local Open Scope classical_set_scope.
Local Open Scope convex_scope.

Definition eps1'' {L : semiCompSemiLattConvType}
           (X : necset_semiCompSemiLattConvType L) : L := Joet `NE X.

Lemma eps1''_Joet_morph L : Joet_morph (@eps1'' L).
Proof.
move=> F.
rewrite /eps1''.
transitivity (Joet `NE (Joet @` ((fun X : necset_semiCompSemiLattType L => `NE X) @` F))); last first.
- congr Joet.
  apply/neset_ext/eqEsubset => x [] x0 Fx0 <-.
  + by case: Fx0 => x1 Fx1 <-; exists x1.
  + by exists `NE x0 => // ; exists x0.
transitivity (Joet `NE (hull (\bigcup_(x in F) x)));
  first by congr Joet; apply neset_ext.
by rewrite Joet_hull Joet_bigcup.
Qed.

Lemma eps1''_affine L : affine_function (@eps1'' L).
Proof.
move=> X Y p.
rewrite /affine_function_at /eps1''.
transitivity (Joet `NE (X :<| p |>: Y)); last by rewrite Joet_conv_setD.
congr (Joet `NE _); apply/neset_ext => /=.
rewrite conv_setE necset_convType.convE.
apply eqEsubset=> u.
- case=> x [] y [] xX [] yY ->.
  exists x; first by rewrite -in_setE.
  by rewrite conv_pt_setE; exists y; first by rewrite -in_setE.
- case=> x Xx; rewrite conv_pt_setE => -[] y Yy <-.
  by exists x, y; rewrite !in_setE.
Qed.

Lemma eps1''_natural (K L : semiCompSemiLattConvType) (f : {hom K , L}) :
  f \o eps1'' =
  eps1'' \o
         (free_semiCompSemiLattConvType \O forget_semiCompSemiLattConvType) # f.
Proof.
rewrite FCompE /= /id_f.
rewrite funeqE => X /=; rewrite apply_affine.
congr (Joet `NE _); by rewrite free_semiCompSemiLattConvType_morE.
Qed.

Definition eps1' :
  free_semiCompSemiLattConvType \O forget_semiCompSemiLattConvType ~~> FId :=
  fun L => @Hom.Pack semiCompSemiLattConvType_category _ _ _ (@eps1'' L) (JoetAffine.Class (@eps1''_affine L) (@eps1''_Joet_morph L)).

Lemma eps1'_natural : naturality _ _ eps1'.
Proof. by move=> K L f; rewrite eps1''_natural. Qed.

Definition eps1 :
  free_semiCompSemiLattConvType \O forget_semiCompSemiLattConvType ~> FId :=
  locked (Natural.Pack (Natural.Class eps1'_natural)).

Lemma eps1E': eps1 = Natural eps1'_natural.
Proof. by rewrite /eps1; unlock. Qed.
Lemma eps1E (L : semiCompSemiLattConvType) :
  eps1 L = (fun X => Joet `NE X) :> (_ -> _).
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
Definition eta1' :
  FId ~~> forget_semiCompSemiLattConvType \O free_semiCompSemiLattConvType :=
  fun C => @Hom.Pack convType_category _ _ _ (@eta1'' C) (@eta1''_affine C).
Lemma eta1'_natural : naturality _ _ eta1'.
Proof.
move=> a b h; rewrite funeqE=> x; apply necset_ext => /=.
by rewrite /eta1' /= /id_f free_semiCompSemiLattConvType_morE'/= image_set1.
Qed.
Definition eta1 :
  FId ~> forget_semiCompSemiLattConvType \O free_semiCompSemiLattConvType :=
  locked (Natural.Pack (Natural.Class eta1'_natural)).
Lemma eta1E': eta1 = Natural eta1'_natural.
Proof. by rewrite /eta1; unlock. Qed.
Lemma eta1E (C : convType) : eta1 C = (@necset1 _) :> (_ -> _).
Proof. by rewrite /eta1; unlock. Qed.
Lemma eta1E'' (C : convType) (x : C) : eta1 C x = necset1 x.
Proof. by rewrite /eta1; unlock. Qed.

Import homcomp_notation.
Local Notation F1 := free_semiCompSemiLattConvType.
Local Notation U1 := forget_semiCompSemiLattConvType.
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
move=> c; apply funext=> /= x.
by rewrite eps1E eta1E /= Joet1.
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
                            (NESet.Class (join1'_neq0 s))).

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

(* TODO: move? *)
Lemma NECSet_mixinType_inj (A : convType) (a b : necset A) :
  NECSet.mixinType a = NECSet.mixinType b -> a = b.
Proof.
move: a b => -[a Ha] [b Hb] /= [ab]; subst a; congr NECSet.Pack; exact/Prop_irrelevance.
Qed.

Section P_delta_functor.
Import category.

Definition P_delta_left :=
  free_semiCompSemiLattConvType \O free_convType \O free_choiceType.

Definition P_delta_right :=
  forget_choiceType \O forget_convType \O forget_semiCompSemiLattConvType.

(* action on objects *)
Definition P_delta_acto (T : Type) : Type := P_delta_left T.

Definition P_delta : functor Type_category Type_category :=
  P_delta_right \O P_delta_left.

Lemma eps0_Dist1 (A : Type) (d : P_delta_acto A) : eps0 _ (FSDist1.d d) = d.
Proof.
rewrite eps0E; apply: (@ScaledConvex.S1_inj _ _ d).
rewrite S1_Convn_indexed_over_finType /=.
rewrite (eq_bigr (fun=> ScaledConvex.S1 d)); last first.
  move=> i _; rewrite fdist_of_FSDistE FSDist1.dE /= -(FSDist1.supp d).
  rewrite fsvalP ScaledConvex.scalept1 /=; congr (ScaledConvex.S1 _).
  case: i => i Hi /=; rewrite FSDist1.supp inE in Hi; exact/eqP.
by rewrite big_const (_ : #| _ | = 1) // -cardfE FSDist1.supp cardfs1.
Qed.
End P_delta_functor.

Section P_delta_category_monad.
Import category.

Local Notation F1 := free_semiCompSemiLattConvType.
Local Notation F0 := free_convType.
Local Notation FC := free_choiceType.
Local Notation UC := forget_choiceType.
Local Notation U0 := forget_convType.
Local Notation U1 := forget_semiCompSemiLattConvType.

Definition eps : P_delta_left \O P_delta_right ~> FId :=
  locked
  (eps1
     \v [NEq F1 \O FId \O U1 , F1 \O U1]
     \v ((NId F1) \h eps0 \h (NId U1))
     \v [NEq F1 \O F0 \O FId \O U0 \O U1 , F1 \O (F0 \O U0) \O U1 ]
     \v ((NId F1) \h (NId F0)\h epsC \h (NId U0) \h (NId U1))
     \v [NEq P_delta_left \O P_delta_right , F1 \O F0 \O (FC \O UC) \O U0 \O U1]
  ).
Definition ret : FId ~> P_delta :=
  locked
  ([NEq UC \O U0 \O (U1 \O F1) \O F0 \O FC , P_delta]
     \v ((NId UC) \h (NId U0) \h eta1 \h (NId F0) \h (NId FC))
     \v [NEq UC \O (U0 \O F0) \O FC , UC \O U0 \O FId \O F0 \O FC]
     \v ((NId UC) \h eta0 \h (NId FC))
     \v [NEq UC \O FC , UC \O FId \O FC]
     \v etaC
  ).

Import homcomp_notation.

Lemma epsE' :
  eps =
  eps1
    \v [NEq F1 \O FId \O U1 , F1 \O U1]
    \v ((NId F1) \h eps0 \h (NId U1))
    \v [NEq F1 \O F0 \O FId \O U0 \O U1 , F1 \O (F0 \O U0) \O U1 ]
    \v ((NId F1) \h (NId F0) \h epsC \h (NId U0) \h (NId U1))
    \v [NEq P_delta_left \O P_delta_right , F1 \O F0 \O (FC \O UC) \O U0 \O U1].
Proof. by rewrite /eps; unlock. Qed.
Lemma retE' :
  ret =
  [NEq UC \O U0 \O (U1 \O F1) \O F0 \O FC , P_delta]
     \v ((NId UC) \h (NId U0) \h eta1 \h (NId F0) \h (NId FC))
     \v [NEq UC \O (U0 \O F0) \O FC , UC \O U0 \O FId \O F0 \O FC]
     \v ((NId UC) \h eta0 \h (NId FC))
     \v [NEq UC \O FC , UC \O FId \O FC]
     \v etaC.
Proof. by rewrite /ret; unlock. Qed.

Lemma epsE'' (L : semiCompSemiLattConvType) :
  eps L =
  [homcomp
     eps1 L
   , ((NId F1) \h eps0 \h (NId U1)) L
   , ((NId F1) \h (NId F0) \h epsC \h (NId U0) \h (NId U1)) L] :> (_ -> _).
Proof. by rewrite epsE'. Qed.

Lemma epsE (L : semiCompSemiLattConvType) :
  eps L =
  ((eps1 _) \o (free_semiCompSemiLattConvType_mor (eps0 _)) \o (free_semiCompSemiLattConvType_mor (free_convType_mor (epsC _))))
    :> (_ -> _).
Proof.
rewrite epsE''; cbn.
congr comp; congr comp.
- by rewrite HCompId HIdComp.
- by rewrite 2!HCompId -NIdFComp HIdComp.
Qed.

Lemma retE'' (T : Type) :
  ret T =
  [homcomp
     ((NId UC) \h (NId U0) \h eta1 \h (NId F0) \h (NId FC)) T
   , ((NId UC) \h eta0 \h (NId FC)) T
   , etaC T] :> (_ -> _).
Proof. by rewrite retE'. Qed.

Lemma retE (T : Type) :
  ret T = (@necset1 _) \o (@FSDist1.d (choice_of_Type T)) :> (_ -> _).
Proof.
rewrite funeqE => x; apply necset_ext.
by rewrite /ret; unlock; rewrite /= etaCE eta0E eta1E FSDistfmap_id.
Qed.

Definition join : P_delta \O P_delta ~> P_delta :=
  [NEq P_delta_right \O FId \O P_delta_left, P_delta]
    \v ((NId P_delta_right) \h eps \h (NId P_delta_left))
    \v [NEq P_delta \O P_delta ,
        (P_delta_right \O (P_delta_left \O P_delta_right)) \O P_delta_left].

Lemma joinE' (T : Type) :
  join T = ((NId P_delta_right) \h eps \h (NId P_delta_left)) T :> (_ -> _).
Proof. reflexivity. Qed.

Lemma joinE (T : Type) :
  join T = @eps (P_delta_left T) :> (_ -> _).
Proof. by rewrite /join !VCompE HCompId HIdComp compfid. Qed.

Lemma ret_natural : JoinLaws.ret_naturality ret.
Proof. exact: natural. Qed.
Lemma join_natural : JoinLaws.join_naturality join.
Proof. exact: natural. Qed.
Lemma join_left_unit : JoinLaws.left_unit ret join.
Proof.
rewrite /JoinLaws.left_unit => a.
rewrite funeqE=> d.
rewrite -homcompE joinE retE.
rewrite epsE compE -homcompE eps1E.
rewrite -[in RHS](Joet1 d); congr (Joet `NE _).
rewrite 2!free_semiCompSemiLattConvType_morE; apply/neset_ext => /=.
rewrite 2!image_set1 FSDistfmap1.
by rewrite epsCE eps0_Dist1.
Qed.
Lemma join_right_unit : JoinLaws.right_unit ret join.
Proof.
rewrite /JoinLaws.right_unit => a.
rewrite joinE.
(* NB: maybe worth factoring out? *)
have -> :
  forall x y (f : {hom x, y}) , P_delta # f = P_delta_left # f :> (_ -> _)
    by move=> x y f; apply funext.
move: (AdjComp.triL triL0 triL1) => triL01.
move: (AdjComp.triL triLC triL01 a) <-.
congr comp.
- rewrite epsE' /AdjComp.Eps /AdjComp.F; cbn.
  rewrite 4!compfid.
  congr comp.
  by rewrite -NIdFComp !HCompId !HIdComp.
- rewrite retE' /P_delta_left /AdjComp.Eta /AdjComp.G /AdjComp.F.
  congr Fun.
  rewrite /P_delta /P_delta_right /P_delta_left hom_ext.
  rewrite !VCompE ![in RHS]HCompE !VCompE !compfid !compidf.
  by rewrite -!NIdFComp !HCompId !HIdComp.
Qed.

Lemma joinA : JoinLaws.associativity join.
Proof.
rewrite /JoinLaws.associativity=> a.
rewrite 2![in RHS]joinE (natural eps _ _ (eps (P_delta_left a))).
rewrite joinE FCompE.
(* NB: maybe worth factoring out? *)
have-> :
  forall x y (f : {hom x, y}) , P_delta # f = P_delta_left # f :> (_ -> _)
    by move=> x y f; apply funext.
congr comp; congr [fun of P_delta_left # _].
by rewrite hom_ext joinE funeqE.
Qed.

Definition P_delta_monadMixin : Monad.mixin_of P_delta :=
  Monad.Mixin ret_natural join_natural join_left_unit join_right_unit joinA.
Definition m :=
  Monad_of_category_monad (Monad.Pack (Monad.Class P_delta_monadMixin)).
End P_delta_category_monad.
