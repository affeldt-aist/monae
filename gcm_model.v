Require Import Reals.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import choice fintype finfun bigop.
From mathcomp Require Import boolp classical_sets.
From mathcomp Require Import finmap.
From infotheo Require Import Reals_ext Rbigop ssrR proba dist convex_choice.
From infotheo Require Import necset.
Require category.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section TODO_move_to_other_file.
Section misc_classical_sets.
Local Open Scope classical_set_scope.
Lemma bigcup_image (A I J : Type) (P : set I) (f : I -> J) (X : J -> set A) :
  \bigcup_(x in f @` P) X x = \bigcup_(x in P) X (f x).
Proof.
apply eqEsubset=> x.
- by case=> j [] i pi <- Xfix; exists i.
- by case=> i Pi Xfix; exists (f i); first by  exists i.
Qed.
End misc_classical_sets.
End TODO_move_to_other_file.

(* choiceType as a category *)
(* Type as a category *)
Section choiceType_category.
Import category.
Definition choiceType_category_class : Category.class_of choiceType :=
@Category.Class choiceType id (fun _ _ _ => True) (fun _ => I) (fun _ _ _ _ _ _ _ => I).
Canonical choiceType_category := Category.Pack choiceType_category_class.
Definition hom_choiceType (a b : choiceType) (f : a -> b) : {hom a,b} := Hom (I : hom (f : El a -> El b)).
End choiceType_category.

(* free choiceType functor *)
Section gen_choiceType_functor.
Import category.

Definition gen_choiceType (T : Type) : choiceType :=
  Choice.Pack (Choice.Class (@gen_eqMixin T) (@gen_choiceMixin T)).

Local Notation m := gen_choiceType.
Local Notation CC := choiceType_category.

Definition gen_choiceType_mor (T U : Type_category) (f : {hom T, U}) :
  {hom m T, m U} := hom_choiceType (f : m T -> m U).
Lemma gen_choiceType_mor_id : FunctorLaws.id gen_choiceType_mor.
Proof. by move=> a; rewrite hom_ext. Qed.
Lemma gen_choiceType_mor_comp : FunctorLaws.comp gen_choiceType_mor.
Proof. by move=> a b c g h; rewrite hom_ext. Qed.
Definition gen_choiceType_functor :=
  Functor.Pack (Functor.Class gen_choiceType_mor_id gen_choiceType_mor_comp).

Lemma gen_choiceType_mor_comp_fun (a b c : Type) (g : {hom b, c})
      (h : {hom a, b}):
  [fun of gen_choiceType_mor [hom of [fun of g] \o [fun of h]]] =
  [fun of gen_choiceType_mor g] \o [fun of gen_choiceType_mor h].
Proof. by rewrite gen_choiceType_mor_comp. Qed.

Local Notation CT := Type_category.
Definition forget_choiceType : functor CC CT.
set (m := Choice.sort).
set (h := fun (a b : CC) (f : {hom CC; a, b}) =>
             @Hom.Pack CT a b _ (FId # f) I : {hom CT; m a , m b}).
refine (@Functor.Pack CC CT m _).
refine (@Functor.Class _ _  m h  _ _); by move=> *; apply hom_ext. 
Defined.
Lemma forget_choiceTypeE :
  (forall a : CC, forget_choiceType a = a)
  /\ (forall a b (f : {hom CC; a , b}), forget_choiceType # f = f :> (a -> b)).
Proof. done. Qed.
End gen_choiceType_functor.

Section epsC_etaC.
Import category.
(*Definition epsC (C : choiceType) : gen_choiceType (forget_choiceType C) -> C.*)
Definition epsC'' {C : choiceType} : gen_choiceType C -> C := idfun.
Definition epsC' : gen_choiceType_functor \O forget_choiceType ~~> FId :=
  fun T => @Hom.Pack choiceType_category _ _ _ (@epsC'' T) I.
Lemma epsC'_natural : naturality _ _ epsC'.
Proof. by []. Qed.
Definition epsC : gen_choiceType_functor \O forget_choiceType ~> FId :=
  locked (Natural.Pack (Natural.Class epsC'_natural)).
Lemma epsCE' : epsC = Natural epsC'_natural.
Proof. by rewrite /epsC; unlock. Qed.
Lemma epsCE (T : choiceType) : epsC T = idfun :> (_ -> _).
Proof. by rewrite /epsC; unlock. Qed.

Definition etaC': FId ~~> forget_choiceType \O gen_choiceType_functor :=
  fun _ => @Hom.Pack Type_category _ _ _ idfun I.
Lemma etaC'_natural : naturality _ _ etaC'.
Proof. by []. Qed.
Definition etaC: FId ~> forget_choiceType \O gen_choiceType_functor :=
  locked (Natural.Pack (Natural.Class etaC'_natural)).
Lemma etaCE' : etaC = Natural etaC'_natural.
Proof. by rewrite /etaC; unlock. Qed.
Lemma etaCE (T : Type) : etaC T = idfun :> (_ -> _).
Proof. by rewrite /etaC; unlock. Qed.

Import homcomp_notation.
Local Notation F := gen_choiceType_functor.
Local Notation G := forget_choiceType.
Lemma triLC c : (epsC (F c)) \o (F # etaC c) = idfun.
Proof. by rewrite etaCE epsCE. Qed.
Lemma triRC d : (G # epsC d) \o (etaC (G d)) = idfun.
Abort.
End epsC_etaC.

(* convType as a category *)
Section convType_category.
Import category.
Lemma affine_function_comp_proof' :
  forall (A B C : convType) (f : A -> B) (g : B -> C),
    affine_function f -> affine_function g -> affine_function (g \o f).
Proof. by move=>A B C f g Hf Hg a b t; rewrite /affine_function_at funcompE Hf Hg. Qed.
Definition convType_category_class : Category.class_of convType :=
  Category.Class affine_function_id_proof affine_function_comp_proof'.
Canonical convType_category := Category.Pack convType_category_class.
End convType_category.

(* semiCompSemiLattConvType as a category *)
Section semiCompSemiLattConvType_category.
Import category.
Local Notation U := semiCompSemiLattConvType.
Lemma Joet_affine_id_proof (A : U) : JoetAffine.class_of (@id A).
Proof.
apply JoetAffine.Class; first by exact: affine_function_id_proof.
by move=> x; congr Joet; apply neset_ext; rewrite /= image_idfun.
Qed.
Lemma Joet_affine_comp_proof (A B C : U) (f : A -> B) (g : B -> C) :
    JoetAffine.class_of f -> JoetAffine.class_of g ->
    JoetAffine.class_of (g \o f).
Proof. 
case => af jf [] ag jg.
apply JoetAffine.Class; first by exact: affine_function_comp_proof'.
move=> x; cbn.
rewrite jf jg.
congr Joet; apply neset_ext =>/=.
by rewrite imageA.
Qed.
Definition semiCompSemiLattConvType_category_class :
  Category.class_of U :=
  Category.Class Joet_affine_id_proof Joet_affine_comp_proof.
Canonical semiCompSemiLattConvType_category :=
  Category.Pack semiCompSemiLattConvType_category_class.
End semiCompSemiLattConvType_category.

Section apply_affine.
Import category.
Lemma apply_affine (K L : semiCompSemiLattConvType) (f : {hom K , L})
  (X : necset_semiCompSemiLattConvType K) :
  f (Joet `NE X) = Joet `NE (f @` X).
Proof. by case: f => f [? /= ->]. Qed.
End apply_affine.

Section Dist_functor.
Import category.
(*
Definition affine_hom (T U : convType) (f : {affine T -> U}) : {hom T, U}.
apply (@Hom.Pack convType_category _ _ _ f).
rewrite /Hom.axiom /=.
by case: f.
Defined.
*)

(* morphism part of Dist *)
Definition Dist_mor (A B : choiceType) (f : {hom A , B}) :
  {hom Dist_convType A , Dist B}.
refine (@Hom.Pack convType_category _ _ _ (Distfmap f) _).
move=> x y t.
by apply: Conv2Dist.bind_left_distr.
Defined.

(* Dist_mor induces maps between supports *)
Definition Dist_mor_supp (A B : choiceType) (f : A -> B(*{hom A , B}*)) (d : Dist A) :
  [finType of finsupp d] -> [finType of finsupp ((Dist_mor (hom_choiceType f)) d)].
Proof.
move=> x.
apply (@FSetSub _ _ (f (fsval x))).
rewrite /= DistBind.supp imfset_id.
apply/bigfcupP.
exists (Dist1.d (f (fsval x))).
- rewrite andbT.
  apply (in_imfset _ (fun x => Dist1.d (f x))) => /=.
  by move:x; case:d.
- rewrite mem_finsupp Dist1.dE inE eqxx; exact/eqP/R1_neq_R0.
Defined.
Global Arguments Dist_mor_supp [A B] f d.
Lemma fsval_Dist_mor_supp (A B : choiceType) (f : {hom A , B}) d i :
  fsval ((Dist_mor_supp f d) i) = f (fsval i).
Proof. by case: i. Qed.

Lemma Dist_mor_id : FunctorLaws.id Dist_mor.
Proof.
by move=> a; rewrite hom_ext funeqE=> x /=; rewrite/idfun Distfmap_id.
Qed.
Lemma Dist_mor_comp : FunctorLaws.comp Dist_mor.
Proof. by move=> a b c g h; rewrite hom_ext /= Distfmap_comp. Qed.

Definition Dist_functor :=
  Functor.Pack (Functor.Class Dist_mor_id Dist_mor_comp).

Lemma Dist_mor_comp_fun (a b c : choiceType) (g : {hom b, c})
      (h : {hom a, b}):
  [fun of Dist_mor [hom of [fun of g] \o [fun of h]]] =
  [fun of Dist_mor g] \o [fun of Dist_mor h].
Proof. by rewrite Dist_mor_comp. Qed.

Local Notation CV := convType_category.
Local Notation CC := choiceType_category.
Definition forget_convType : functor CV CC.
set (m := [eta FId] : CV -> CC).
set (h := fun (a b : CV) (f : {hom CV; a, b}) =>
             @Hom.Pack CC a b _ (FId # f) I : {hom CC; m a , m b}).
refine (@Functor.Pack CV CC m _).
refine (@Functor.Class _ _  m h  _ _); by move=> *; apply hom_ext. 
Defined.

Lemma forget_convTypeE :
  (forall a : CV, forget_convType a = a)
  /\ (forall a b (f : {hom CV; a , b}), forget_convType # f = f :> (a -> b)).
Proof. done. Qed.
End Dist_functor.

(*
  eps0 is the counit of the adjunction (Dist -| coercion) and it is just Convn
  (* p.164 *).
*)
Section eps0_eta0.
Import category.
Import ScaledConvex.
Local Open Scope fset_scope.
Local Open Scope R_scope.
Local Open Scope convex_scope.

Definition eps0'' {C : convType} (d : Dist C) : C :=
  Convn_indexed_over_finType (dist_of_Dist d) (fun x : finsupp d => fsval x).

Lemma eps0''_affine (C : convType) : affine_function (@eps0'' C).
Proof.
move => x y p.
rewrite /affine_function_at.
case/boolP: (p == `Pr 0); first by move/eqP ->; rewrite !conv0.
move=> pn0.
case/boolP: (p == `Pr 1); first by move/eqP ->; rewrite !conv1.
move=> pn1.
move: (pn1) => /onem_neq0 opn0.
apply S1_inj.
rewrite S1_conv.
rewrite !S1_Convn_indexed_over_finType.
transitivity (\ssum_(i : dist_of_Dist.D (x <|p|> y))
              scalept ((x <|p|> y) (fsval i)) (S1 (fsval i)));
  first by apply eq_bigr => i; rewrite dist_of_DistE.
rewrite -(@big_seq_fsetE
            _ _ _ _ _ xpredT
            (fun i => scalept ((x <|p|> y) i) (S1 i))
         ) /=.
transitivity (\ssum_(i <- finsupp (x <|p|> y))
  ((scalept (x i) (S1 i) : Scaled_convType C) <|p|> scalept (y i) (S1 i))); first by apply eq_bigr => i _; rewrite Dist_scalept_conv.
rewrite big_seq_fsetE big_scalept_conv_split /=.
rewrite -(@big_seq_fsetE _ _ _ _ _ xpredT (fun i => scalept (x i) (S1 i))).
rewrite -(@big_seq_fsetE _ _ _ _ _ xpredT (fun i => scalept (y i) (S1 i))) /=.
have -> : \ssum_i scalept (dist_of_Dist x i) (S1 (fsval i)) =
         \ssum_(i <- finsupp x) scalept (x i) (S1 i)
  by rewrite big_seq_fsetE /=; apply eq_bigr => i _; rewrite dist_of_DistE.
have -> : \ssum_i scalept (dist_of_Dist y i) (S1 (fsval i)) =
         \ssum_(i <- finsupp y) scalept (y i) (S1 i)
  by rewrite big_seq_fsetE /=; apply eq_bigr => i _; rewrite dist_of_DistE.
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
    move/fsubsetP: (Conv2Dist.incl_finsupp_conv2dist x y pn0).
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
  by rewrite !inE /= Hi finsupp_Conv2 // inE Hi orbT.
Qed.

Lemma eps0''_natural (C D : convType) (f : {hom C, D}) :
  f \o eps0'' = eps0'' \o (Dist_functor \O forget_convType) # f.
Proof.
rewrite FCompE /= /id_f.
apply funext => d; apply S1_inj => /=.
rewrite S1_proj_Convn_indexed_over_finType; last by case: f.
rewrite S1_Convn_indexed_over_finType.
evar (Y : dist_of_Dist.D ((Distfmap f) d) -> scaled_pt D).
transitivity (\ssum_i Y i); last first.
- apply eq_bigr => i _ /=.
  rewrite dist_of_DistE /= DistBind.dE imfset_id /=.
  have -> : fsval i \in (\bigcup_(d0 <- [fset Dist1.d (f a) | a in finsupp d]) finsupp d0)
    by case: i => v; rewrite DistBind.supp imfset_id.
  have H : scalept R0 (S1 (fsval i)) = Zero D by rewrite scalept0.
  have H0 : forall a : C, 0 <= d a * (Dist1.d (f a)) (fsval i)
      by move=> a; apply mulR_ge0; apply Dist.ge0.
  rewrite big_scaleptl'; [| done | done] => {H} {H0}.
  rewrite (bigID (fun i0 => fsval i == f i0)) /=.
  have -> : \ssum_(i0 <- finsupp d | fsval i != f i0)
             scalept (d i0 * (Dist1.d (f i0)) (fsval i)) (S1 (fsval i)) =
           Zero _
    by rewrite big1 // => c /negbTE Hc; rewrite Dist1.dE inE Hc mulR0 scalept0.
  rewrite addpt0.
  rewrite big_seq_fsetE /=.
  exact: erefl.
rewrite /Y => {Y}.
set f' := (Dist_mor_supp f d).
transitivity (\ssum_i scalept (dist_of_Dist d i) (S1 (fsval (f' i)))); first by apply eq_bigr => *; rewrite fsval_Dist_mor_supp.
rewrite (@partition_big
           _ _ _ _ (dist_of_Dist.D ((Distfmap f) d)) _ f' xpredT) /f' //=.
apply eq_bigr => -[i Hi] _ /=.
transitivity (\ssum_(i0 | Dist_mor_supp f d i0 == [` Hi])
               scalept (d (fsval i0) * (Dist1.d (f (fsval i0))) i) (S1 i)).
- apply eq_bigr => i0 /eqP.
  move/(congr1 (@fsval _ _)); rewrite fsval_Dist_mor_supp /= => Hi0.
  by rewrite dist_of_DistE Dist1.dE -Hi0 inE eqxx mulR1.
apply eq_bigl => i0.
apply/eqP/eqP; first by move/(congr1 (@fsval _ _)) => /= <-.
move=> H.
exact/val_inj.
Qed.

Definition eps0' : Dist_functor \O forget_convType ~~> FId :=
fun a => @Hom.Pack convType_category _ _ _ eps0'' (eps0''_affine (C:=FId a)).

Lemma eps0'E (C : convType) (d : Dist C) :
  eps0' C d = Convn_indexed_over_finType (dist_of_Dist d) (fun x : finsupp d => (fsval x)).
Proof. reflexivity. Qed.

Lemma eps0'_natural : naturality _ _ eps0'.
Proof. by move=> C D f; rewrite eps0''_natural. Qed.

Definition eps0 : Dist_functor \O forget_convType ~> FId :=
  locked (Natural.Pack (Natural.Class eps0'_natural)).

Lemma eps0E' : eps0 = Natural eps0'_natural.
Proof. by rewrite /eps0; unlock. Qed.
Lemma eps0E (C : convType) :
  eps0 C = (fun d => Convn_indexed_over_finType (dist_of_Dist d) (fun x : finsupp d => (fsval x))) :> (_ -> _).
Proof. by rewrite /eps0; unlock. Qed.

Definition eta0' : FId ~~> forget_convType \O Dist_functor :=
  fun C => @Hom.Pack choiceType_category _ _ _ (fun x : C => Dist1.d x) I.
Lemma eta0'_natural : naturality _ _ eta0'.
Proof.
by move=> a b h; rewrite funeqE=> x; rewrite FIdf /eta0' /= Distfmap1.
Qed.

Definition eta0 : FId ~> forget_convType \O Dist_functor :=
  locked (Natural.Pack (Natural.Class eta0'_natural)).
Lemma eta0E' : eta0 = Natural eta0'_natural.
Proof. by rewrite /eta0; unlock. Qed.
Lemma eta0E (T : choiceType) : eta0 T = (@Dist1.d _) :> (_ -> _).
Proof. by rewrite /eta0; unlock. Qed.

(* TODO: move *)
Section fbig_pred1_inj.
Variables (R : Type) (idx : R) (op : Monoid.com_law idx).
Lemma fbig_pred1_inj (A C : choiceType) h (k : A -> C) (d : {fset _}) a :
  a \in d -> injective k -> \big[op/idx]_(a0 <- d | k a0 == k a) h a0 = h a.
Proof.
move=> ad inj_k.
rewrite big_fset_condE -(big_seq_fset1 op); apply eq_fbig => // a0.
rewrite !inE /=; apply/idP/idP => [|/eqP ->]; last by rewrite eqxx andbT.
by case/andP => _ /eqP/inj_k ->.
Qed.
End fbig_pred1_inj.
Arguments fbig_pred1_inj [R] [idx] [op] [A] [C] [h] [k].

Import homcomp_notation.
Import ScaledConvex.
Local Open Scope fset_scope.
Local Open Scope R_scope.
Local Notation F := Dist_functor.
Local Notation G := forget_convType.
Lemma triL0 c : (eps0 (F c)) \o (F # eta0 c) = idfun.
Proof.
apply funext => x /=.
rewrite eps0E eta0E; apply: (@S1_inj _ _ x).
rewrite S1_Convn_indexed_over_finType /=.
pose cast (y : finsupp x) : FId c := let: FSetSub a _ := y in a.
have Y0 : forall (i : finsupp (Distfmap (@Dist1.d _) x)),
  {a : finsupp x | fsval i = Dist1.d (cast a)}.
  case=> i /= Hi; apply cid; move: Hi.
  by rewrite supp_Distfmap => /imfsetP[c0 /= c0x Hi]; exists (FSetSub c0x).
pose Y i := projT1 (Y0 i).
rewrite (eq_bigr (fun i => scalept (x (cast (Y i))) (S1 (fsval i)))); last first.
  move=> i _; rewrite dist_of_DistE /F /Y; case: (Y0 _)=> a /= ia /=.
  rewrite {1}ia DistfmapE (fbig_pred1_inj _ _ _ (@Dist1_inj _)) //; exact/fsvalP.
have HY' (i : finsupp x) :
  Dist1.d (fsval i) \in finsupp (Distfmap (@Dist1.d c) x).
  by rewrite supp_Distfmap; apply/imfsetP => /=; exists (fsval i).
set Y' := fun x0 => FSetSub (HY' x0).
have Y'K : cancel Y' Y.
  by move=> i; apply val_inj => /=; rewrite /Y; case: (Y0 _) => ? /= /Dist1_inj.
have YK : cancel Y Y' by move=> i; apply val_inj; rewrite /= /Y; case: (Y0 _).
set dxy := dist_of_finDist.d (Dist_lift_supp.d (Dist_crop0.d x) Y'K).
have Hdxy : x \o cast \o Y =1 dxy.
  move=> i; rewrite dist_of_finDist.dE /= Dist_lift_supp.dE /=.
  apply/eqP; case: ifPn.
    by move/imfsetP => -[j Hj ->]; rewrite fsfunE ffunE ifT // inE.
  apply/contraNT => x0; apply/imfsetP; exists (Y i) => //=.
  by rewrite mem_finsupp fsfunE ffunE ifT // inE.
clearbody dxy.
rewrite (eq_bigr (fun i => scalept (dxy i) (S1 (fsval i)))); last first.
  move=> i; by rewrite /= -Hdxy.
rewrite -S1_Convn_indexed_over_finType; congr S1.
apply Dist_ext => a /=.
rewrite /Convn_indexed_over_finType convn_convdist /= ConvDist.dE fsfunE /=.
case: ifPn => Ha.
- rewrite /Convn_indexed_over_finType.d_enum /=.
  have ax : a \in finsupp x.
    case/bigfcupP : Ha => i /andP[/= _].
    rewrite /Convn_indexed_over_finType.d_enum ffunE -Hdxy /Y /=.
    case: (Y0 _) => -x0 /= -> _; rewrite Dist1.supp inE => /eqP ->; exact/fsvalP.
  transitivity (\sum_(a0 <- finsupp x) x a0 * (Dist1.d (Dist1.d a0)) (Dist1.d a)); last first.
    rewrite (big_fsetID _ (xpred1 a)) /=.
    rewrite -2!big_fset_condE [in X in _ + X = _]big1 ?addR0; last first.
      move=> c0 /negbTE c0a.
      by rewrite Dist1.dE inE (inj_eq (@Dist1_inj _)) eq_sym c0a mulR0.
    by rewrite fbig_pred1_inj // Dist1.dE inE eqxx mulR1.
  rewrite (reindex_onto enum_rank enum_val) /=; last by move=> *; exact: enum_valK.
  rewrite -(@eq_big _ _ _ _ _ xpredT _ (fun j => x (cast (Y j)) * fsval j a)); last 2 first.
    by move=> i; rewrite enum_rankK eqxx.
    by move=> i _; rewrite ffunE -Hdxy enum_rankK.
  rewrite [in RHS]big_seq_fsetE /= (reindex Y') /=; last first.
    by exists Y => i _; [rewrite Y'K | rewrite YK].
  apply eq_bigr => i _ /=.
  rewrite !Dist1.dE !inE Y'K inj_eq //; exact: Dist1_inj.
- apply/esym/eqP; apply: contraNT Ha => xa0.
  rewrite -mem_finsupp in xa0.
  pose x' := Y' (FSetSub xa0).
  have x'a : finsupp (fsval x') `<=` finsupp x.
    apply/fsubsetP => i /=.
    by rewrite Dist1.supp inE => /eqP ->.
  apply/bigfcupP; exists (enum_rank x').
    rewrite /index_enum -enumT mem_enum /= /Convn_indexed_over_finType.d_enum ffunE -Hdxy /=.
    rewrite enum_rankK /Y /=.
    case: (Y0 _) => //= x0 /Dist1_inj <-.
    by apply/ltRP/Dist.gt0.
  rewrite mem_finsupp /= enum_rankK.
  rewrite /= Dist1.dE inE eqxx; exact/eqP/R1_neq_R0.
Qed.

Lemma triR0 d : (G # eps0 d) \o (eta0 (G d)) = idfun.
Abort.

End eps0_eta0.

(* the join operator for Dist is ((coercion) \o eps0) *)
Section eps0_correct.
Import ScaledConvex.
Local Open Scope R_scope.

Lemma eps0_correct (A : choiceType) (D : Dist (Dist A)) : eps0'' D = Distjoin D.
Proof.
apply Dist_ext => a; rewrite -[LHS]Scaled1RK /eps0''.
rewrite (S1_proj_Convn_indexed_over_finType (Dist_eval_affine a)) big_scaleR.
rewrite DistjoinE big_seq_fsetE; apply eq_bigr => -[d dD] _.
by rewrite (scaleR_scalept _ (dist_ge0 _ _)) dist_of_DistE Scaled1RK.
Qed.
End eps0_correct.

Section necset_functor.
Import category.
Local Open Scope convex_scope.

(* the morphism part of necset *)
Section necset_mor.
Variables (A B : convType) (f : {hom A , B}).

Definition necset_mor' : necset_convType A -> necset_convType B.
move=> car.
refine (NECSet.Pack (NECSet.Class (CSet.Class (@is_convex_set_image' _ _ f _ car)) (NESet.Class _))); first by case: f.
apply/set0P; exists (f (neset_repr car)) => /=.
exists (neset_repr car) => //; exact: repr_in_neset.
Defined.

(* the results of necset_mor are semiLattConvType-morphisms, i.e., are
   affine and preserve semilatt operations *)
Lemma necset_mor'_affine : affine_function necset_mor'.
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
  (f @` (\bigcup_(x in X) x) = \bigcup_(x in necset_mor' @` X) x)%classic.
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

Lemma necset_mor'_Joet_morph : Joet_morph necset_mor'.
Proof.
move=> /= X; apply necset_ext => /=; rewrite funeqE => b.
rewrite image_preserves_convex_hull'; last by case: f.
congr (hull _ b) => {b}.
exact: bigsetU_affine.
Qed.

Definition necset_mor :
  {hom necset_semiCompSemiLattConvType A, necset_semiCompSemiLattConvType B} :=
  locked (@Hom.Pack semiCompSemiLattConvType_category _ _ _ necset_mor' (JoetAffine.Class necset_mor'_affine necset_mor'_Joet_morph)).

Lemma necset_morE (X : necset_convType A) :
  NECSet.mixinType (necset_mor X) = image_neset f X.
Proof. by rewrite /necset_mor; unlock; apply neset_ext. Qed.

Lemma necset_morE' (X : necset_convType A) :
  NESet.car (NECSet.mixinType (necset_mor X)) = image_neset f X.
Proof. by rewrite /necset_mor; unlock. Qed.
End necset_mor.

(*
Definition Joet_affine_hom (T U : semiCompSemiLattConvType)
           (f : {Joet_affine T -> U}) : {hom T, U}.
apply (@Hom.Pack semiCompSemiLattConvType_category _ _ _ f).
rewrite /Hom.axiom /=.
by case: f.
Defined.
Definition convType_hom_affine (T U : convType) (f : {hom T, U}) :
  {affine T -> U}.
apply (@AffineFunction.Pack _ _ _ f).
by case: f.
Defined.
Definition necset_actm (T U : convType) (f : {hom T, U}) :
  {hom necset_semiCompSemiLattConvType T, necset_semiCompSemiLattConvType U} :=
  Joet_affine_hom (necset_mor (convType_hom_affine f)).
*)

Lemma necset_mor_id : FunctorLaws.id necset_mor.
Proof.
move=> a; rewrite hom_ext funeqE=> /= x /=.
apply necset_ext => /=.
by rewrite necset_morE' /= image_idfun.
Qed.
Lemma necset_mor_comp : FunctorLaws.comp necset_mor.
Proof.
move=> a b c [] g affine_g [] h affine_h; rewrite hom_ext funeqE => /= x /=.
apply necset_ext => /=.
rewrite 2!necset_morE' /= -imageA.
congr image.
by rewrite necset_morE'.
Qed.

Definition necset_functor :=
  Functor.Pack (Functor.Class necset_mor_id necset_mor_comp).

Lemma necset_mor_comp_fun (a b c : convType) (g : {hom b, c})
      (h : {hom a, b}):
  [fun of necset_mor [hom of [fun of g] \o [fun of h]]] =
  [fun of necset_mor g] \o [fun of necset_mor h].
Proof. by rewrite necset_mor_comp. Qed.

Local Notation CS := semiCompSemiLattConvType_category.
Local Notation CV := convType_category.

Definition forget_semiCompSemiLattConvType : functor CS CV.
set (m := [eta FId] : CS -> CV).
set (h := fun (a b : CS) (f : {hom CS; a, b}) =>
             @Hom.Pack CV a b _ (FId # f) (JoetAffine.base (Hom.class (FId # f))) : {hom CV; m a , m b}).
refine (@Functor.Pack CS CV m _).
refine (@Functor.Class _ _  m h  _ _); by move=> *; apply hom_ext. 
Defined.

Lemma forget_semiCompSemiLattConvTypeE :
  (forall a : CS, forget_convType a = a)
  /\ (forall a b (f : {hom CS; a , b}), forget_semiCompSemiLattConvType # f = f :> (a -> b)).
Proof. done. Qed.
End necset_functor.

(*
  eps1 is the counit of the adjunction (necset -| coercion),
  where the coercion is from semiCompSemiLattConvType to convType.
*)
Section eps1_eta1.
Import category.
Local Open Scope classical_set_scope.

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
transitivity (Joet `NE (conv_set p X Y)); last by rewrite Joet_conv_setD.
congr (Joet `NE _); apply/neset_ext => /=.
rewrite conv_setE necset_convType.convE.
apply eqEsubset=> u.
- case=> x [] y [] xX [] yY ->.
  exists x; first by rewrite -in_setE.
  by exists y; first by rewrite -in_setE.
- case=> x Xx [] y Yy <-.
  by exists x, y; rewrite !in_setE.
Qed.

Lemma eps1''_natural (K L : semiCompSemiLattConvType) (f : {hom K , L}) :
  f \o eps1'' =
  eps1'' \o (necset_functor \O forget_semiCompSemiLattConvType) # f.
Proof.
rewrite FCompE /= /id_f.
rewrite funeqE => X /=; rewrite apply_affine.
congr (Joet `NE _); by rewrite necset_morE.
Qed.

Definition eps1' : necset_functor \O forget_semiCompSemiLattConvType ~~> FId :=
  fun L => @Hom.Pack semiCompSemiLattConvType_category _ _ _ (@eps1'' L) (JoetAffine.Class (@eps1''_affine L) (@eps1''_Joet_morph L)).

Lemma eps1'_natural : naturality _ _ eps1'.
Proof. by move=> K L f; rewrite eps1''_natural. Qed.

Definition eps1 : necset_functor \O forget_semiCompSemiLattConvType ~> FId :=
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
Definition eta1' : FId ~~> forget_semiCompSemiLattConvType \O necset_functor :=
  fun C => @Hom.Pack convType_category _ _ _ (@eta1'' C) (@eta1''_affine C).
Lemma eta1'_natural : naturality _ _ eta1'.
Proof.
move=> a b h; rewrite funeqE=> x; apply necset_ext => /=.
by rewrite /eta1' /= /id_f necset_morE'/= image_set1.
Qed.
Definition eta1 : FId ~> forget_semiCompSemiLattConvType \O necset_functor :=
  locked (Natural.Pack (Natural.Class eta1'_natural)).
Lemma eta1E': eta1 = Natural eta1'_natural.
Proof. by rewrite /eta1; unlock. Qed.
Lemma eta1E (C : convType) : eta1 C = (@necset1 _) :> (_ -> _).
Proof. by rewrite /eta1; unlock. Qed.
Lemma eta1E'' (C : convType) (x : C) : eta1 C x = necset1 x.
Proof. by rewrite /eta1; unlock. Qed.

Import homcomp_notation.
Local Notation F := necset_functor.
Local Notation G := forget_semiCompSemiLattConvType.
Lemma necset1E (T : convType) (t : T) : necset1 t = [set t] :> set T.
Proof. done. Qed.
Lemma triL1 c : (eps1 (F c)) \o (F # eta1 c) = idfun.
Proof.
apply funext=> x /=; apply/necset_ext=> /=.
rewrite eps1E eta1E' /= necset_morE' /= /eta1'' /=.
rewrite -[in RHS](hull_cset x); congr hull.
apply/eqEsubset=> a /=.
- case=> y [] b xb <-.
  by rewrite necset1E => ->.
- move=> xa.
  exists (necset1 a); last by rewrite necset1E.
  by exists a.
Qed.
Lemma triR1 d : (G # eps1 d) \o (eta1 (G d)) = idfun.
Abort.

End eps1_eta1.

Section join1.
Local Open Scope convex_scope.
Local Open Scope classical_set_scope.

Definition join1' (C : convType) (s : necset (necset_convType C)) : {convex_set C} :=
  CSet.Pack (CSet.Class (convex_hull (classical_sets.bigsetU s (fun x => if x \in s then (x : set _) else cset0 _)))).

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
  NECSet.Pack (NECSet.Class (CSet.Class (convex_hull _)) (NESet.Class (join1'_neq0 s))).

Lemma eps1_correct (C : convType) (s : necset (necset_convType C)) :
  eps1'' s = join1 s.
Proof.
rewrite /eps1'' /join1 /=; apply/necset_ext => /=; congr (hull _).
rewrite /bigsetU; rewrite funeqE => c; rewrite propeqE; split.
- by case=> X sX Xc; exists X => //; rewrite -in_setE in sX; rewrite sX.
- by case=> X sX; rewrite -in_setE in sX; rewrite sX => Xc; exists X => //; rewrite -in_setE.
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
(* P_delta = (forget) \o necset \o Dist \o gen_choiceType, where
   - gen_choiceType is the free choiceType functor,
   - Dist is the free convex space functor, and
   - necset is the convex powerset functor. *)

Definition P_delta_left :=
  necset_functor \O Dist_functor \O gen_choiceType_functor.

Definition P_delta_right :=
  forget_choiceType
    \O forget_convType
    \O forget_semiCompSemiLattConvType.

(* action on objects *)
Definition P_delta_acto (T : Type) : Type := P_delta_left T.

Definition P_delta : functor Type_category Type_category :=
  P_delta_right \O P_delta_left.

Lemma eps0_Dist1 (A : Type) (d : P_delta_acto A) : eps0 _ (Dist1.d d) = d.
Proof.
rewrite eps0E; apply: (@ScaledConvex.S1_inj _ _ d).
rewrite S1_Convn_indexed_over_finType /=.
rewrite (eq_bigr (fun=> ScaledConvex.S1 d)); last first.
  move=> i _; rewrite dist_of_DistE Dist1.dE /= -(Dist1.supp d).
  rewrite fsvalP ScaledConvex.scalept1 /=; congr (ScaledConvex.S1 _).
  case: i => i Hi /=; rewrite Dist1.supp inE in Hi; exact/eqP.
by rewrite big_const (_ : #| _ | = 1) // -cardfE Dist1.supp cardfs1.
Qed.
End P_delta_functor.

Section P_delta_category_monad.
Import category.

Local Notation F1 := necset_functor.
Local Notation F0 := Dist_functor.
Local Notation FC := gen_choiceType_functor.
Local Notation UC := forget_choiceType.
Local Notation U0 := forget_convType.
Local Notation U1 := forget_semiCompSemiLattConvType.

Definition eps : P_delta_left \O P_delta_right ~> FId :=
  locked
  (eps1
     \v [NId F1 \O FId \O U1 , F1 \O U1]
     \v ((NId F1) \h eps0 \h (NId U1))
     \v [NId F1 \O F0 \O FId \O U0 \O U1 , F1 \O (F0 \O U0) \O U1 ]
     \v ((NId F1) \h (NId F0)\h epsC \h (NId U0) \h (NId U1))
     \v [NId P_delta_left \O P_delta_right , F1 \O F0 \O (FC \O UC) \O U0 \O U1]
  ).
Definition ret : FId ~> P_delta :=
  locked
  ([NId UC \O U0 \O (U1 \O F1) \O F0 \O FC , P_delta]
     \v ((NId UC) \h (NId U0) \h eta1 \h (NId F0) \h (NId FC))
     \v [NId UC \O (U0 \O F0) \O FC , UC \O U0 \O FId \O F0 \O FC]
     \v ((NId UC) \h eta0 \h (NId FC))
     \v [NId UC \O FC , UC \O FId \O FC]
     \v etaC
  ).

Import homcomp_notation.

Lemma epsE' :
  eps =
  eps1
    \v [NId F1 \O FId \O U1 , F1 \O U1]
    \v ((NId F1) \h eps0 \h (NId U1))
    \v [NId F1 \O F0 \O FId \O U0 \O U1 , F1 \O (F0 \O U0) \O U1 ]
    \v ((NId F1) \h (NId F0) \h epsC \h (NId U0) \h (NId U1))
    \v [NId P_delta_left \O P_delta_right , F1 \O F0 \O (FC \O UC) \O U0 \O U1].
Proof. by rewrite /eps; unlock. Qed.
Lemma retE' :
  ret =
  [NId UC \O U0 \O (U1 \O F1) \O F0 \O FC , P_delta]
     \v ((NId UC) \h (NId U0) \h eta1 \h (NId F0) \h (NId FC))
     \v [NId UC \O (U0 \O F0) \O FC , UC \O U0 \O FId \O F0 \O FC]
     \v ((NId UC) \h eta0 \h (NId FC))
     \v [NId UC \O FC , UC \O FId \O FC]
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
  ((eps1 _) \o (necset_mor (eps0 _)) \o (necset_mor (Dist_mor (epsC _))))
    :> (_ -> _).
Proof.
rewrite epsE''; cbn.
congr funcomp; congr funcomp.
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
  ret T = (@necset1 _) \o (@Dist1.d (gen_choiceType T)) :> (_ -> _).
Proof.
rewrite funeqE => x; apply necset_ext.
by rewrite /ret; unlock; rewrite /= etaCE eta0E eta1E Distfmap_id.
Qed.

Definition join : P_delta \O P_delta ~> P_delta :=
  [NId P_delta_right \O FId \O P_delta_left, P_delta]
    \v ((NId P_delta_right) \h eps \h (NId P_delta_left))
    \v [NId P_delta \O P_delta ,
        (P_delta_right \O (P_delta_left \O P_delta_right)) \O P_delta_left].

Lemma joinE' (T : Type) :
  join T = ((NId P_delta_right) \h eps \h (NId P_delta_left)) T :> (_ -> _).
Proof. reflexivity. Qed.

Lemma joinE (T : Type) :
  join T = @eps (P_delta_left T) :> (_ -> _).
Proof.
rewrite /join.
by rewrite !VCompE HCompId HIdComp funcompfid.
Qed.

Lemma ret_natural : JoinLaws.ret_naturality ret.
Proof. exact: (natural ret). Qed.
Lemma join_natural : JoinLaws.join_naturality join.
Proof. exact: (natural join). Qed.
Lemma join_left_unit : JoinLaws.join_left_unit ret join.
Proof.
rewrite /JoinLaws.join_left_unit => a.
rewrite funeqE=> d.
rewrite -homcompE joinE retE.
rewrite epsE funcompE -homcompE eps1E.
rewrite -[in RHS](Joet1 d); congr (Joet `NE _).
rewrite 2!necset_morE; apply/neset_ext => /=.
rewrite 2!image_set1 Distfmap1.
by rewrite epsCE eps0_Dist1.
Qed.
Lemma join_right_unit : JoinLaws.join_right_unit ret join.
Proof.
rewrite /JoinLaws.join_right_unit => a.
rewrite joinE.
(* NB: maybe worth factoring out? *)
have -> :
  forall x y (f : {hom x, y}) , P_delta # f = P_delta_left # f :> (_ -> _)
    by move=> x y f; apply funext.
move: (AdjComp.triL triL0 triL1) => triL01.
move: (AdjComp.triL triLC triL01 a) <-.
congr funcomp.
- rewrite epsE' /AdjComp.Eps /AdjComp.F; cbn.
  rewrite 4!funcompfid.
  congr funcomp.
  by rewrite -NIdFComp !HCompId !HIdComp.
- rewrite retE' /P_delta_left /AdjComp.Eta /AdjComp.G /AdjComp.F.
  congr Fun.
  rewrite /P_delta /P_delta_right /P_delta_left hom_ext.
  rewrite !VCompE ![in RHS]HCompE !VCompE !funcompfid !funcompidf.
  by rewrite -!NIdFComp !HCompId !HIdComp.
Qed.

Lemma joinA : JoinLaws.join_associativity join.
Proof.
rewrite /JoinLaws.join_associativity=> a.
rewrite 2![in RHS]joinE (natural eps _ _ (eps (P_delta_left a))).
rewrite joinE FCompE.
(* NB: maybe worth factoring out? *)
have-> :
  forall x y (f : {hom x, y}) , P_delta # f = P_delta_left # f :> (_ -> _)
    by move=> x y f; apply funext.
congr funcomp; congr [fun of P_delta_left # _].
by rewrite hom_ext joinE funeqE.
Qed.

Definition P_delta_monadMixin : Monad.mixin_of P_delta :=
  Monad.Mixin
    ret_natural
    join_natural
    join_left_unit
    join_right_unit
    joinA.
Definition m := Monad_of_category_monad
                  (Monad.Pack (Monad.Class P_delta_monadMixin)).
End P_delta_category_monad.
