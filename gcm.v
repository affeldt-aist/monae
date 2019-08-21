Require Import Reals.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import choice fintype finfun bigop.
From infotheo Require Import Reals_ext Rbigop ssrR proba dist convex_choice.
From mathcomp Require Import boolp classical_sets.
From mathcomp Require Import finmap set.
From infotheo Require Import gcm.
Require category.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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
Admitted.
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
- rewrite mem_finsupp Dist1.dE /Dist1.f /= fsfunE inE eqxx.
  by apply/eqP/R1_neq_R0.
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
- rewrite [in RHS](bigID (fun i => i \in (finsupp x))) /=.
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
rewrite [in RHS](bigID (fun i => i \in (finsupp y))) /=.
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
  rewrite dist_of_DistE /=.
  rewrite DistBind.dE /DistBind.f imfset_id /=.
  rewrite fsfunE.
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
    by rewrite big1 // => c /negbTE Hc; rewrite Dist1.dE /Dist1.f fsfunE inE Hc mulR0 scalept0.
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
  rewrite dist_of_DistE Dist1.dE /Dist1.f fsfunE /=.
  have -> : i \in [fset f (fsval i0)] by rewrite -Hi0 inE.
  by rewrite -Hi0 mulR1.
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
move=> a b h; rewrite funeqE=> x.
by rewrite FIdf /eta0' /= /Distfmap /= DistBind1f.
Qed.
Definition eta0 : FId ~> forget_convType \O Dist_functor :=
  locked (Natural.Pack (Natural.Class eta0'_natural)).
Lemma eta0E' : eta0 = Natural eta0'_natural.
Proof. by rewrite /eta0; unlock. Qed.
Lemma eta0E (T : choiceType) : eta0 T = (@Dist1.d _) :> (_ -> _).
Proof. by rewrite /eta0; unlock. Qed.

Require Import Lra.
Lemma Dist1_inj (C : choiceType) (a b : C) : Dist1.d a = Dist1.d b -> a = b.
Proof.
move/eqP => ab; apply/eqP; apply: contraTT ab => ab.
apply/eqP => /(congr1 (fun x : Dist.t _ => x a)).
rewrite !Dist1.dE /Dist1.f !fsfunE !inE eqxx (negbTE ab); lra.
Qed.
Import homcomp_notation.
Import ScaledConvex.
Local Open Scope fset_scope.
Local Open Scope R_scope.
Local Notation F := Dist_functor.
Local Notation G := forget_convType.
Lemma triL0 c : (eps0 (F c)) \o (F # eta0 c) = idfun.
Proof.
apply funext=> x /=.

rewrite eps0E eta0E; apply: (@S1_inj _ _ x).
rewrite S1_Convn_indexed_over_finType /=.

have Y : forall (i : finsupp (Distfmap (Dist1.d (A:=c)) x)),
    exists a_x0 : prod (Dist (Dist c)) (FId c),
        a_x0.2 \in finsupp x /\
               a_x0.1 = Dist1.d (Dist1.d a_x0.2) /\
               fsval i \in finsupp a_x0.1.
- case=> i /= iP.
  move: iP; rewrite /Distfmap DistBind.supp=> /bigfcupP [] a /andP [].
  have-> : [fset Dist1.d (Dist1.d a0) | a0 in [fset a0 | a0 in finsupp x]] =
           [fset Dist1.d (Dist1.d a0) | a0 in finsupp x]
    by apply eq_imfset => //; move=> y/= ; rewrite inE /=.
  case/imfsetP=> x0 /= x0x ax0 _ ia.
  exists (a, x0).
  by split=> //; split.
set Ya := (fun i => match cid (Y i) with exist a_x0 _ => a_x0.1 end).
set Yx0 := (fun i => match cid (Y i) with exist a_x0 _ => a_x0.2 end).
set F := fun (i : finsupp (Distfmap (Dist1.d (A:=c)) x)) =>
           scalept (x (Yx0 i)) (S1 (fsval i)).
(*set F := fun (i0 : Dist_convType c) => scalept (x XX) (S1 i0).*)
(*evar (F : Dist c -> scaled_pt (Dist_convType c)).*)
rewrite (eq_bigr F); last first.
- move=> i _. 
  rewrite dist_of_DistE /Distfmap /=.
  rewrite /F /Yx0.
  case: i => i /= iP.
  case: (cid (Y.[iP])%fmap).
  case => a x0 /= [] x0x [] ax0 [] ia /=.
(*
  case=> i /= iP; rewrite dist_of_DistE /Distfmap /=.
  move: iP; rewrite /Distfmap DistBind.supp=> /bigfcupP [] a /andP [].
  have-> : [fset Dist1.d (Dist1.d a0) | a0 in [fset a0 | a0 in finsupp x]] =
           [fset Dist1.d (Dist1.d a0) | a0 in finsupp x]
    by apply eq_imfset => //; move=> y/= ; rewrite inE /=.
  case/imfsetP=> x0 /= x0x ax0 _ ia _.
*)
  suff -> : (DistBind.d x (fun a0 : c => Dist1.d (Dist1.d a0))) i = x x0 by done.
  rewrite DistBind.dE /DistBind.f fsfunE.
  have-> : [fset Dist1.d (Dist1.d a) | a in [fset a | a in finsupp x]] =
           [fset Dist1.d (Dist1.d a) | a in finsupp x]
    by apply eq_imfset => //; move=> y/= ; rewrite inE /=.
  have-> : \sum_(a0 <- finsupp x) x a0 * (Dist1.d (Dist1.d a0)) i =
           \sum_(a0 <- finsupp x) x a0 * (if i == Dist1.d a0 then 1 else 0)
    by apply eq_bigr=> a0 _; rewrite Dist1.dE /Dist1.f fsfunE inE.
  rewrite (bigID (fun a0 => i == Dist1.d a0)) /=.
  have-> : \sum_(i0 <- finsupp x | i != Dist1.d i0)
            x i0 * (if i == Dist1.d i0 then 1 else 0) = 0
    by rewrite big1 //= => a0; move/negbTE ->; rewrite mulR0.
  have-> : \sum_(i0 <- finsupp x | i == Dist1.d i0)
            x i0 * (if i == Dist1.d i0 then 1 else 0) =
           \sum_(i0 <- finsupp x | i == Dist1.d i0) x i0
    by apply eq_bigr=> a0 ->; rewrite mulR1.
  rewrite addR0.
  have/eqP -> : \bigcup_(d <- [fset Dist1.d (Dist1.d a) | a in finsupp x])
                 finsupp d  == [fset Dist1.d a | a in finsupp x].
  + rewrite eqEfsubset; apply/andP=> []; split; apply/fsubsetP=> a'.
    * case/bigfcupP=> x0' /andP [].
      case/imfsetP=> x1 /= Hx1 -> _.
      rewrite Dist1.supp inE=> /eqP ->.
      by apply/imfsetP; exists x1.
    * case/imfsetP=> x0' /= Hx0' ->; apply/bigfcupP.
      exists (Dist1.d (Dist1.d x0')) => //=; last by rewrite Dist1.supp inE.
      rewrite andbT; apply/imfsetP.
      by exists x0' => //; rewrite Dist1.supp inE.
  case: ifP.
  + case/imfsetP=> a' /= Ha' ia'; rewrite ia'.
    have-> : \sum_(i0 <- finsupp x | Dist1.d a' == Dist1.d i0) x i0 =
             \sum_(i0 <- finsupp x | a' == i0) x i0.
    * apply eq_bigl=> i0.
      apply/eqP; case: ifP; first by move/eqP ->.
      by move=> H /eq_Dist1 /eqP; rewrite H.
    suff <- : x a' = x x0.
      rewrite (eq_bigl _ _ (eq_sym _)) -big_filter filter_pred1_uniq //.
      by rewrite big_seq1.
    move: ia; rewrite ax0; rewrite Dist1.supp => /imfsetP [] x1 /=.
    rewrite inE => /eqP x1x0 ix1.
    by move: x1x0; rewrite -ix1 ia' => /eq_Dist1 ->.
  + move: ia; rewrite ax0 Dist1.supp=> /imfsetP [] x1 /=.
    rewrite inE=> /eqP x1x0 ix1.
    rewrite ix1 x1x0 /=.
    by rewrite in_imfset.
rewrite /F.
have H : finsupp (Distfmap (Dist1.d (A:=c)) x) =
         (@Dist1.d _) @` (finsupp x).
  rewrite /Distfmap DistBind.supp big_imfset /=; last by move=> c0 c1 ? ? /Dist1_inj/Dist1_inj.
  rewrite (eq_bigr (fun i => fset1 (Dist1.d i))); last by move=> ? _; rewrite Dist1.supp.
  (* TODO: extract lemma *)
  rewrite big_imfset //=; apply/fsetP => d; apply/bigfcupP/imfsetP.
  - by move=> -[c0]; rewrite andbT => c0x; rewrite inE => /eqP ->; exists c0.
  - by move=> -[c0] /= x0 ->; exists c0 => //; [rewrite andbT | rewrite inE].
have H' : forall i, Dist1.d (Yx0 i) = fsval i.
  move=> i.
  rewrite /Yx0.
  case: (cid (Y i)) => -[dd xc] /= [Hxc [->{dd}]].
  rewrite Dist1.supp /=.
  by rewrite inE => /eqP.
(*
have H'' : forall x0 : FId c, Dist1.d x0 \in finsupp (Distfmap (@Dist1.d c) x)
    by admit.
set x0Y := fun x0 : FId c => FSetSub (H'' x0). 
have H''' : forall x0 : FId c, Yx0 (x0Y x0) = x0 by admit.
*)
set D := Yx0 @` (dist_of_Dist.D (Distfmap (Dist1.d (A:=c)) x)).
Check D.
Check fun j : D => j.
(*
Check \ssum_(j <- D) scalept (x j) (S1 (fsval (x0Y j))).
Check \ssum_(j : D) scalept (x (fsval j)) (S1 (fsval (x0Y (fsval j)))).
*)
Check (@fsval ((@FId choiceType_category) c) D).
Check S1_Convn_indexed_over_finType.
Check (S1_Convn_indexed_over_finType _ (fun i : [finType of finsupp (Distfmap (Dist1.d (A:=c)) x)] => fsval i)).
evar (dxy : dist [finType of finsupp (Distfmap (Dist1.d (A:=c)) x)]).
have Hdxy : x \o Yx0 = dxy by admit.
rewrite (eq_bigr (fun i => scalept (dxy i) (S1 (fsval i)))); last first.
  by move=> i; rewrite -Hdxy.
rewrite -S1_Convn_indexed_over_finType; congr S1.


have -> : \ssum_i scalept (x (Yx0 i)) (S1 (fsval i)) =
          \ssum_(j <- D) scalept (x j) (S1 (fsval (x0Y j))) by admit.
Fail rewrite -S1_Convn_indexed_over_finType.
Admitted.

Lemma triR0 d : (G # eps0 d) \o (eta0 (G d)) = idfun.
Admitted.

End eps0_eta0.

Section join0.
Import category.
(* join operator for Dist *)
Definition join0 (C : choiceType) (d : Dist (Dist C)) : Dist C :=
  DistBind.d d (Dist_mor [hom of idfun]).

(* join0 is ((coercion) \o eps0) *)
Section eps0_correct.
Import ScaledConvex.
Local Open Scope R_scope.

Lemma eps0_correct (C : choiceType) (d : Dist (Dist C)) : eps0'' d = join0 d.
Proof.
rewrite /join0 -DistBindA DistBindp1; apply Dist_ext => c.
rewrite -[LHS]Scaled1RK /eps0''.
rewrite (@S1_proj_Convn_indexed_over_finType _ _ (fun D : Dist C => D c));
  last exact: Dist_eval_affine.
rewrite big_scaleR.
rewrite DistBind.dE /DistBind.f fsfunE.
case: ifP => [_ | ].
- transitivity (\sum_(i : dist_of_Dist.D d | true) d (fsval i) * (fsval i) c).
  + apply eq_bigr => -[v vP] _.
    move/scaleR_scalept:(dist_ge0 (dist_of_Dist d) [` vP]%fset) ->.
    by rewrite Scaled1RK dist_of_DistE.
  suff -> : finsupp d = [seq fsval i | i in [finType of finsupp d]] :> seq _
    by rewrite big_image; apply eq_bigl => a; rewrite inE.
  by rewrite enum_fsetE.
- rewrite !imfset_id.
  move/bigfcupP => H.
  have H' : forall i : Dist C, i \in finsupp d -> c \notin finsupp i
      by move=> i Hi; apply/negP => Hx; apply H; exists i => //; rewrite andbT.
  have H0 : 0 = \sum_(i | true) 0 by move=> t; rewrite big1.
  rewrite [in RHS](H0 (dist_of_Dist.D d)).
  apply eq_bigr => -[v vP] _.
  move/scaleR_scalept:(dist_ge0 (dist_of_Dist d) [`vP]%fset) ->.
  rewrite dist_of_DistE /= mul1R.
  suff -> : v c = 0 by rewrite mulR0.
  rewrite fsfun_dflt //.
  exact: H'.
Qed.
End eps0_correct.
End join0.

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

Import homcomp_notation.
Local Notation F := necset_functor.
Local Notation G := forget_semiCompSemiLattConvType.
Lemma triL1 c : (eps1 (F c)) \o (F # eta1 c) = idfun.
Admitted.
Lemma triR1 d : (G # eps1 d) \o (eta1 (G d)) = idfun.
Admitted.

End eps1_eta1.

Section join1.
Local Open Scope convex_scope.
Local Open Scope classical_set_scope.

Definition join1' (C : convType) (s : necset (necset_convType C)) : {convex_set C} :=
  CSet.Pack (CSet.Class (convex_hull (bigsetU s (fun x => if x \in s then (x : set _) else cset0 _)))).

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
  move=> i _; rewrite dist_of_DistE Dist1.dE /Dist1.f fsfunE /= -(Dist1.supp d).
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
- rewrite 2!HCompE 2!homcomp_hom homcompA -functor_o_fun.
  rewrite !NIdE funcompidf functor_id.
  by congr [fun of necset_mor _]; rewrite hom_ext /= funcompfid.
- do 2 rewrite HCompE homcomp_hom NIdE functor_id funcompfid.
  by rewrite HCompE homcomp_hom -NIdO_HComp NIdE funcompidf.
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
by rewrite /ret; unlock; rewrite /= etaCE eta0E eta1E /Distfmap /= DistBind1f.
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
do ! rewrite VCompE homcomp_hom.
rewrite funcompfid funcompidf.
rewrite HCompE homcomp_hom NIdE functor_id funcompfid.
by rewrite HCompE homcomp_hom NIdE funcompidf.
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
rewrite 2!image_set1 /Distfmap DistBind1f /=.
by rewrite epsCE eps0_Dist1.
Qed.
Lemma join_right_unit : JoinLaws.join_right_unit ret join.
Proof.
Admitted.

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

Require Import monad fail_monad proba_monad.

Section P_delta_monad.
End P_delta_monad.

Section P_delta_altProbMonad.
Local Open Scope R_scope.
Local Open Scope reals_ext_scope.
Local Open Scope classical_set_scope.
Local Open Scope proba_scope.
Local Open Scope convex_scope.
Local Open Scope latt_scope.

Definition alt A (x y : m A) : m A := x [+] y.
Definition choice p A (x y : m A) : m A := x <|p|> y.

Lemma altA A : associative (@alt A).
Proof. by move=> x y z; rewrite /alt joetA. Qed.
Lemma bindaltDl : BindLaws.left_distributive (@Bind m) alt.
Proof.
Admitted.

Definition P_delta_monadAltMixin : MonadAlt.mixin_of m :=
  MonadAlt.Mixin altA bindaltDl.
Definition mA : altMonad := MonadAlt.Pack (MonadAlt.Class P_delta_monadAltMixin).

Lemma altxx A : idempotent (@Alt mA A).
Proof. by move=> x; rewrite /Alt /= /alt joetxx. Qed.
Lemma altC A : commutative (@Alt mA A).
Proof. by move=> a b; rewrite /Alt /= /alt /= joetC. Qed.

Definition P_delta_monadAltCIMixin : MonadAltCI.class_of mA :=
  MonadAltCI.Class (MonadAltCI.Mixin altxx altC).
Definition mACI : altCIMonad := MonadAltCI.Pack P_delta_monadAltCIMixin.

Lemma choice0 A (x y : m A) : choice `Pr 0 x y = y.
Proof. by rewrite /choice conv0. Qed.
Lemma choice1 A (x y : m A) : choice `Pr 1 x y = x.
  (* NB(sai): redundant given choice0 and choiceC, isnt' it? NB(rei): yes*)
Proof. by rewrite /choice conv1. Qed.
Lemma choiceC A p (x y : m A) : choice p x y = choice `Pr p.~ y x.
Proof. by rewrite /choice convC. Qed.
Lemma choicemm A p : idempotent (@choice p A).
Proof. by move=> m; rewrite /choice convmm. Qed.
Lemma choiceA A (p q r s : prob) (x y z : m A) :
  p = (r * s) :> R /\ s.~ = (p.~ * q.~)%R ->
  choice p x (choice q y z) = choice s (choice r x y) z.
Proof.
case=> H1 H2.
case/boolP : (r == `Pr 0) => r0.
  have p0 : p = `Pr 0 by apply/prob_ext => /=; rewrite H1 (eqP r0) mul0R.
  rewrite p0 choice0 (eqP r0) choice0 (_ : q = s) //; apply/prob_ext => /=.
  by move: H2; rewrite p0 onem0 mul1R => /(congr1 onem); rewrite !onemK.
case/boolP : (s == `Pr 0) => s0.
  have p0 : p = `Pr 0 by apply/prob_ext => /=; rewrite H1 (eqP s0) mulR0.
  rewrite p0 (eqP s0) 2!choice0 (_ : q = `Pr 0) ?choice0 //; apply/prob_ext.
  move: H2; rewrite p0 onem0 mul1R (eqP s0) onem0 => /(congr1 onem).
  by rewrite onemK onem1.
rewrite /choice convA (@r_of_pq_is_r _ _ r s) //; congr ((_ <| _ |> _) <| _ |> _).
by apply/prob_ext; rewrite s_of_pqE -H2 onemK.
Qed.
Lemma bindchoiceDl p : BindLaws.left_distributive (@Bind m) (@choice p).
Admitted.

Definition P_delta_monadProbMixin : MonadProb.mixin_of m :=
  MonadProb.Mixin choice0 choice1 choiceC choicemm choiceA bindchoiceDl.
Definition P_delta_monadProbMixin' : MonadProb.mixin_of (Monad.Pack (MonadAlt.base (MonadAltCI.base (MonadAltCI.class mACI)))) := P_delta_monadProbMixin.

(*Definition mp : probMonad := MonadProb.Pack (MonadProb.Class P_delta_monadProbMixin).*)

Lemma choicealtDr A (p : prob) :
  right_distributive (fun x y : mACI A => choice p x y) (fun x y => Alt x y).
Proof. by move=> x y z; rewrite /choice joetDr. Qed.

Definition P_delta_monadAltProbMixin : @MonadAltProb.mixin_of mACI choice :=
  MonadAltProb.Mixin choicealtDr.
Definition P_delta_monadAltProbMixin' : @MonadAltProb.mixin_of mACI (MonadProb.choice P_delta_monadProbMixin) := P_delta_monadAltProbMixin.
Definition mAP : altProbMonad := MonadAltProb.Pack (MonadAltProb.Class P_delta_monadAltProbMixin').
End P_delta_altProbMonad.
