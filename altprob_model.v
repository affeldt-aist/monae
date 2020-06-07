Require Import Reals.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import boolp classical_sets.
From mathcomp Require Import finmap.
From infotheo Require Import Reals_ext Rbigop ssrR fdist fsdist convex_choice.
From infotheo Require Import necset.
Require category.
Require Import monae_lib hierarchy monad_lib proba_lib monad_model gcm_model.

(******************************************************************************)
(*                  Model of the monad type altProbMonad                      *)
(*                                                                            *)
(* gcmAP == model of a monad that combines non-deterministic choice and       *)
(*          probability, built on top of the geometrically convex monad       *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope proba_scope.
Local Open Scope category_scope.

Section P_delta_altProbMonad.
Local Open Scope R_scope.
Local Open Scope reals_ext_scope.
Local Open Scope classical_set_scope.
Local Open Scope convex_scope.
Local Open Scope latt_scope.
Local Open Scope monae_scope.

Definition alt A (x y : gcm A) : gcm A := x [+] y.
Definition choice p A (x y : gcm A) : gcm A := x <| p |> y.

Lemma altA A : associative (@alt A).
Proof. by move=> x y z; rewrite /alt lub_binaryA. Qed.

Lemma image_FSDistfmap A B (x : gcm A) (k : choice_of_Type A -> gcm B) :
  FSDistfmap k @` x = (gcm # k) x.
Proof.
rewrite /Actm /= /category.Monad_of_category_monad.f /= /category.id_f /=.
by rewrite/free_semiCompSemiLattConvType_mor /=; unlock.
Qed.

Lemma FunaltDr (A B : Type) (x y : gcm A) (k : A -> gcm B) :
  (gcm # k) (x [+] y) = (gcm # k) x [+] (gcm # k) y.
Proof.
apply necset_ext => /=.
rewrite -(image_FSDistfmap (x [+] y) (fun x : choice_of_Type A => k x)).
rewrite -FunctionalExtensionality.eta_expansion.
rewrite image_preserves_convex_hull'; last exact: FSDistfmap_affine.
congr hull; rewrite funeqE => /= d; rewrite propeqE; split.
- case => d' [x0] -[->{x0} xd' <-{d}|->{x0} xd' <-{d}].
  + exists ((gcm # k) x); [by left | rewrite -image_FSDistfmap; by exists d'].
  + exists ((gcm # k) y); [by right | rewrite -image_FSDistfmap; by exists d'].
- case => /= D -[->{D}|->{D}]; rewrite -image_FSDistfmap.
  + case=> d' xd' <-{d}; exists d' => //; exists x => //; by left.
  + case=> d' xd' <-{d}; exists d' => //; exists y => //; by right.
Qed.

Lemma FunpchoiceDr (A B : Type) (x y : gcm A) (k : A -> gcm B) p :
  (gcm # k) (x <|p|> y) = (gcm # k) x <|p|> (gcm # k) y.
Proof.
apply necset_ext => /=.
rewrite -[in LHS]image_FSDistfmap funeqE => d; rewrite propeqE; split.
- move=> -[d'].
  rewrite necset_convType.convE => -[x0 [y0 [x0x [y0y ->{d'}]]]] <-{d}.
  rewrite necset_convType.convE /=.
  exists (FSDistfmap (k : choice_of_Type _ -> _ ) x0),
     (FSDistfmap (k : choice_of_Type _ -> _ ) y0); split.
  by rewrite in_setE -image_FSDistfmap; exists x0 => //; rewrite -in_setE.
  split; last exact: ConvFSDist.bind_left_distr.
  by rewrite in_setE -image_FSDistfmap; exists y0 => //; rewrite -in_setE.
- rewrite necset_convType.convE => -[/= d1 [d2]].
  rewrite in_setE -image_FSDistfmap => -[] [z1 xz1 <-{d1}].
  rewrite in_setE -image_FSDistfmap => -[] [z2 xz2 <-{d2}].
  move=> ->{d}; exists (z1 <|p|> z2); last exact: ConvFSDist.bind_left_distr.
  rewrite -in_setE necset_convType.convE; apply/asboolP; exists z1, z2.
  by rewrite !in_setE.
Qed.

Section bindaltDl.
Import category.
Import comps_notation.
Local Notation F1 := free_semiCompSemiLattConvType.
Local Notation F0 := free_convType.
Local Notation FC := free_choiceType.
Local Notation UC := forget_choiceType.
Local Notation U0 := forget_convType.
Local Notation U1 := forget_semiCompSemiLattConvType.

Lemma affine_F1e0U1PD_alt T (u v : gcm (gcm T)) :
  (F1 # eps0 (U1 (P_delta_left T)))%category (u [+] v) =
  (F1 # eps0 (U1 (P_delta_left T)))%category u [+] (F1 # eps0 (U1 (P_delta_left T)))%category v.
Proof.
rewrite [in LHS]/lub_binary -lub_op_hull.
have huv : NECSet.class_of (hull [set u; v]).
  apply: (NECSet.Class (CSet.Class (hull_is_convex _)) (NESet.Mixin _)).
  rewrite hull_eq0; apply/eqP => /(congr1 (fun x => x u)).
  by rewrite propeqE => -[X _]; apply X; left.
have @UV : necset_semiCompSemiLattConvType (F1 ((F0 \O U0) (U1 (P_delta_left T)))) := NECSet.Pack huv.
transitivity (|_| ((F1 # eps0 (U1 (P_delta_left T)))%category @` UV)%:ne).
  rewrite -(apply_affine (F1 # eps0 (U1 (P_delta_left T)))%category UV).
  congr (_ _); congr (|_| _); exact/neset_ext.
rewrite [in RHS]/lub_binary.
transitivity (|_| (hull ((F1 # eps0 (U1 (P_delta_left T)))%category @` [set u; v]))%:ne).
  congr (|_| _%:ne); apply/neset_ext => /=.
  have /image_preserves_convex_hull' : affine_function (F1 # eps0 (U1 (P_delta_left T)))%category.
    move=> a b p; rewrite /affine_function_at => /=.
    rewrite /free_semiCompSemiLattConvType_mor /=; unlock; rewrite /free_semiCompSemiLattConvType_mor' /=.
    apply/necset_ext => /=; rewrite funeqE => X; rewrite propeqE; split.
    - case=> D.
      rewrite /Conv /= necset_convType.convE => -[x0 [y0 [x0a [y0a]]]] ->{D} <-{X}.
      rewrite /Conv /= necset_convType.convE.
      exists ((eps0 (necset_semiCompSemiLattConvType (FSDist_convType (choice_of_Type T)))) x0),
        ((eps0 (necset_semiCompSemiLattConvType (FSDist_convType (choice_of_Type T)))) y0).
      split.
        by rewrite in_setE /=; exists x0 => //; rewrite -in_setE.
      split.
        by rewrite in_setE /=; exists y0 => //; rewrite -in_setE.
      rewrite !eps0E.
      transitivity (eps0'' (ConvFSDist.d p x0 y0)) => //.
      by rewrite eps0''_affine.
    - rewrite /Conv /= necset_convType.convE => -[x0 [y0 []]].
      rewrite in_setE /= => -[] x1 ax1 <-{x0} [].
      rewrite in_setE /= => -[] x2 bx2 <-{y0} ->.
      rewrite /Conv /= necset_convType.convE; exists (x1 <|p|> x2).
      exists x1, x2.
      split; first by rewrite in_setE.
      split => //; by rewrite in_setE.
      rewrite eps0E.
      transitivity (eps0'' (ConvFSDist.d p x1 x2)) => //.
      by rewrite eps0''_affine.
  exact.
rewrite lub_op_hull; congr (|_| _%:ne).
apply/neset_ext => /=.
rewrite /free_semiCompSemiLattConvType_mor /=; unlock; rewrite /free_semiCompSemiLattConvType_mor' /=.
rewrite funeqE => /= X; rewrite propeqE; split.
- case => /= x0 -[|] -> <- /=; by [left | right].
- case=> -> /=; by [exists u => //; left | exists v => //; right].
Qed.

Lemma affine_e1PD_alt T (x y : El (F1 (FId (U1 (P_delta_left T))))) :
  (eps1 (P_delta_left T)) (x [+] y) =
  (eps1 (P_delta_left T)) x [+] (eps1 (P_delta_left T)) y.
Proof.
rewrite /lub_binary eps1E -lub_op_setU.
transitivity (|_| (hull (\bigcup_(x0 in [set x; y]) x0))%:ne); last first.
  rewrite lub_op_hull /=; apply/necset_ext => /=; congr hull.
  rewrite [in RHS]setU_bigsetU; apply classical_sets_ext.eq_bigcup => //.
  rewrite /bigsetU /= funeqE => /= X; rewrite propeqE; split.
  - case => /= x0 [] <- x0X; by [exists x0 => //; left | exists x0 => //; right].
  - case => x0 [] -> ?; by [exists x => //; left | exists y => //; right].
congr (|_| _%:ne); exact/neset_ext.
Qed.

Lemma bindaltDl : BindLaws.left_distributive (@hierarchy.Bind gcm) alt.
Proof.
move=> A B x y k.
rewrite !hierarchy.bindE /alt FunaltDr.
suff -> : forall T (u v : gcm (gcm T)), hierarchy.Join (u [+] v : gcm (gcm T)) = hierarchy.Join u [+] hierarchy.Join v by [].
move=> T u v.
rewrite /= /Monad_of_category_monad.join /=.
rewrite HCompId HIdComp !HCompId !HIdComp.
have-> : ((F1 \O F0) # epsC (U0 (U1 (P_delta_left T))))%category = idfun :> (_ -> _).
  have -> : epsC (U0 (U1 (P_delta_left T))) =
            [NEq _, _] _ by rewrite hom_ext /= epsCE.
  by rewrite functor_id.
by rewrite affine_F1e0U1PD_alt affine_e1PD_alt.
Qed.
End bindaltDl.

Definition P_delta_monadAltMixin : MonadAlt.mixin_of gcm :=
  MonadAlt.Mixin altA bindaltDl.
Definition gcmA : altMonad := MonadAlt.Pack (MonadAlt.Class P_delta_monadAltMixin).

Lemma altxx A : idempotent (@Alt gcmA A).
Proof. by move=> x; rewrite /Alt /= /alt lub_binaryxx. Qed.
Lemma altC A : commutative (@Alt gcmA A).
Proof. by move=> a b; rewrite /Alt /= /alt /= lub_binaryC. Qed.

Definition P_delta_monadAltCIMixin : MonadAltCI.class_of gcmA :=
  MonadAltCI.Class (MonadAltCI.Mixin altxx altC).
Definition gcmACI : altCIMonad := MonadAltCI.Pack P_delta_monadAltCIMixin.

Lemma choice0 A (x y : gcm A) : x <| 0%:pr |> y = y.
Proof. by rewrite /choice conv0. Qed.
Lemma choice1 A (x y : gcm A) : x <| 1%:pr |> y = x.
Proof. by rewrite /choice conv1. Qed.
Lemma choiceC A p (x y : gcm A) : x <|p|> y = y <|p.~%:pr|> x.
Proof. by rewrite /choice convC. Qed.
Lemma choicemm A p : idempotent (@choice p A).
Proof. by move=> m; rewrite /choice convmm. Qed.
Lemma choiceA A (p q r s : prob) (x y z : gcm A) :
  p = (r * s) :> R /\ s.~ = (p.~ * q.~)%R ->
  x <| p |> (y <| q |> z) = (x <| r |> y) <| s |> z.
Proof.
case=> H1 H2.
case/boolP : (r == 0%:pr) => r0.
  have p0 : p = 0%:pr by apply/prob_ext => /=; rewrite H1 (eqP r0) mul0R.
  rewrite p0 choice0 (eqP r0) choice0 (_ : q = s) //; apply/prob_ext => /=.
  by move: H2; rewrite p0 onem0 mul1R => /(congr1 onem); rewrite !onemK.
case/boolP : (s == 0%:pr) => s0.
  have p0 : p = 0%:pr by apply/prob_ext => /=; rewrite H1 (eqP s0) mulR0.
  rewrite p0 (eqP s0) 2!choice0 (_ : q = 0%:pr) ?choice0 //; apply/prob_ext.
  move: H2; rewrite p0 onem0 mul1R (eqP s0) onem0 => /(congr1 onem).
  by rewrite onemK onem1.
rewrite /choice convA (@r_of_pq_is_r _ _ r s) //; congr ((_ <| _ |> _) <| _ |> _).
by apply/prob_ext; rewrite s_of_pqE -H2 onemK.
Qed.

Section bindchoiceDl.
Import category.
Import comps_notation.
Local Notation F1 := free_semiCompSemiLattConvType.
Local Notation F0 := free_convType.
Local Notation FC := free_choiceType.
Local Notation UC := forget_choiceType.
Local Notation U0 := forget_convType.
Local Notation U1 := forget_semiCompSemiLattConvType.

Lemma affine_F1e0U1PD_conv T (u v : gcm (gcm T)) p :
  ((F1 # eps0 (U1 (P_delta_left T))) (u <|p|> v) =
   (F1 # eps0 (U1 (P_delta_left T))) u <|p|> (F1 # eps0 (U1 (P_delta_left T))) v)%category.
Proof.
rewrite /Conv /= /free_semiCompSemiLattConvType_mor /=; unlock.
rewrite /free_semiCompSemiLattConvType_mor' /=; apply/necset_ext => /=.
rewrite funeqE => /= X; rewrite propeqE; split.
  case => /= d0.
  rewrite necset_convType.convE => -[/= d1 [d2 [d1u [d2v ->{d0}]]]] <-{X}.
  rewrite necset_convType.convE; exists (eps0'' d1), (eps0'' d2); split.
    rewrite in_setE /=; exists d1; by [rewrite -in_setE | rewrite eps0E].
  split.
    rewrite in_setE /=; exists d2; by [rewrite -in_setE | rewrite eps0E].
  rewrite !eps0E.
  transitivity (eps0'' (ConvFSDist.d p d1 d2)) => //.
  by rewrite eps0''_affine.
rewrite necset_convType.convE => -[/= d1 [d2 []]].
rewrite in_setE /= => -[x1 ux1 <-{d1}] -[].
rewrite in_setE /= => -[x2 ux2 <-{d2}] ->{X}.
exists (x1 <|p|> x2); first by rewrite necset_convType.convE; exists x1, x2; rewrite 2!in_setE.
rewrite !eps0E.
transitivity (eps0'' (ConvFSDist.d p x1 x2)) => //.
by rewrite eps0''_affine.
Qed.

Lemma affine_e1PD_conv T (x y : El (F1 (FId (U1 (P_delta_left T))))) p :
  (eps1 (P_delta_left T)) (x <|p|> y) =
  (eps1 (P_delta_left T)) x <|p|> (eps1 (P_delta_left T)) y.
Proof.
rewrite eps1E -lub_op_conv_setD; congr (|_| _); apply/neset_ext => /=.
by rewrite -necset_convType.conv_conv_set.
Qed.

Lemma bindchoiceDl p : BindLaws.left_distributive (@hierarchy.Bind gcm) (@choice p).
move=> A B x y k.
rewrite !hierarchy.bindE /choice FunpchoiceDr.
suff -> : forall T (u v : gcm (gcm T)), hierarchy.Join (u <|p|> v : gcm (gcm T)) = hierarchy.Join u <|p|> hierarchy.Join v by [].
move=> T u v.
rewrite /= /Monad_of_category_monad.join /=.
rewrite HCompId HIdComp !HCompId !HIdComp.
have-> : ((F1 \O F0) # epsC (U0 (U1 (P_delta_left T))))%category = idfun :> (_ -> _).
  have -> : epsC (U0 (U1 (P_delta_left T))) =
            [NEq _, _] _ by rewrite hom_ext /= epsCE.
  by rewrite functor_id.
by rewrite affine_F1e0U1PD_conv affine_e1PD_conv.
Qed.
End bindchoiceDl.

Definition P_delta_monadProbMixin : MonadProb.mixin_of gcm :=
  MonadProb.Mixin choice0 choice1 choiceC choicemm choiceA bindchoiceDl.
Definition P_delta_monadProbMixin' :
  MonadProb.mixin_of (Monad.Pack (MonadAlt.base (MonadAltCI.base (MonadAltCI.class gcmACI)))) :=
  P_delta_monadProbMixin.
Definition gcmp : probMonad :=
  MonadProb.Pack (MonadProb.Class P_delta_monadProbMixin).

Lemma choicealtDr A (p : prob) :
  right_distributive (fun x y : gcmACI A => x <| p |> y) Alt.
Proof. by move=> x y z; rewrite /choice lub_binaryDr. Qed.

Definition P_delta_monadAltProbMixin : @MonadAltProb.mixin_of gcmACI choice :=
  MonadAltProb.Mixin choicealtDr.
Definition P_delta_monadAltProbMixin' :
  @MonadAltProb.mixin_of gcmACI (MonadProb.choice P_delta_monadProbMixin) :=
  P_delta_monadAltProbMixin.
Definition gcmAP : altProbMonad :=
  MonadAltProb.Pack (MonadAltProb.Class P_delta_monadAltProbMixin').
End P_delta_altProbMonad.

Section examples.
Local Open Scope proba_monad_scope.

(* An example that probabilistic choice in this model is not trivial:
   we can distinguish different probabilities. *)
Example gcmAP_choice_nontrivial (p q : prob) :
  p <> q ->
  Ret true <|p|> Ret false <> Ret true <|q|> Ret false :> gcmAP bool.
Proof.
move/eqP => pq.
apply/eqP.
apply: contra pq => /eqP Heq.
apply/eqP.
move: Heq.
rewrite !gcm_retE.
rewrite /Choice /= /Conv /= /necset_convType.conv /=.
unlock.
move/(f_equal (@NECSet.car _)) => /=.
rewrite /necset_convType.pre_pre_conv /=.
Local Open Scope convex_scope.
set mk1d := fun b : choice_of_Type bool => FSDist1.d b.
move/(f_equal (fun x : FSDist.t _ -> _ => x (mk1d true <|p|> mk1d false))).
set tmp := ex _.
move=> Heq.
have: tmp -> tmp by [].
rewrite {2}Heq /tmp {Heq tmp}.
case.
  exists (mk1d true).
  exists (mk1d false).
  split; first by apply/asboolP.
  split; by [|apply/asboolP].
move=> x [] y.
rewrite 2!in_setE 2!necset1E => -[] -> [] ->.
move/(f_equal (fun x : {dist (choice_of_Type bool)} => x true)) => /=.
rewrite /Conv /= !ConvFSDist.dE !FSDist1.dE !inE !eqxx.
case/boolP: ((true : choice_of_Type bool) == false) => [/eqP//|].
by rewrite !mulR1 !mulR0 !addR0 => _ ?; apply prob_ext.
Qed.
End examples.
