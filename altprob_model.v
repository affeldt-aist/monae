(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2020 monae authors, license: LGPL-2.1-or-later               *)
Require Import Reals.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import boolp classical_sets.
From mathcomp Require Import finmap.
From infotheo Require Import Reals_ext Rbigop ssrR fdist fsdist convex.
From infotheo Require Import necset.
Require category.
From HB Require Import structures.
Require Import monae_lib hierarchy monad_lib proba_lib monad_model gcm_model.
Require Import category.

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

Lemma altA A : ssrfun.associative (@alt A).
Proof. by move=> x y z; rewrite /alt lubA. Qed.

Lemma image_FSDistfmap A B (x : gcm A) (k : choice_of_Type A -> gcm B) :
  FSDistfmap k @` x = (gcm # k) x.
Proof.
rewrite /hierarchy.actm /= /category.Monad_of_category_monad.f /= /category.id_f /=.
by rewrite/free_semiCompSemiLattConvType_mor /=; unlock.
Qed.

Section funalt_funchoice.
Import category.
Import comps_notation.
Local Notation F1 := free_semiCompSemiLattConvType.
Local Notation F0 := free_convType.
Local Notation FC := free_choiceType.
Local Notation UC := forget_choiceType.
Local Notation U0 := forget_convType.
Local Notation U1 := forget_semiCompSemiLattConvType.
Lemma FunaltDr (A B : Type) (x y : gcm A) (k : A -> gcm B) :
  (gcm # k) (x [+] y) = (gcm # k) x [+] (gcm # k) y.
Proof.
rewrite /hierarchy.actm /=.
rewrite /Monad_of_category_monad.f /=.
case: (free_semiCompSemiLattConvType_mor
        (free_convType_mor (free_choiceType_mor (hom_Type k))))=> f /= [] Haf Hbf.
rewrite Hbf lubE.
congr biglub.
apply neset_ext=> /=.
by rewrite image_setU !image_set1.
Qed.

Lemma FunpchoiceDr (A B : Type) (x y : gcm A) (k : A -> gcm B) p :
  (gcm # k) (x <|p|> y) = (gcm # k) x <|p|> (gcm # k) y.
Proof.
rewrite /hierarchy.actm /=.
rewrite /Monad_of_category_monad.f /=.
case: (free_semiCompSemiLattConvType_mor
        (free_convType_mor (free_choiceType_mor (hom_Type k))))=> f /= [] Haf Hbf.
by apply Haf.
Qed.
End funalt_funchoice.

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
case: ((F1 # eps0 (U1 (P_delta_left T)))%category)=> f /= [] Haf Hbf.
rewrite !lubE Hbf.
congr biglub.
apply neset_ext=> /=.
by rewrite image_setU !image_set1.
Qed.

Lemma affine_e1PD_alt T (x y : el (F1 (FId (U1 (P_delta_left T))))) :
  (eps1 (P_delta_left T)) (x [+] y) =
  (eps1 (P_delta_left T)) x [+] (eps1 (P_delta_left T)) y.
Proof.
case: (eps1 (P_delta_left T))=> f /= [] Haf Hbf.
rewrite !lubE Hbf.
congr biglub.
apply neset_ext=> /=.
by rewrite image_setU !image_set1.
Qed.

Local Notation F1o := necset_semiCompSemiLattConvType.
Local Notation F0o := FSDist_convType.
Local Notation FCo := choice_of_Type.
Local Notation F1m := free_semiCompSemiLattConvType_mor.
Local Notation F0m := free_convType_mor.
Lemma bindaltDl : BindLaws.left_distributive (@hierarchy.bind gcm) alt.
Proof.
move=> A B x y k.
rewrite !hierarchy.bindE /alt FunaltDr.
suff -> : forall T (u v : gcm (gcm T)),
  hierarchy.Join (u [+] v : gcm (gcm T)) = hierarchy.Join u [+] hierarchy.Join v by [].
move=> T u v.
rewrite /= /join_ /=.
rewrite HCompId HIdComp /AdjComp.Eps.
do 3 rewrite VCompE_nat homfunK functor_o !compE.
rewrite !functor_id HCompId HIdComp.
rewrite (_ : epsC (U0 (U1 (F1o (F0o (FCo T))))) = [NEq _, _] _) ?hom_ext ?epsCE //.
rewrite NEqE !functor_id_hom.
by rewrite affine_F1e0U1PD_alt affine_e1PD_alt.
Qed.
End bindaltDl.

HB.instance Definition P_delta_monadAltMixin := @isMonadAlt.Build (Monad_of_category_monad.m'' Mgcm) alt altA bindaltDl.
(*Definition gcmA : altMonad := MonadAlt.Pack (MonadAlt.Class P_delta_monadAltMixin).*)

Lemma altxx A : idempotent (@alt A).
Proof. by move=> x; rewrite /= /alt lubxx. Qed.
Lemma altC A : commutative (@alt A).
Proof. by move=> a b; rewrite /= /alt /= lubC. Qed.

HB.instance Definition gcmACI := @isMonadAltCI.Build (Monad_of_category_monad.m'' Mgcm) altxx altC.
(*Definition gcmACI : altCIMonad := MonadAltCI.Pack P_delta_monadAltCIMixin.*)

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
  have p0 : p = 0%:pr by apply/val_inj; rewrite /= H1 (eqP r0) mul0R.
  rewrite p0 choice0 (eqP r0) choice0 (_ : q = s) //; apply/val_inj => /=.
  by move: H2; rewrite p0 onem0 mul1R => /(congr1 onem); rewrite !onemK.
case/boolP : (s == 0%:pr) => s0.
  have p0 : p = 0%:pr by apply/val_inj; rewrite /= H1 (eqP s0) mulR0.
  rewrite p0 (eqP s0) 2!choice0 (_ : q = 0%:pr) ?choice0 //; apply/val_inj.
  move: H2; rewrite p0 onem0 mul1R (eqP s0) onem0 => /(congr1 onem).
  by rewrite onemK onem1.
rewrite /choice convA (@r_of_pq_is_r _ _ r s) //; congr ((_ <| _ |> _) <| _ |> _).
by apply/val_inj; rewrite /= s_of_pqE -H2 onemK.
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
case: ((F1 # eps0 (U1 (P_delta_left T)))%category)=> f /= [] Haf Hbf.
by apply: Haf.
Qed.

Lemma affine_e1PD_conv T (x y : el (F1 (FId (U1 (P_delta_left T))))) p :
  (eps1 (P_delta_left T)) (x <|p|> y) =
  (eps1 (P_delta_left T)) x <|p|> (eps1 (P_delta_left T)) y.
Proof.
rewrite eps1E -biglub_conv_setD; congr (|_| _); apply/neset_ext => /=.
by rewrite -necset_convType.conv_conv_set.
Qed.

Local Notation F1o := necset_semiCompSemiLattConvType.
Local Notation F0o := FSDist_convType.
Local Notation FCo := choice_of_Type.
Local Notation F1m := free_semiCompSemiLattConvType_mor.
Local Notation F0m := free_convType_mor.
Lemma bindchoiceDl p : BindLaws.left_distributive (@hierarchy.bind gcm) (@choice p).
Proof.
move=> A B x y k.
rewrite !hierarchy.bindE /choice FunpchoiceDr.
suff -> : forall T (u v : gcm (gcm T)), hierarchy.Join (u <|p|> v : gcm (gcm T)) = hierarchy.Join u <|p|> hierarchy.Join v by [].
move=> T u v.
rewrite /= /Monad_of_category_monad.join /=.
rewrite /join_ /=.
rewrite HCompId HIdComp /AdjComp.Eps.
do 3 rewrite VCompE_nat homfunK functor_o !compE.
rewrite !functor_id HCompId HIdComp.
rewrite (_ : epsC (U0 (U1 (F1o (F0o (FCo T))))) = [NEq _, _] _) ?hom_ext ?epsCE //.
rewrite NEqE !functor_id_hom.
by rewrite affine_F1e0U1PD_conv affine_e1PD_conv.
Qed.
End bindchoiceDl.

HB.instance Definition P_delta_monadProbMixin :=
  isMonadProb.Build (Monad_of_category_monad.m'' Mgcm) choice0 choice1 choiceC choicemm choiceA bindchoiceDl.
(*Definition P_delta_monadProbMixin : MonadProb.mixin_of gcm :=
  MonadProb.Mixin choice0 choice1 choiceC choicemm choiceA bindchoiceDl.
Definition P_delta_monadProbMixin' :
  MonadProb.mixin_of (Monad.Pack (MonadAlt.base (MonadAltCI.base (MonadAltCI.class gcmACI)))) :=
  P_delta_monadProbMixin.
Definition gcmp : probMonad :=
  MonadProb.Pack (MonadProb.Class P_delta_monadProbMixin).*)

Lemma choicealtDr A (p : prob) :
  right_distributive (fun x y : (Monad_of_category_monad.m'' Mgcm) A => x <| p |> y) (@alt A).
Proof. by move=> x y z; rewrite /choice lubDr. Qed.

HB.instance Definition gcmAP :=
  @isMonadAltProb.Build (Monad_of_category_monad.m'' Mgcm) choicealtDr.
(*Definition P_delta_monadAltProbMixin : @MonadAltProb.mixin_of gcmACI choice :=
  MonadAltProb.Mixin choicealtDr.
Definition P_delta_monadAltProbMixin' :
  @MonadAltProb.mixin_of gcmACI (MonadProb.choice P_delta_monadProbMixin) :=
  P_delta_monadAltProbMixin.
Definition gcmAP : altProbMonad :=
  MonadAltProb.Pack (MonadAltProb.Class P_delta_monadAltProbMixin').*)
End P_delta_altProbMonad.

Section examples.
Local Open Scope proba_monad_scope.

(* An example that probabilistic choice in this model is not trivial:
   we can distinguish different probabilities. *)
Example gcmAP_choice_nontrivial (p q : prob) :
  p <> q ->
  hierarchy.Ret true <|p|> hierarchy.Ret false <> hierarchy.Ret true <|q|> hierarchy.Ret false :> (*gcmAP*) (Monad_of_category_monad.m'' Mgcm) bool.
Proof.
apply contra_not.
rewrite !gcm_retE /Choice /= /Conv /= => /(congr1 (@NECSet.car _)).
rewrite !necset_convType.convE !conv_cset1 /=.
move/(@classical_sets_ext.set1_inj _ (Conv _ _ _))/(congr1 (@FSDist.f _))/fsfunP/(_ true).
rewrite !ConvFSDist.dE !FSDist1.dE /=.
rewrite !(@in_fset1 (choice_of_Type bool)) eqxx /= ifF; last exact/negbTE/eqP.
by rewrite !mulR1 !mulR0 !addR0; exact: val_inj.
Qed.
End examples.
