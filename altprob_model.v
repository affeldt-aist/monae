Require Import Reals.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import boolp classical_sets.
From mathcomp Require Import finmap.
From infotheo Require Import Reals_ext Rbigop ssrR proba fsdist convex_choice.
From infotheo Require Import necset.
Require category.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* work in progress, this file contains admitted proofs *)

Require Import monae_lib monad fail_monad proba_monad monad_model gcm_model.

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

Lemma image_FSDistfmap A B (x : m A) (k : choice_of_Type A -> m B) :
  FSDistfmap k @` x = (m # k) x.
Proof.
rewrite /Fun /= /category.Monad_of_category_monad.f /= /category.id_f /=.
by rewrite/free_semiCompSemiLattConvType_mor /=; unlock.
Qed.

Lemma FunaltDr (A B : Type) (x y : m A) (k : A -> m B) :
  (m # k) (x [+] y) = (m # k) x [+] (m # k) y.
Proof.
apply necset_ext => /=.
transitivity (FSDistfmap (k : choice_of_Type A -> _) @` hull (\bigcup_(x0 in [set x; y]) x0)).
  have -> : hull (\bigcup_(x0 in [set x; y]) x0) = x [+] y by [].
  by rewrite image_FSDistfmap.
transitivity (hull (FSDistfmap (k : choice_of_Type A -> _) @` (\bigcup_(x0 in [set x; y]) x0))).
  rewrite image_preserves_convex_hull' //= => a b t.
  by rewrite /affine_function_at /f /FSDistfmap ConvFSDist.bind_left_distr.
congr hull; rewrite funeqE => /= d; rewrite propeqE; split.
- case => d' [x0] -[->{x0} xd' <-{d}|->{x0} xd' <-{d}].
  + exists ((m # k) x); [by left | rewrite -image_FSDistfmap; by exists d'].
  + exists ((m # k) y); [by right | rewrite -image_FSDistfmap; by exists d'].
- case => /= D -[->{D}|->{D}]; rewrite -image_FSDistfmap.
  + case=> d' xd' <-{d}; exists d' => //; exists x => //; by left.
  + case=> d' xd' <-{d}; exists d' => //; exists y => //; by right.
Qed.

Lemma FunpchoiceDr (A B : Type) (x y : m A) (k : A -> m B) p :
  (m # k) (x <|p|> y) = (m # k) x <|p|> (m # k) y.
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
  rewrite -in_setE necset_convType.convE inE; apply/asboolP; exists z1, z2.
  by rewrite !in_setE.
Qed.

Section bindaltDl.
Lemma bindaltDl : BindLaws.left_distributive (@Bind m) alt.
Proof.
move=> A B x y k.
rewrite !bindE /alt FunaltDr.
suff -> : forall T (u v : m (m T)), Join (u [+] v : m (m T)) = Join u [+] Join v by [].
move=> T u v.
Import category.
Import homcomp_notation.
Local Notation F1 := free_semiCompSemiLattConvType.
Local Notation F0 := free_convType.
Local Notation FC := free_choiceType.
Local Notation UC := forget_choiceType.
Local Notation U0 := forget_convType.
Local Notation U1 := forget_semiCompSemiLattConvType.
rewrite /= /Monad_of_category_monad.join /=.
rewrite HCompId HIdComp epsE'' !HCompId -!NIdFComp !HIdComp.
have-> : (F1 \O F0) # epsC (U0 (U1 (P_delta_left T))) = idfun :> (_ -> _).
  have -> : epsC (U0 (U1 (P_delta_left T))) =
            [NEq _, _] _ by rewrite hom_ext /= epsCE.
  by rewrite functor_id.
rewrite compfid.
admit.
Admitted.
End bindaltDl.

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

Section bindchoiceDl.
Lemma bindchoiceDl p : BindLaws.left_distributive (@Bind m) (@choice p).
move=> A B x y k.
rewrite !bindE /choice FunpchoiceDr.
suff -> : forall T (u v : m (m T)), Join (u <|p|> v : m (m T)) = Join u <|p|> Join v by [].
move=> T u v.
Import category.
Import homcomp_notation.
Local Notation F1 := free_semiCompSemiLattConvType.
Local Notation F0 := free_convType.
Local Notation FC := free_choiceType.
Local Notation UC := forget_choiceType.
Local Notation U0 := forget_convType.
Local Notation U1 := forget_semiCompSemiLattConvType.
rewrite /= /Monad_of_category_monad.join /=.
rewrite HCompId HIdComp epsE'' !HCompId -!NIdFComp !HIdComp.
have-> : (F1 \O F0) # epsC (U0 (U1 (P_delta_left T))) = idfun :> (_ -> _).
  have -> : epsC (U0 (U1 (P_delta_left T))) =
            [NEq _, _] _ by rewrite hom_ext /= epsCE.
  by rewrite functor_id.
rewrite compfid.
admit.
Admitted.
End bindchoiceDl.

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
