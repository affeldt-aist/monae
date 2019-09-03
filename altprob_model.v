Require Import Reals.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import choice fintype finfun bigop.
From mathcomp Require Import boolp classical_sets.
From mathcomp Require Import finmap.
From infotheo Require Import Reals_ext Rbigop ssrR proba fsdist convex_choice.
From infotheo Require Import necset.
Require category.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* work in progress *)

Require Import monad fail_monad proba_monad gcm_model.

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
