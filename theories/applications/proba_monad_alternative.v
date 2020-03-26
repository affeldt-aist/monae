(* wip on the relations of axioms over monadAltProb - distributivity *)

Require Import Reals Lra.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import Rstruct.
From mathcomp Require boolp.
From infotheo Require Import ssrR Reals_ext proba.
From infotheo Require Import fdist convex.
Require Import monae_lib hierarchy fail_lib proba_lib.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module MonadAltProbNoDistr.
Record class_of (m : Type -> Type) := Class {
  base : MonadAltCI.class_of m ;
  mixin_prob : MonadProb.mixin_of (Monad.Pack (MonadAlt.base (MonadAltCI.base base))) }.
Structure t : Type := Pack { m : Type -> Type ; class : class_of m }.
Definition baseType (M : t) : altCIMonad := MonadAltCI.Pack (base (class M)).
Definition altType (M : t) : altMonad := MonadAlt.Pack (MonadAltCI.base (base (class M))).
Module Exports.
Notation altProbNoDistrMonad := t.
Coercion baseType : altProbNoDistrMonad >-> altCIMonad.
Canonical baseType.
Definition altprobnodistr_is_prob M :=
  MonadProb.Pack (MonadProb.Class (mixin_prob (class M))).
Canonical altprobnodistr_is_prob.
Canonical altType.
Definition apndConvex {M} {A : Type} :=
  ConvexSpace.Pack (ConvexSpace.Class (prob_mixin (MonadProb.Pack (MonadProb.Class (mixin_prob (class M)))) A)).
End Exports.
End MonadAltProbNoDistr.
Export MonadAltProbNoDistr.Exports.


(* TODO: move to convex *)
Section misc_convex.
Local Open Scope convex_scope.

Lemma convDif (C : convType) (b : bool) (p : prob) (x y z w : C) :
  (if b then x <| p |> y else z <| p |> w) =
  (if b then x else z) <| p |> (if b then y else w).
Proof. by case: b. Qed.
End misc_convex.


Section misc_proba_monad.
Local Open Scope proba_monad_scope.
Lemma choiceE (M : probMonad) (A : Type) (p : prob) (a b : M A) :
  a <|p|> b = @Conv probConvex p a b.
Proof. done. Qed.

(*
Lemma choiceA' (M : probMonad) (A : Type) (p q : prob) (a b c : M A) :
  a <|p|> (b <|q|> c) = (a <|fdist.r_of_pq p q|> b) <|fdist.s_of_pq p q|> c.
Proof. by rewrite !choiceE convA. Qed.
*)
End misc_proba_monad.


Require Import FunctionalExtensionality.
Section examples.
Local Open Scope proba_monad_scope.
Local Open Scope monae_scope.
Local Open Scope proba_scope.
Local Open Scope R_scope.
Local Open Scope reals_ext_scope.

Variable M : altProbNoDistrMonad.

(* problematic right-distributivity of bind *)
Definition Ax_prob_bindDr := forall p, BindLaws.right_distributive (@Bind M) (Choice p).

(* another problematic distributivity: nondeterminism over probability *)
Definition Ax_choiceDalt := forall (T : Type) p,
    right_distributive (fun x y : M T => x [~] y) (fun x y : M T => x <| p |> y).

Definition Ax_choiceDalt' := forall (T : Type) p,
    left_distributive (fun x y : M T => x [~] y) (fun x y : M T => x <| p |> y).

Lemma choiceDaltLR : Ax_choiceDalt -> Ax_choiceDalt'.
Proof.
by move=> choiceDalt T p x y z; rewrite altC choiceDalt; congr Choice; rewrite altC.
Qed.

(* collapse of probabilistic choice *)
Definition Ax_collapsed_choice :=
  forall (T : Type) (p q : oprob) (x y : M T), x <|p|> y = x <|q|> y.

Lemma Abou_Saleh_technical_equality (T : Type) (x y : M T) :
  x [~] y = arb >>= fun b => if b then x else y.
Proof. by rewrite alt_bindDl !bindretf. Qed.

Lemma choiceDif (T : Type) (b : bool) (p : prob) (x y z w : M T) :
  (if b then x <| p |> y else z <| p |> w) =
  (if b then x else z) <| p |> (if b then y else w).
Proof. by case: b. Qed.

(* the right distr. of bind implies the distr. of nondeterminism over probability *)
Example Abou_Saleh_prob_bindDr_implies_choiceDalt :
  Ax_prob_bindDr -> Ax_choiceDalt.
Proof.
move=> prob_bindDr T p x y z.
rewrite -[in LHS](choicemm p x) Abou_Saleh_technical_equality.
transitivity (arb >>= (fun b : bool => (if b then x else y) <|p|> if b then x else z)). 
  by congr (@Bind M bool T (@arb M) _); apply functional_extensionality=> b; rewrite choiceDif.
by rewrite prob_bindDr -!Abou_Saleh_technical_equality.
Qed.

Section Keimel_A_3_lemmas.
Variables (T : Type).
Hypothesis choiceDalt : Ax_choiceDalt.

Lemma choiceDalt' : Ax_choiceDalt'.
Proof. by apply:choiceDaltLR. Qed.

Lemma Keimel_technical (p : prob) (x y : M T) : (x <|p|> y) [~] x = x <|p|> (x [~] y).
Proof. by rewrite choiceDalt' altmm altC. Qed.
Lemma Keimel_technical' (p : prob) (x y : M T) : (x <|p|> y) [~] y = (x [~] y) <|p|> y.
Proof. by rewrite choiceDalt' altmm altC. Qed.
Lemma Keimel_technical'' (p : prob) (x y : M T) :
  x <|p|> y = (x <|p|> (x [~] y)) <|p|> ((x [~] y) <|p|> y).
Proof. by rewrite -[LHS]altmm choiceDalt Keimel_technical Keimel_technical'. Qed.
Lemma Keimel_technical''' (p : prob) (x y : M T) :
  x <|p|> (x [~] y) = x <|(p * p)%:pr|> (x [~] y).
Proof.
case/boolP: (p != 1%:pr);
  last by move/negbNE/eqP->; rewrite !choiceE /=; congr (@Conv probConvex); apply val_inj; rewrite /= mul1R.
move=> pneq1.
rewrite (Keimel_technical'' p x (x [~] y)) altA altmm.
rewrite !choiceE -convA' ?p_of_rs1 ?negb_and ?pneq1 // !convmm.
rewrite (_ : [p_of p, p] = (p * p)%:pr) //.
by apply val_inj; rewrite /= p_of_rsE.
Qed.

Lemma Keimel_A_2 (x y : M T) (p0 q0 : oprob) :
  p0 != q0 -> x <|p0|> y = x <|q0|> y ->
  forall (p q : oprob), x <|p|> y = x <|q|> y.
Admitted.

Lemma Keimel_technical'''' (p q : oprob) (x y : M T) :
  x <|p|> (x [~] y) = x <|q|> (x [~] y).
Proof.
move/Keimel_A_2: (Keimel_technical''' p x y); apply=> //.
apply/eqP=> /(congr1 (Prob.p \o OProb.p)) /=.
(*
have pneq0: p != 0%:opr by case/andP: sp.
have ipneq0: / p <> 0 by apply invR_neq0;apply/eqP; case/andP: sp.
*)
rewrite -[in X in X = _](mulR1 p) eqR_mul2l;
by apply/eqP; rewrite ?oprob_neq0 // eq_sym oprob_neq1.
Qed.
End Keimel_A_3_lemmas.

Theorem Keimel_A_3 : Ax_choiceDalt -> Ax_collapsed_choice.
Proof.
move=> choiceDalt T p q x y.
set Y := RHS.
rewrite Keimel_technical'' //.
rewrite (Keimel_technical'''' choiceDalt p q x y).
rewrite [X in _ <|p|> X = Y]choiceC {2}altC.
rewrite (Keimel_technical'''' choiceDalt (p.~)%:opr (q.~)%:opr y x).
rewrite -[X in _ <|p|> X = Y]choiceC.
rewrite !choiceE convACA -!choiceE altC.
rewrite (Keimel_technical'''' choiceDalt p q x y).
rewrite [X in _ <|q|> X = Y]choiceC {2}altC.
rewrite (Keimel_technical'''' choiceDalt (p.~)%:opr (q.~)%:opr y x).
rewrite -[X in _ <|q|> X = Y]choiceC.
rewrite -[in X in _ <|q|> X = Y]altC.
by rewrite -Keimel_technical'' //.
Qed.

End examples.
