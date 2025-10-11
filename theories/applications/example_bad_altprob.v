(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2025 monae authors, license: LGPL-2.1-or-later               *)
From mathcomp Require Import all_ssreflect ssralg ssrnum finmap.
From mathcomp Require Import boolp classical_sets reals.
From infotheo Require Import classical_sets_ext realType_ext fdist proba.
From infotheo Require Import fsdist convex.
From HB Require Import structures.
Require Import preamble hierarchy monad_lib proba_lib alt_lib.
Require monad_model. (* for choice_of_Type *)


(* wip on the relations of axioms over monadAltProb - distributivity *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope monae_scope.
Local Open Scope proba_monad_scope.

HB.mixin Record isMonadProbDr {R : realType} (M : UU0 -> UU0) of MonadProb R M := {
  (* composition distributes rightwards over [probabilistic] choice *)
  (* WARNING: this should not be asserted as an axiom in conjunction with
     distributivity of <||> over [] *)
  choice_bindDr : forall p, BindLaws.right_distributive (@bind M) (choice p) }.

#[short(type=probDrMonad)]
HB.structure Definition MonadProbDr {R : realType} := {M of isMonadProbDr R M & }.

HB.mixin Record isMonadProbAlt {R : realType} (M : UU0 -> UU0)
    of MonadAltCIProbNoDistr R M :=
  { altDr : forall T p, right_distributive
      (fun x y : M T => x <| p |> y) (fun a b => a [~] b) }.

(* Bad combination 1 *)
#[short(type=probAltMonad)]
HB.structure Definition MonadProbAlt {R : realType} :=
  { M of isMonadProbAlt R M & }.

(* Bad combination 2 *)
#[short(type=altProbDrMonad)]
HB.structure Definition MonadAltProbDr {R : realType} :=
  { M of isMonadAltProb R M & isMonadProbDr R M }.

(* TODO: move to convex *)
Section misc_convex.

Local Open Scope convex_scope.

Lemma conv_if (R : realType) (C : convType R) (b : bool) (p : {prob R}) (x y z w : C) :
  (if b then x else z) <| p |> (if b then y else w) =
  (if b then x <| p |> y else z <| p |> w).
Proof. by case: b. Qed.

End misc_convex.

Section convex_monad_convex.
Variables (R : realType) (M : convexMonad R) (A : Type).
Local Notation c := monad_model.choice_of_Type.

Local Definition cma := c (M A).

HB.instance Definition _ := Choice.on cma.

(*HB.instance Definition  :=
  isConvexSpace.Build R cma (choice1 _) choicemm choiceC choiceA.*)

Definition probConvex := HB.pack_for (convType R) cma
  (isConvexSpace.Build R cma (choice1 _) choicemm choiceC choiceA).

End convex_monad_convex.

Arguments probConvex {R M A}.

Section misc_proba_monad.
Local Open Scope proba_monad_scope.

Lemma choiceE (R : realType) (M : probMonad R) (A : Type) (p : {prob R}) (a b : M A) :
  a <|p|> b = @conv R probConvex p a b.
Proof. done. Qed.

End misc_proba_monad.

Section examples.

Variables (R : realType)  (M : altCIProbNoDistrMonad R).

(* problematic right-distributivity of bind *)
Definition Ax_prob_bindDr := forall p, BindLaws.right_distributive (@bind M) (choice p).

(* another problematic distributivity: nondeterminism over probability *)
Definition Ax_choiceDalt := forall (T : Type) p,
    right_distributive (fun x y : M T => x [~] y) (fun x y : M T => x <| p |> y).

Definition Ax_choiceDalt' := forall (T : Type) p,
    left_distributive (fun x y : M T => x [~] y) (fun x y : M T => x <| p |> y).

Lemma choiceDaltLR : Ax_choiceDalt -> Ax_choiceDalt'.
Proof.
by move=> choiceDalt T p x y z; rewrite altC choiceDalt; congr choice; rewrite altC.
Qed.

(* collapse of probabilistic choice *)
Definition Ax_collapsed_choice :=
  forall (T : Type) (p q : {oprob R}) (x y : M T), x <|p|> y = x <|q|> y.

Lemma Abou_Saleh_technical_equality (T : Type) (x y : M T) :
  x [~] y = arb >>= fun b => if b then x else y.
Proof. by rewrite alt_bindDl !bindretf. Qed.

Lemma choiceDif (T : Type) (b : bool) (p : {prob R}) (x y z w : M T) :
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
  by congr (@bind M bool T (@arb M) _); apply: funext => b; rewrite choiceDif.
by rewrite prob_bindDr -!Abou_Saleh_technical_equality.
Qed.

Section Keimel_A_3_lemmas.
Variables (T : Type).
Hypothesis choiceDalt : Ax_choiceDalt.

Lemma choiceDalt' : Ax_choiceDalt'.
Proof. by apply:choiceDaltLR. Qed.

Lemma Keimel_technical (p : {prob R}) (x y : M T) : (x <|p|> y) [~] x = x <|p|> (x [~] y).
Proof. by rewrite choiceDalt' altmm altC. Qed.
Lemma Keimel_technical' (p : {prob R}) (x y : M T) : (x <|p|> y) [~] y = (x [~] y) <|p|> y.
Proof. by rewrite choiceDalt' altmm altC. Qed.
Lemma Keimel_technical'' (p : {prob R}) (x y : M T) :
  x <|p|> y = (x <|p|> (x [~] y)) <|p|> ((x [~] y) <|p|> y).
Proof. by rewrite -[LHS]altmm choiceDalt Keimel_technical Keimel_technical'. Qed.
Lemma Keimel_technical''' (p : {prob R}) (x y : M T) :
  x <|p|> (x [~] y) = x <|((p:R) * (p:R))%:pr|> (x [~] y).
Proof.
case/boolP: (p != 1%:pr);
  last by move/negbNE/eqP->; rewrite !choiceE /=; congr (@conv R probConvex); apply val_inj; rewrite /= mul1r.
move=> pneq1.
rewrite (Keimel_technical'' p x (x [~] y)) altA altmm.
rewrite !choiceE -convA' ?p_of_rs1 ?negb_and ?pneq1 // !convmm.
rewrite (_ : [p_of p, p] = ((p:R) * (p:R))%:pr) //.
by apply val_inj; rewrite /= p_of_rsE.
Qed.

Lemma Keimel_A_2 (x y : M T) (p0 q0 : {oprob R}) :
  p0 != q0 -> x <|p0|> y = x <|q0|> y ->
  forall (p q : {oprob R}), x <|p|> y = x <|q|> y.
Admitted.

Lemma Keimel_technical'''' (p q : {oprob R}) (x y : M T) :
  x <|p|> (x [~] y) = x <|q|> (x [~] y).
Proof.
have:= @Keimel_A_2 x (x [~] y) p (oprobmulr p p).
apply; last by rewrite -Keimel_technical'''.
apply/eqP => /(congr1 \val) /(congr1 \val) /=.
rewrite -[in LHS](mulr1 (p:R)).
move/mulfI; rewrite oprob_neq0 => /(_ erefl) /esym /eqP.
exact/negP/oprob_neq1.
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
