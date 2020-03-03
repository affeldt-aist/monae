(* wip on the relations of axioms over monadAltProb - distributivity *)

Require Import Reals Lra.
From mathcomp Require Import all_ssreflect.
From mathcomp Require boolp.
From infotheo Require Import ssrR Reals_ext proba.
From infotheo Require convex_choice.
Require Import monae_lib monad fail_monad proba_monad.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module MonadAltProbNoDistr.
Record class_of (m : Type -> Type) := Class {
  base : MonadAltCI.class_of m ;
  base2 : MonadProb.mixin_of (Monad.Pack (MonadAlt.base (MonadAltCI.base base))) }.
Structure t : Type := Pack { m : Type -> Type ; class : class_of m }.
Definition baseType (M : t) : altCIMonad := MonadAltCI.Pack (base (class M)).
Definition altType (M : t) : altMonad := MonadAlt.Pack (MonadAltCI.base (base (class M))).
Module Exports.
Notation altProbNoDistrMonad := t.
Coercion baseType : altProbNoDistrMonad >-> altCIMonad.
Canonical baseType.
Definition altprobnodistr_is_prob M :=
  MonadProb.Pack (MonadProb.Class (base2 (class M))).
Canonical altprobnodistr_is_prob.
Canonical altType.
End Exports.
End MonadAltProbNoDistr.
Export MonadAltProbNoDistr.Exports.

(* TODO: move to convex *)
Section misc_convex.
Import convex_choice.
Local Open Scope convex_scope.

Lemma convDif (C : convType) (b : bool) (p : prob) (x y z w : C) :
  (if b then x <| p |> y else z <| p |> w) =
  (if b then x else z) <| p |> (if b then y else w).
Proof. by case: b. Qed.
End misc_convex.

Require Import FunctionalExtensionality.
Section examples.
Local Open Scope proba_monad_scope.
Local Open Scope monae_scope.

Variable M : altProbNoDistrMonad.

(* problematic right-distributivity of bind *)
Definition Ax_prob_bindDr := forall p, BindLaws.right_distributive (@Bind M) (Choice p).

(* another problematic distributivity: nondeterminism over probability *)
Definition Ax_choiceDalt := forall (T : Type) p,
    right_distributive (fun x y => x [~] y) (fun x y : M T => x <| p |> y).

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

Example Keimel_appendix :
  Ax_choiceDalt -> forall (T : Type) (p q : prob) (x y : M T), x <|p|> y = x <|q|> y.
Abort.

End examples.
