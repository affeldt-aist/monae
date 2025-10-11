(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2025 monae authors, license: LGPL-2.1-or-later               *)
From mathcomp Require Import all_ssreflect ssralg ssrnum finmap.
From mathcomp Require Import boolp classical_sets reals.
From infotheo Require Import classical_sets_ext realType_ext fdist proba.
From infotheo Require Import fsdist convex.
From HB Require Import structures.
Require Import preamble hierarchy monad_lib proba_lib alt_lib.

(* This file contains consequences of combining MonadAltCI and MonadProb *)
(*   together with the other distributive law.                           *)
(*                                                                       *)
(* References:                                                           *)
(* [Abou-Saleh]:                                                         *)
(*  Abou-Saleh, F., Cheung, K.-H., and Gibbons, J. (2016).               *)
(*  Reasoning about probability and nondeterminism.                      *)
(*  In POPL workshop on Probabilistic Programming Semantics.             *)
(*  https://www.cs.ox.ac.uk/jeremy.gibbons/publications/prob-nondet.pdf  *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope monae_scope.
Local Open Scope proba_monad_scope.

#[short(type=altProbDrMonad)]
HB.structure Definition MonadAltProbDr {R : realType} :=
  { M of isMonadAltCI M & isMonadProbDr R M }.

Section choiceDalt.
Variables (R : realType).

(* technical equality from [Abou-Saleh] *)
Local Lemma altEbindarb (M : altMonad) (T : Type) (x y : M T) :
  x [~] y = arb >>= fun b => if b then x else y.
Proof. by rewrite alt_bindDl !bindretf. Qed.

Local Lemma choiceDif (M : convexMonad R) (T : Type) (b : bool) (p : {prob R}) (x y z w : M T) :
  (if b then x <| p |> y else z <| p |> w) =
  (if b then x else z) <| p |> (if b then y else w).
Proof. by case: b. Qed.

(* the right distr. of bind implies the distr. of nondeterminism over probability *)
Fact choiceDalt (M : altProbDrMonad R) (T : Type) (p : {prob R}) :
  right_distributive (fun x y : M T => x [~] y) (fun x y : M T => x <| p |> y).
Proof.
move=> x y z.
rewrite -[in LHS](choicemm p x) altEbindarb.
transitivity (arb >>= (fun b : bool => (if b then x else y) <|p|> if b then x else z)).
  by congr (@bind M bool T (@arb M) _); apply: funext => b; rewrite choiceDif.
by rewrite choice_bindDr -!altEbindarb.
Qed.

End choiceDalt.
