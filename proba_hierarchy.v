(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2020 monae authors, license: LGPL-2.1-or-later               *)
Ltac typeof X := type of X.

Require Import ssrmatching Reals.
From mathcomp Require Import all_ssreflect.
From mathcomp Require boolp.
From infotheo Require Import Reals_ext.
Require Import monae_lib.
From HB Require Import structures.
Require Import hierarchy.

(******************************************************************************)
(*        A formalization of monadic effects over the category Set            *)
(*               (part 2/2, see hierarchy.v for part 1/2)                     *)
(*                                                                            *)
(* Probability monads:                                                        *)
(*         probaMonad == probabilistic choice and bind left-distributes over  *)
(*                       choice                                               *)
(*        probDrMonad == probaMonad + bind right-distributes over choice      *)
(*       altProbMonad == combined (probabilistic and nondeterministic) choice *)
(*    exceptProbMonad == exceptions + probabilistic choice                    *)
(*                                                                            *)
(* references:                                                                *)
(* - R. Affeldt, D. Nowak, Extending Equational Monadic Reasoning with Monad  *)
(* Transformers, https://arxiv.org/abs/2011.03463                             *)
(* - R. Affeldt, D. Nowak, T. Saikawa, A Hierarchy of Monadic Effects for     *)
(* Program Verification using Equational Reasoning, MPC 2019                  *)
(* - J. Gibbons, R. Hinze, Just do it: simple monadic equational reasoning,   *)
(* ICFP 2011                                                                  *)
(* - J. Gibbons, Unifying Theories of Programming with Monads, UTP 2012       *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope do_notation.
Declare Scope mprog.
Declare Scope monae_scope.
Delimit Scope monae_scope with monae.
Declare Scope proba_monad_scope.

Reserved Notation "mx <| p |> my" (format "mx  <| p |>  my", at level 49).

Local Open Scope reals_ext_scope.
HB.mixin Record isMonadProb (M : UU0 -> UU0) of Monad M := {
  choice : forall (p : prob) (T : UU0), M T -> M T -> M T ;
  (* identity axioms *)
  choice0 : forall (T : UU0) (a b : M T), choice 0%:pr _ a b = b ;
  choice1 : forall (T : UU0) (a b : M T), choice 1%:pr _ a b = a ;
  (* skewed commutativity *)
  choiceC : forall (T : UU0) p (a b : M T), choice p _ a b = choice (p.~ %:pr) _ b a ;
  choicemm : forall (T : UU0) p, idempotent (@choice p T) ;
  (* quasi associativity *)
  choiceA : forall (T : UU0) (p q r s : prob) (a b c : M T),
    (p = r * s :> R /\ s.~ = p.~ * q.~)%R ->
    (*NB: needed to preserve the notation in the resulting choiceA lemma, report? *)
    let bc := choice q _ b c in
    let ab := choice r _ a b in
    choice p _ a bc = choice s _ ab c;
  (* composition distributes leftwards over [probabilistic] choice *)
  prob_bindDl : forall p, BindLaws.left_distributive (@bind [the monad of M]) (choice p)
}.

HB.structure Definition MonadProb := {M of isMonadProb M & }.
Notation "a <| p |> b" := (choice p _ a b).
Notation probMonad := MonadProb.type.
Arguments choiceA {_} {_} _ _ _ _ {_} {_} {_}.
Arguments choiceC {_} {_} _ _ _.
Arguments choicemm {_} {_} _.

HB.mixin Record isMonadProbDr (M : UU0 -> UU0) of MonadProb M := {
  (* composition distributes rightwards over [probabilistic] choice *)
  (* WARNING: this should not be asserted as an axiom in conjunction with
     distributivity of <||> over [] *)
  prob_bindDr : forall p, BindLaws.right_distributive (@bind [the monad of M]) (choice p) (* NB: not used *)
}.

HB.structure Definition MonadProbDr := {M of isMonadProbDr M & }.
Notation probDrMonad := MonadProbDr.type.

HB.mixin Record isMonadAltProb (M : UU0 -> UU0) of MonadAltCI M & MonadProb M := {
  choiceDr : forall T p,
    right_distributive (@choice [the probMonad of M] p T) (fun a b => a [~] b)
}.
HB.structure Definition MonadAltProb :=
  { M of isMonadAltProb M & isFunctor M & isMonad M & isMonadAlt M &
         isMonadAltCI M & isMonadProb M }.
Notation altProbMonad := MonadAltProb.type.

Section altprob_lemmas.
Local Open Scope proba_monad_scope.
Variable (M : altProbMonad).
Lemma choiceDl A p :
  left_distributive (fun x y : M A => x <| p |> y) (fun x y => x [~] y).
Proof. by move=> x y z; rewrite !(choiceC p) choiceDr. Qed.
End altprob_lemmas.

HB.mixin Record isMonadExceptProb (M : UU0 -> UU0) of MonadExcept M & MonadProb M := {
  catchDl : forall (A : UU0) w,
    left_distributive (@catch [the exceptMonad of M] A) (fun x y => choice w A x y)
}.

HB.structure Definition MonadExceptProb :=
 { M of isMonadExceptProb M & isFunctor M & isMonad M & isMonadFail M &
        isMonadExcept M & isMonadProb M }.
Notation exceptProbMonad := MonadExceptProb.type.
