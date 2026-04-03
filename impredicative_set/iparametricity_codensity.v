(* monae: Monadic equational reasoning in Rocq                                *)
(* Copyright (C) 2025 monae authors, license: LGPL-2.1-or-later               *)
From mathcomp Require Import all_ssreflect.
From HB Require Import structures.
Require Import ipreamble ihierarchy imonad_lib ifmt_lifting imonad_model.
From elpi Require Import derive (*param2*).
Require Import param1 param2.
(*From elpi Require Import derive.std.*)
(*From elpi Require Import derive.legacy.*)
(*From elpi Require Import derive.experimental.*)

(**md**************************************************************************)
(* Instantiations of uniform lifting (Theorem 27 of [Mauro Jaskelioff,        *)
(* Modular Monad Transformers, ESOP 2009]) with:                              *)
(* - the identity monad (Module Identity)                                     *)
(* - the exception monad (Module Exception)                                   *)
(* - the option monad (Module Option)                                         *)
(* - the list monad (Module List)                                             *)
(* - the state monad (Module State)                                           *)
(*                                                                            *)
(* WARNING: see fmt_lifting.v                                                 *)
(******************************************************************************)

Local Open Scope monae_scope.

Set Bullet Behavior "Strict Subproofs".

Lemma Actm_exponenialFE (M : monad) (X Y : UU0) (f : X -> Y) :
  forall A eX, ((exponentialF A \o M) # f) eX = M # f \o eX.
Proof. by []. Qed.

(******************************************************************************)

Module Identity.
Section identity_naturality.
(*Variable A : UU0.*)
(*Let A : UU0 := nat.*)

(*Realizer A as A_R := (@eq A).*)
Elpi derive.param2 eq.

Let M := [the monad of idfun].

Definition Mi (X : UU0) : UU0 := ltac:(
  let t := constr:(M X) in
  let t := eval cbn in t in
  exact t).

Definition T (A : UU0) : UU0 := MK Mi A.

(*Parametricity T arity 2.*)

#[recursive]derive T.

Variable A : UU0.
Variable m : T A.

Axiom param : T_R A A (@eq A) m m.

Lemma naturality : naturality (exponentialF A \o M) M m.
Proof.
move=> X Y f; apply funext => eX.
by apply: (param X Y (fun x y => (M # f) x = y)) => a a' ->/=.
Qed.

End identity_naturality.
End Identity.

Check uniform_sigma_lifting (M := [the monad of idfun]) _ _ Identity.naturality.

(******************************************************************************)

Module Exception.
Section exception_naturality.
(*Variables Z A : UU0.

Realizer Z as Z_R := (@eq Z).
Realizer A as A_R := (@eq A).*)

(*
This typechecks:

Inductive
sum_R (A1 A2 : UU0) (A_R : A1 -> A2 -> UU0) (B1 B2 : UU0) (B_R : B1 -> B2 -> UU0)
  : A1 + B1 -> A2 + B2 -> UU0 :=
    inl_R : forall (_1 : A1) (_2 : A2), A_R _1 _2 -> sum_R (*A1 A2 A_R B1 B2 B_R*) (inl _1) (inl _2)
  | inr_R : forall (_1 : B1) (_2 : B2), B_R _1 _2 -> sum_R (*A1 A2 A_R B1 B2 B_R*) (inr _1) (inr _2).
*)

#[verbose] derive sum.
Print sum_R.
(*
coq-elpi creates sum_R at UU1, not UU0.
Inductive
sum_R (A1 A2 : UU1) (A_R : A1 -> A2 -> UU1) (B1 B2 : UU1) (B_R : B1 -> B2 -> UU1)
  : A1 + B1 -> A2 + B2 -> UU1 :=
    inl_R : forall (_1 : A1) (_2 : A2), A_R _1 _2 -> sum_R A1 A2 A_R B1 B2 B_R (inl _1) (inl _2)
  | inr_R : forall (_1 : B1) (_2 : B2), B_R _1 _2 -> sum_R A1 A2 A_R B1 B2 B_R (inr _1) (inr _2).
*)

#[verbose] derive ExceptMonad.acto.
Fail Elpi derive.param2 ExceptMonad.acto.

(*
sum_R at UU1 causes a universe inconsistency:

Error:
param2: constant does not have the right type: Unable to unify
 "forall E1 E2 : UU0,
  (E1 -> E2 -> UU0) ->
  forall A1 A2 : UU0, (A1 -> A2 -> UU0) -> E1 + A1 -> E2 + A2 -> UU1"
with
 "forall E1 E2 : UU0,
  (E1 -> E2 -> UU0) ->
  forall A1 A2 : UU0,
  (A1 -> A2 -> UU0) -> ExceptMonad.acto E1 A1 -> ExceptMonad.acto E2 A2 -> UU0"
(universe inconsistency: Cannot enforce sum_R.u0 <= Set).
*)

derive eq.

Definition M (Z : UU0) := ExceptMonad.acto Z.
(*Definition M (Z : UU0) : monad := ExceptMonad.acto Z.*)

derive M.

Definition Me (Z : UU0) (X : UU0) : UU0 := ltac:(
  let t := constr:(M Z X) in
  let t := eval cbn in t in
  exact t).

derive Me.

Definition T (Z A : UU0) : UU0 := MK (Me Z) A.

(*Parametricity Recursive T arity 2.*)

#[verbose] derive MK.
#[recursive] derive T.

Variables Z A : UU0.
Variable m : T Z A.

Axiom param : T_R _ _ (@eq Z) m m.

Lemma naturality : naturality (exponentialF A \o M) M m.
Proof.
move=> X Y f; apply funext => eX.
set rhs := RHS.
have : Me_R X Y (fun x y => f x = y) (m X eX) rhs.
  apply: param => a _ <-; rewrite Actm_exponenialFE compE.
  by case: (eX a) => [e|x]; constructor.
by rewrite compE; case=> [a _ <-|x _ <-].
Qed.

End exception_naturality.
End Exception.

Check fun Z => uniform_sigma_lifting
  (M := [the monad of ExceptMonad.acto Z]) _ _ (Exception.naturality Z).

(******************************************************************************)

Module Option.
Section option_naturality.
Variable A : UU0.

Let M := [the monad of option_monad].

Variable m : MK M A.

Lemma naturality : naturality (exponentialF A \o M) M m.
Proof. exact: Exception.naturality. Qed.

End option_naturality.
End Option.

Check uniform_sigma_lifting (M := [the monad of option_monad]) _ _ Option.naturality.

(******************************************************************************)

Module List.
Section list_naturality.
Variable A : UU0.

Realizer A as A_R := (@eq A).

Let M := [the monad of ListMonad.acto].

Definition Ml (X : UU0) : UU0 := ltac:(
  let t := constr:(M X) in
  let t := eval cbn in t in
  exact t).

Definition T : UU0 := MK Ml A.

Parametricity Recursive T arity 2.

Variable m : T.

Axiom param : T_R m m.

Lemma naturality : naturality (exponentialF A \o M) M m.
Proof.
move=> X Y f /=; apply funext => eX.
set rhs := RHS.
have : Ml_R X Y (fun x y => f x = y) (m X eX) rhs.
  apply: param => a _ <-; rewrite Actm_exponenialFE compE.
  by elim: (eX a) => [|? ? ?]; constructor.
by rewrite compE; elim => // x _ <- l _ _ <-.
Qed.

End list_naturality.
End List.

Check uniform_sigma_lifting (M := [the monad of ListMonad.acto]) _ _ List.naturality.

(******************************************************************************)

Module State.
Section state_naturality.
Variable S A : UU0.

Realizer S as S_R := (@eq S).
Realizer A as A_R := (@eq A).

Let M := [the monad of StateMonad.acto S].

Definition Ms X : UU0 := ltac:(
  let t := constr:(M X) in
  let t := eval cbn in t in
  exact t).

Definition T : UU0 := MK Ms A.

Parametricity Recursive T arity 2.

Variable m : T.

Axiom param : T_R m m.

Lemma Actm_ModelMonadStateE' (X Y : UU0) (f : X -> Y) (eX : (exponentialF A \o M) X) a (s : S):
  (M # f \o eX) a s = let (x, y) := eX a s in (f x, y).
Proof. by []. Qed.

Lemma Actm_ModelMonadStateE (X Y : UU0) (f : X -> Y) (eX : A -> S -> (X * S)) (s : S)
  (mX : (A -> Ms X) -> Ms X) :
  (M # f \o mX) eX s = (let (x, y) := mX eX s in (f x, y)).
Proof. by []. Qed.

Lemma naturality : naturality (exponentialF A \o M) M m.
Proof.
move=> X Y f; apply funext => eX.
set rhs := RHS.
have H : Ms_R X Y (fun x y => f x = y) (m X eX) rhs.
  apply param => // a _ <- s1 _ <-.
  rewrite Actm_exponenialFE Actm_ModelMonadStateE'.
  by case: (eX a) => x s2; exact: prod_R_pair_R.
apply funext => s.
have {}H : prod_R X Y (fun x y => f x = y) S S S_R (m X eX s) (rhs s) by exact: H.
inversion H as [x y fxy s1 s2 s12 xs1 ys2].
by rewrite Actm_ModelMonadStateE -xs1 fxy s12.
Qed.
End state_naturality.
End State.

Check fun S => uniform_sigma_lifting
  (M := [the monad of StateMonad.acto S]) _ _ (State.naturality S).
