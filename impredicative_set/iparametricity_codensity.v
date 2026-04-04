(* monae: Monadic equational reasoning in Rocq                                *)
(* Copyright (C) 2025 monae authors, license: LGPL-2.1-or-later               *)
From mathcomp Require Import all_ssreflect.
From HB Require Import structures.
Require Import ipreamble ihierarchy imonad_lib ifmt_lifting imonad_model.
From elpi Require Import derive param2.

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
Elpi derive.param2 eq.

Let M : monad := idfun.

Definition Mi (X : UU0) : UU0 := ltac:(
  let t := constr:(M X) in
  let t := eval cbn in t in
  exact t).

Definition T (A : UU0) : UU0 := MK Mi A.

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

Check uniform_sigma_lifting (M := idfun) _ _ Identity.naturality.

(******************************************************************************)

Module Exception.
Section exception_naturality.

Let M (Z : UU0) : monad := ExceptMonad.acto Z.

Definition Me (Z : UU0) (X : UU0) : UU0 := ltac:(
  let t := constr:(M Z X) in
  let t := eval cbn in t in
  exact t).

Definition T (Z A : UU0) : UU0 := MK (Me Z) A.

(* In order to derive `param2` on `ExceptMonad.acto`,
   we cannot use `Datatypes.sum` in its definition.
   `Datatypes.sum` is defined with template universe polymorphism,
   which means, syntactically, its universe is set to `Type`,
   while our instance of `sum` (in `ExceptMonad.acto`) will reside in `Set`.
   `coq-elpi` supposedly analyzes the definition of `sum` via its syntax,
   and generates `sum_R` in `Type` (= `UU1`), resulting in a
   universe inconsistency when doing `Elpi derive.param2 ExceptMonad.acto`.
   We have redefined `sum` in `imonad_model.v` explicitly
   in `Set` to avoid this problem. *)

#[recursive] derive T.
(* This automatically does:
Elpi derive.param2 ExceptMonad.acto.
Elpi derive.param2 M.
Elpi derive.param2 Me.
Elpi derive.param2 MK.
and more. *)

Variables Z A : UU0.
Variable m : T Z A.

Axiom param : T_R Z Z (@eq Z) A A (@eq A) m m.

Lemma naturality : naturality (exponentialF A \o (M Z)) (M Z) m.
Proof.
move=> X Y f; apply funext => eX.
set rhs := RHS.
have : Me_R _ _ (@eq Z) X Y (fun x y => f x = y) (m X eX) rhs.
  apply: param => a _ <-; rewrite Actm_exponenialFE compE.
  by case: (eX a) => [e|x]; constructor.
by rewrite compE; case=> [a _ <-|x _ <-].
Qed.

End exception_naturality.
End Exception.

Check fun Z => uniform_sigma_lifting
  (M := ExceptMonad.acto Z) _ _ (Exception.naturality Z).

(******************************************************************************)

Module Option.
Section option_naturality.
Variable A : UU0.

Let M : monad := option_monad.

Variable m : MK M A.

Lemma naturality : naturality (exponentialF A \o M) M m.
Proof. exact: Exception.naturality. Qed.

End option_naturality.
End Option.

Check uniform_sigma_lifting (M := option_monad) _ _ Option.naturality.

(******************************************************************************)

Module List.
Import IListMonad.
Section list_naturality.

Let M : monad := IListMonad.acto.

Definition Ml (X : UU0) : UU0 := ltac:(
  let t := constr:(M X) in
  let t := eval cbn in t in
  exact t).

Definition T (A : UU0) : UU0 := MK Ml A.

#[recursive] derive T.

Variable A : UU0.
Variable m : T A.
Axiom param : T_R A A (@eq A) m m.

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

Check uniform_sigma_lifting (M := IListMonad.acto) _ _ List.naturality.

End List.

(******************************************************************************)

Module State.
Import IStateMonad.
Section state_naturality.

Let M (S : UU0) : monad := IStateMonad.acto S.

Definition Ms (S X : UU0) := ltac:(
  let t := constr:(M S X) in
  let t := eval cbn in t in
  exact t).

Definition T (S A : UU0) : UU0 := MK (Ms S) A.

#[recursive] derive T.

Variable S A : UU0.
Variable m : T S A.

Axiom param : T_R S S (@eq S) A A (@eq A) m m.

Lemma Actm_ModelMonadStateE' (X Y : UU0) (f : X -> Y) (eX : (exponentialF A \o M S) X) a (s : S):
  (M S # f \o eX) a s = let (x, y) := eX a s in (f x, y).
Proof. by []. Qed.

Lemma Actm_ModelMonadStateE (X Y : UU0) (f : X -> Y) (eX : A -> S -> (X * S)) (s : S)
  (mX : (A -> Ms S X) -> Ms S X) :
  (M S # f \o mX) eX s = (let (x, y) := mX eX s in (f x, y)).
Proof. by []. Qed.

Lemma naturality : naturality (exponentialF A \o M S) (M S) m.
Proof.
move=> X Y f; apply funext => eX.
set rhs := RHS.
have H : Ms_R _ _ (@eq S) X Y (fun x y => f x = y) (m X eX) rhs.
  apply: param => // a _ <- s1 _ <-.
  rewrite Actm_exponenialFE Actm_ModelMonadStateE'.
  by case: (eX a) => x s2; exact: pair_R.
apply funext => s.
have {}H : prod_R X Y (fun x y => f x = y) S S (@eq S) (m X eX s) (rhs s) by exact: H.
inversion H as [x y fxy s1 s2 s12 xs1 ys2].
by rewrite Actm_ModelMonadStateE -xs1 fxy s12.
Qed.
End state_naturality.

Check fun S => uniform_sigma_lifting
  (M := IStateMonad.acto S) _ _ (State.naturality S).

End State.
