(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2020 monae authors, license: LGPL-2.1-or-later               *)
Declare ML Module "paramcoq".

From mathcomp Require Import all_ssreflect.
Require Import imonae_lib ihierarchy imonad_lib ifmt_lifting imonad_model.

(******************************************************************************)
(* Instantiations of uniform lifting (Theorem 27 of [Mauro Jaskelioff,        *)
(* Modular Monad Transformers, ESOP 2009]) with:                              *)
(* - the identity monad (Module Identity)                                     *)
(* - the exception monad (Module Exception)                                   *)
(* - the option monad (Module Option)                                         *)
(* - the list monad (Module List)                                             *)
(* - the state monad (Module State)                                           *)
(*                                                                            *)
(* WARNING: see ifmt_lifting.v                                                *)
(******************************************************************************)

Local Open Scope monae_scope.

Import Univ.
Set Bullet Behavior "Strict Subproofs".

(******************************************************************************)

Module Identity.

Section Naturality.

Variable A : UU0.

Realizer A as A_R := (@eq A).

Definition M (X : UU0) : UU0 :=
ltac:(
  let t := constr:(ModelMonad.identity X) in
  let t := eval cbn in t in
  exact t).

Definition T : UU0 := MK M A.

Parametricity T arity 2.

Variable m : T.

Axiom param : T_R m m.

Lemma naturality :
  naturality (exponential_F A \O ModelMonad.identity) ModelMonad.identity m.
Proof.
intros X Y f.
apply fun_ext => g.
unfold comp at 1 2.
apply
  (param X Y (fun x y => (ModelMonad.identity # f) x = y) g
    (ModelMonad.identity # f \o g)).
intros a1 a2 Ha.
rewrite Ha.
reflexivity.
Qed.

End Naturality.

End Identity.

Check uniform_sigma_lifting (M:=ModelMonad.identity) _ _ Identity.naturality.

(******************************************************************************)

Module Exception.

Section Naturality.

Variables E A : UU0.

Realizer E as E_R := (@eq E).
Realizer A as A_R := (@eq A).

Definition M (X : UU0) : UU0 :=
ltac:(
  let t := constr:(ModelMonad.Except.t E X) in
  let t := eval cbn in t in
  exact t).

Definition T : UU0 := MK M A.

Parametricity Recursive T arity 2.

Variable m : T.

Axiom param : T_R m m.

Program Lemma naturality :
naturality
  (exponential_F A \O ModelMonad.Except.t E) (ModelMonad.Except.t E) m.
Proof.
intros X Y f.
apply fun_ext => g.
unfold comp at 1 2.
assert (H :
  forall a a' : A, a = a' ->
  M_R X Y (fun (x : X) (y : Y) => f x = y) (g a)
    (((ModelMonad.Except.t E # f) \o g) a')).
{
  intros a a' Ha.
  subst a'.
  unfold comp.
  case (g a); cbn; intro; constructor; reflexivity.
}
assert (Hparam :=
  param X Y (fun x y => f x = y) g (ModelMonad.Except.t E # f \o g) H).
transitivity (m Y ((ModelMonad.Except.t E # f) \o g)); [ | reflexivity].
destruct Hparam; compute; congruence.
Qed.

End Naturality.

End Exception.

Check fun E =>
  uniform_sigma_lifting (M:=ModelMonad.Except.t E) _ _ (Exception.naturality E).

(******************************************************************************)

Module Option.

Section Naturality.

Variable A : UU0.

Definition M (X : UU0) : UU0 := ModelMonad.option_monad X.

Definition T : UU0 := MK M A.

Variable m : T.

Lemma naturality :
naturality
  (exponential_F A \O ModelMonad.option_monad) ModelMonad.option_monad m.
Proof.
apply Exception.naturality.
Qed.

End Naturality.

End Option.

Check uniform_sigma_lifting (M:=ModelMonad.option_monad) _ _ Option.naturality.

(******************************************************************************)

Module List.

Section Naturality.

Variable A : UU0.

Realizer A as A_R := (@eq A).

Definition M (X : UU0) : UU0 :=
ltac:(
  let t := constr:(ModelMonad.ListMonad.t X) in
  let t := eval cbn in t in
  exact t).

Definition T : UU0 := MK M A.

Parametricity Recursive T arity 2.

Variable m : T.

Axiom param : T_R m m.

Lemma naturality : naturality
  (exponential_F A \O ModelMonad.ListMonad.t) ModelMonad.ListMonad.t m.
Proof.
move=> X Y f /=; apply fun_ext => g.
rewrite [RHS](_ : _ = m Y ((ModelMonad.ListMonad.t # f) \o g)) //.
have : list_R X Y (fun x y => f x = y) (m X g) (m Y ((ModelMonad.ListMonad.t # f) \o g)).
  apply: param.
  by rewrite /A_R /comp => a _ <-; elim: (g a) => [|? ? ?]; constructor.
rewrite /comp; elim=> //= x y fxy mx my _.
by rewrite /Actm /= => <-; rewrite -fxy.
Qed.

End Naturality.

End List.

Check uniform_sigma_lifting (M:=ModelMonad.ListMonad.t) _ _ List.naturality.

(******************************************************************************)

Module State.

Section Naturality.

Variable S A : UU0.

Realizer S as S_R := (@eq S).
Realizer A as A_R := (@eq A).

Definition M X : UU0 :=
ltac:(
  let t := constr:(ModelMonad.State.t S X) in
  let t := eval cbn in t in
  exact t).

Definition T : UU0 := MK M A.

Parametricity Recursive T arity 2.

Variable m : T.

Axiom param : T_R m m.

Lemma naturality :
naturality
  (exponential_F A \O ModelMonad.State.t S)
  (ModelMonad.State.t S) m.
Proof.
intros X Y f.
apply fun_ext => g.
unfold comp at 1 2.
assert (H :
  forall a a' : A, a = a' ->
  M_R X Y (fun (x : X) (y : Y) => f x = y) (g a)
    ((ModelMonad.State.t S # f \o g) a')).
{
  move=> a ? <- s ?; rewrite /S_R => <-.
  unfold comp, Actm.
  cbn.
  unfold ModelMonad.State.map, ModelMonad.State.bind, Monad_of_ret_bind.Map.
  rewrite /uncurry /prod_curry /=.
  by case (g a s).
}
apply fun_ext => s0.
assert (Hparam :=
  param X Y (fun x y => f x = y) g ((ModelMonad.State.t S # f) \o g)
    H s0 s0 (erefl s0)).
simple inversion Hparam as [x y Hxy s s' Hs Hx Hy].
compute.
compute in Hy.
rewrite -Hx -Hy.
unfold S_R in Hs.
subst y s'.
reflexivity.
Qed.

End Naturality.

End State.

Check fun S =>
  uniform_sigma_lifting (M:=ModelMonad.State.t S) _ _ (State.naturality S).
