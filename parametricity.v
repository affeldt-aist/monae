Declare ML Module "paramcoq".

From mathcomp Require Import all_ssreflect.
Require Import monad mmt_sect5 monad_model.
Import Univ.

Unset Universe Checking.
Set Bullet Behavior "Strict Subproofs".

(** The identity functor *)
Module Identity.

Section Naturality.

Variable A : UU1.

Realizer A as A_R := (@eq A).

Definition M (X : UU1) : UU1 :=
ltac:(
  let t := constr:(ModelMonad.identity X) in
  let t := eval cbn in t in
  exact t).

Definition T : UU1 := k_type M A.

Parametricity T arity 2.

Variable m : T.

Axiom param : T_R m m.

Lemma naturality :
naturality (exponential_F A \O ModelMonad.identity) ModelMonad.identity m.
Proof.
intros X Y f.
rewrite boolp.funeqE => g.
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

(** The option functor *)
(* TODO: Replace with the exception monad *)
Module Option.

Section Naturality.

Variable A : UU1.

Realizer A as A_R := (@eq A).

Definition M (X : UU1) : UU1 := 
ltac:(
  let t := constr:(ModelMonad.option_monad X) in
  let t := eval cbn in t in
  exact t).

Definition T : UU1 := k_type M A.

Parametricity Recursive T arity 2.

Variable m : T.

Axiom param : T_R m m.

Program Lemma naturality :
naturality
  (exponential_F A \O ModelMonad.option_monad) ModelMonad.option_monad m.
Proof.
intros X Y f.
rewrite boolp.funeqE => g.
unfold comp at 1 2.
Abort. (* WIP *)
(*
assert (H :
  forall a a' : A, a = a' ->
  option_R X Y (fun (x : X) (y : Y) => f x = y) (g a)
    ((ModelMonad.option_monad # f \o g) a')).
{
  intros a a' Ha.
  subst a'.
  unfold comp.
  case (g a); cbn; [ | constructor].
  intro x.
  constructor.
  reflexivity.
}
assert (Hparam :=
  param X Y (fun x y => f x = y) g (ModelMonad.option_monad # f \o g) H).
destruct Hparam; cbn; congruence.
Qed.
*)

End Naturality.

End Option.

(** The list functor *)
Module List.

Section Naturality.

Variable A : UU1.

Realizer A as A_R := (@eq A).

Definition M (X : UU1) : UU1 :=
ltac:(
  let t := constr:(ModelMonad.ListMonad.functor X) in
  let t := eval cbn in t in
  exact t).

Definition T : UU1 := k_type M A.

Parametricity Recursive T arity 2.

Variable m : T.

Axiom param : T_R m m.

Lemma naturality :
naturality
  (exponential_F A \O ModelMonad.ListMonad.functor)
  ModelMonad.ListMonad.functor m.
Proof.
intros X Y f.
rewrite boolp.funeqE => g.
unfold comp at 1 2.
assert (H :
  forall a a' : A, a = a' ->
  list_R X Y (fun (x : X) (y : Y) => f x = y) (g a)
    ((ModelMonad.ListMonad.functor # f \o g) a')).
{
  intros a a' Ha.
  subst a'.
  unfold comp.
  case (g a); cbn; [constructor | ].
  intros x lx.
  constructor; [reflexivity | ].
  induction lx as [ | x' lx' IH]; [constructor | ].
  constructor; [reflexivity | exact IH].
}
assert (Hparam :=
  param X Y (fun x y => f x = y) g ((ModelMonad.ListMonad.functor # f) \o g) H).
induction Hparam as [ | x y Hf mx my IH Hmap].
- admit. (*reflexivity.*)
- cbn.
  admit. (*congruence.*)
Abort.

End Naturality.

End List.

(** The state functor *)
Module State.

Section Naturality.

Variable A S : Type.

Realizer A as A_R := (@eq A).
Realizer S as S_R := (@eq S).

Definition M X : Type :=
ltac:(
  let t := constr:(ModelMonad.State.functor S X) in
  let t := eval cbn in t in
  exact t).

Definition T : UU1 := k_type M A.

Parametricity Recursive T arity 2.

Variable m : T.

Axiom param : T_R m m.

Lemma naturality :
naturality
  (exponential_F A \O ModelMonad.State.functor S )
  (ModelMonad.State.functor S) m.
(*
Lemma naturality (X Y : Type) (f : X -> Y) :
ModelMonad.State.functor S # f \o m X =
m Y \o (fun g => ModelMonad.State.functor S # f \o g).
*)
Proof.
intros X Y f.
rewrite boolp.funeqE => g.
unfold comp at 1 2.
assert (H :
  forall a a' : A, a = a' ->
  M_R X Y (fun (x : X) (y : Y) => f x = y) (g a)
    ((ModelMonad.State.functor S # f \o g) a')).
{
  intros a a' Ha s s' Hs.
  unfold S_R in Hs.
  subst a' s'.
  unfold comp, Fun.
  cbn.
  unfold ModelMonad.State.map.
  case (g a s).
  intros x s'.
  constructor; reflexivity.
}
rewrite boolp.funeqE => s0.
assert (Hparam :=
  param X Y (fun x y => f x = y) g ((ModelMonad.State.functor S # f) \o g)
    H s0 s0 (erefl s0)).
simple inversion Hparam as [x y Hxy s s' Hs Hx Hy].
compute.
compute in Hy.
rewrite <- Hx, <- Hy.
unfold S_R in Hs.
subst y s'.
reflexivity.
Qed.

End Naturality.

End State.
