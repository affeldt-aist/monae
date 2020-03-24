Declare ML Module "paramcoq".

Require FunctionalExtensionality.
From mathcomp Require Import all_ssreflect. (* Just for \o *)
Require Import monad mmt_sect5 monad_model.
Import Univ.

Unset Universe Checking.

(** The identity functor *)
Module Identity.

Section Naturality.

Variable A : UU1.

Realizer A as A_R := (@eq A).

(* Definitions of [M] and [map] below could be replaced by
   declaring [M] as a functor. The same applies for the
   other pairs of [M] and [map] further below. *)

Definition M (X : UU1) : UU1 := X. (* TODO: use FId *)

Definition map {X Y : UU1} (f : X -> Y) (m : M X) : M Y :=
f m.

Definition T : UU1 := k_type M A.

Parametricity T arity 2.

Variable m : T.

Axiom param : T_R m m.

Lemma naturality (X Y : Type) (f : X -> Y) :
map f \o m X = m Y \o (fun g => map f \o g).
Proof.
apply FunctionalExtensionality.functional_extensionality_dep => g.
unfold comp at 1 2.
apply (param X Y (fun x y => map f x = y) g (map f \o g)).
intros a1 a2 Ha.
rewrite Ha.
reflexivity.
Qed.

End Naturality.

End Identity.

(** The option functor *)
Module Option.

Section Naturality.

Variable A : UU1.

Realizer A as A_R := (@eq A).

Definition M (X : UU1) : UU1 := option X. (* TODO: ModelMonad.option_monad *)

Definition map {X Y : UU1} (f : X -> Y) (m : M X) : M Y :=
option_map f m.

Definition T : UU1 := k_type M A.

Parametricity Recursive T arity 2.

Variable m : T.

Axiom param : T_R m m.

Lemma naturality (X Y : Type) (f : X -> Y) :
map f \o m X = m Y \o (fun g => map f \o g).
Proof.
apply FunctionalExtensionality.functional_extensionality_dep => g.
unfold comp at 1 2.
assert (H :
  forall a a' : A, a = a' ->
  option_R X Y (fun (x : X) (y : Y) => f x = y) (g a) ((map f \o g) a')).
{
  intros a a' Ha.
  subst a'.
  unfold comp.
  case (g a); cbn; [ | constructor].
  intro x.
  constructor.
  reflexivity.
}
assert (Hparam := param X Y (fun x y => f x = y) g (map f \o g) H).
destruct Hparam; cbn; congruence.
Qed.

End Naturality.

End Option.

(** The list functor *)
Module List.

Section Naturality.

Variable A : UU1.

Realizer A as A_R := (@eq A).

Definition M (X : UU1) : UU1 := list X. (* TODO: ModelMonad.ListMonad.t *)

Definition map {X Y : UU1} (f : X -> Y) (m : M X) : M Y :=
List.map f m.

Definition T : UU1 := k_type M A.

Parametricity Recursive T arity 2.

Variable m : T.

Axiom param : T_R m m.

Lemma naturality (X Y : Type) (f : X -> Y) :
map f \o m X = m Y \o (fun g => map f \o g).
Proof.
apply FunctionalExtensionality.functional_extensionality_dep => g.
unfold comp at 1 2.
assert (H :
  forall a a' : A, a = a' ->
  list_R X Y (fun (x : X) (y : Y) => f x = y) (g a) ((map f \o g) a')).
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
assert (Hparam := param X Y (fun x y => f x = y) g (comp (map f) g) H).
induction Hparam as [ | x y Hf mx my IH Hmap].
- reflexivity.
- cbn.
  unfold map in *.
  congruence.
Qed.

End Naturality.

End List.

(** The state functor *)
Module State.

Section Naturality.

Variable A S : Type.

Realizer A as A_R := (@eq A).
Realizer S as S_R := (@eq S).

Definition M X : Type := S -> X * S. (* TODO: ModelState.state *)

Definition map {X Y : Type} (f : X -> Y) (m : M X) : M Y :=
fun s => let (x, s') := m s in (f x, s').

Definition T : UU1 := k_type M A.

Parametricity Recursive T arity 2.

Variable m : T.

Axiom param : T_R m m.

Lemma naturality (X Y : Type) (f : X -> Y) :
map f \o m X = m Y \o (fun g => map f \o g).
Proof.
apply FunctionalExtensionality.functional_extensionality_dep => g.
unfold comp at 1 2.
assert (H :
  forall a a' : A, a = a' ->
  M_R X Y (fun (x : X) (y : Y) => f x = y) (g a) ((map f \o g) a')).
{
  intros a a' Ha s s' Hs.
  unfold S_R in Hs.
  subst a' s'.
  unfold comp, map.
  case (g a s).
  intros x s'.
  constructor; reflexivity.
}
apply FunctionalExtensionality.functional_extensionality_dep => s0.
assert (Hparam :=
  param X Y (fun x y => f x = y) g (comp (map f) g) H s0 s0 (erefl s0)).
simple inversion Hparam as [x y Hxy s s' Hs Hx Hy].
unfold map at 1.
rewrite <- Hx, <- Hy.
unfold S_R in Hs.
subst y s'.
reflexivity.
Qed.

End Naturality.

End State.

(** Attempt at a generic proof *)
Module Generic.

Section Naturality.

Variable A : UU1.

Realizer A as A_R := (@eq A).

Variable M : UU1 -> UU1.

Variable map : forall {X Y : UU1}, (X -> Y) -> M X -> M Y.

Variable R : forall X Y : Type, (X -> Y -> Type) -> M X -> M Y -> Type.

Realizer M as M_R := R.

(* What would the minimal properties to be satisfied by [R] such that
   the admitted subgoals below become provable? *)

Definition T : UU1 := k_type M A.

Parametricity T arity 2.

Variable m : T.

Axiom param : T_R m m.

Lemma naturality (X Y : Type) (f : X -> Y) :
map f \o m X = m Y \o (fun g => map f \o g).
Proof.
apply FunctionalExtensionality.functional_extensionality_dep => g.
unfold comp at 1 2.
assert (H :
  forall a a' : A, a = a' ->
  M_R X Y (fun (x : X) (y : Y) => f x = y) (g a) ((map f \o g) a')).
{
  intros a a' Ha.
  subst a'.
  unfold M_R, comp.
  admit.
}
assert (Hparam := param X Y (fun x y => f x = y) g (comp (map f) g) H).
unfold M_R, comp in *.
admit.
Abort.

End Naturality.

End Generic.
