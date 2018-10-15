Require Import ssreflect ssrmatching ssrfun ssrbool.
From mathcomp Require Import eqtype ssrnat seq choice fintype tuple.

From infotheo Require Import proba ssr_ext.

Require Import monad proba_monad monad_model.

(*
  This file provides a model for the probability monad.
  It depends on the formalization of distributions from the infotheo library
  (https://github.com/affeldt-aist/infotheo).

  Contents:
  - Module finLaws.
      the algebraic laws from monad.v for monads with a finite type
  - Module finMonad.
      monad with a finite type
  - Module Module finMonadProb.

*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module finLaws.
Section finlaws.
Variable M : finType -> Type.

Variable b : forall A B, M A -> (A -> M B) -> M B.

Local Notation "m >>= f" := (b m f).

Definition associative := forall A B C (m : M A) (f : A -> M B) (g : B -> M C),
  (m >>= f) >>= g = m >>= (fun x => (f x >>= g)).

Definition bind_right_distributive (add : forall B, M B -> M B -> M B) := forall A B,
  forall (m : M A) (k1 k2 : A -> M B),
    m >>= (fun x => add _ (k1 x) (k2 x)) = add _ (m >>= k1) (m >>= k2).

Definition bind_left_distributive (add : forall B, M B -> M B -> M B) := forall A B,
  forall (m1 m2 : M A) (k : A -> M B),
    (add _ m1 m2) >>= k = add _ (m1 >>= k) (m2 >>= k).

Definition right_zero (f : forall A, M A) :=
  forall A B (g : M B), g >>= (fun _ => f A) = f A.

Definition left_zero (f : forall A, M A) := forall A B g, f A >>= g = f B.

Definition left_neutral (r : forall A : finType, A -> M A) := forall (A B : finType) (x : A) (f : A -> M B),
  r _ x >>= f = f x.

Definition right_neutral (r : forall A : finType, A -> M A) := forall A (m : M A),
  m >>= r _ = m.

Definition left_id (r : forall A, M A) (add : forall B, M B -> M B -> M B) := forall A (m : M A),
  add _ (r _) m = m.

Definition right_id (r : forall A, M A) (add : forall B, M B -> M B -> M B) := forall A (m : M A),
  add _ m (r _) = m.

End finlaws.
End finLaws.

Module finMonad.
Record class_of (m : finType -> Type) : Type := Class {
  ret : forall A : finType, A -> m A;
  bind : forall A B : finType, m A -> (A -> m B) -> m B ;
  _ : finLaws.left_neutral bind ret ;
  _ : finLaws.right_neutral bind ret ;
  _ : finLaws.associative bind }.
Record t : Type := Pack { m : finType -> Type; class : class_of m }.
Module Exports.
Definition Bind (M : t) A B : m M A -> (A -> m M B) -> m M B :=
  let: Pack _ (Class _ x _ _ _) := M in x A B.
Arguments Bind {M A B} : simpl never.
Definition Ret (M : t) (A : finType) : A -> m M A :=
  let: Pack _ (Class x _ _ _ _) := M in x A.
Arguments Ret {M A} : simpl never.
Notation "m >>= f" := (Bind m f).
Notation finmonad := t.
Coercion m : finmonad >-> Funclass.
End Exports.
End finMonad.
Export finMonad.Exports.

Require Import Reals.

Module finMonadProb.
Record mixin_of (m : finMonad.t) : Type := Mixin {
  choice : forall (p : Prob.t) (A : finType), m A -> m A -> m A
           where "mx <| p |> my" := (choice p mx my) ;
  (* identity laws *)
  _ : forall (A : finType) (mx my : m A), mx <| [Pr of 0] |> my = my ;
  _ : forall (A : finType) (mx my : m A), mx <| [Pr of 1] |> my = mx ;
  (* skewed commutativity law *)
  _ : forall (A : finType) p (mx my : m A), mx <| p |> my = my <| [Pr of p.~] |> mx ;
  _ : forall A p, idempotent (@choice p A) ;
  (* quasi associativity *)
  _ : forall (A : finType) (p q r s : Prob.t) (mx my mz : m A),
    (p = r * s :> R /\ s.~ = p.~ * q.~)%R ->
    mx <| p |> (my <| q |> mz) = (mx <| r |> my) <| s |> mz ;
  (* composition distributes leftwards over [probabilistic] choice *)
  _ : forall p, finLaws.bind_left_distributive (@Bind m) (choice p) ;
} .
Record class_of (m : finType -> Type) := Class {
  base : finMonad.class_of m ; mixin : mixin_of (finMonad.Pack base) }.
Structure t := Pack { m : finType -> Type ; class : class_of m }.
End finMonadProb.

Module finMonadProbModel.
Local Obligation Tactic := idtac.

Program Definition monad : finMonad.t := @finMonad.Pack proba.dist
  (@finMonad.Class _ Dist1.d DistBind.d _ _ _ ).
Next Obligation. move=> ? ? ? ?; exact: DistBind1f. Qed.
Next Obligation. move=> ? ?; exact: DistBindp1. Qed.
Next Obligation. move=> ? ? ? ? ?; exact: DistBindA. Qed.

Program Definition prob_mixin : finMonadProb.mixin_of monad :=
  @finMonadProb.Mixin monad (fun p (A : finType) (m1 m2 : proba.dist A) =>
    (@ConvexDist.d A m1 m2 _ (Prob.O1 p))) _ _ _ _ _ _.
Next Obligation. move=> ? ? ?; exact: ConvexDist.d0. Qed.
Next Obligation. move=> ? ? ?; exact: ConvexDist.d1. Qed.
Next Obligation. move=> ? ? ? ?; exact: ConvexDist.quasi_commute. Qed.
Next Obligation. move=> ? ? ?; exact: ConvexDist.idempotent. Qed.
Next Obligation. move=> ? ? ? ? ? ? ? ? [? ?] /=; exact: ConvexDist.quasi_assoc. Qed.
Next Obligation. move=> ? ? ? ? ? ?; exact: ConvexDist.bind_left_distr. Qed.

Definition prob_class : finMonadProb.class_of proba.dist :=
  @finMonadProb.Class _ _ prob_mixin.

Definition prob : finMonadProb.t := finMonadProb.Pack prob_class.

End finMonadProbModel.
