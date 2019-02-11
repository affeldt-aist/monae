Require Import FunctionalExtensionality Coq.Program.Tactics ProofIrrelevance.
Require Classical.
Require Import ssreflect ssrmatching ssrfun ssrbool.
From mathcomp Require Import eqtype ssrnat seq path div choice fintype tuple.
From mathcomp Require Import finfun bigop.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Category.
Record class_of (T : Type) : Type := Class {
  ob : T -> Type ; (* T and ob forms a ``universe a la Tarski'' *)
  hom : forall A B, (ob A -> ob B) -> Prop ; (* subset of morphisms *)
  _  : injective ob ; (* ob is injective *)
  _ : forall (A : T), hom (A:=A) (B:=A) id ; (* id is in hom *)
  _  : forall (A B C : T) (f : ob A -> ob B) (g : ob B -> ob C),
      hom f -> hom g -> hom (g \o f) ; (* hom is closed under composition *)
}.
Structure t : Type := Pack { T : Type ; class : class_of T }.
Module Exports.
(*
Definition Ob (C : t) : T -> Type :=
  let: Pack _ (Class ob _ _ _ _) := C in ob.
*)
End Exports.
End Category.

