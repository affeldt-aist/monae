(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2020 monae authors, license: LGPL-2.1-or-later               *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import boolp.
Require Import preamble category hierarchy.

(**md**************************************************************************)
(* # Converter from category.monad to hierarchy.monad                         *)
(*                                                                            *)
(* ```                                                                        *)
(* Monad_of_category_monad == module, interface to isMonad from hierarchy.v   *)
(* Monad_of_category_monad.m == turns a monad over the Type category into     *)
(*                        a monad in the sense of isMonad from hierarchy.v    *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope category_scope.

Local Notation CT := (Type : category).

Module Monad_of_category_monad.
Section def.
Variable M : category.Monad.Exports.monad CT.

Definition Fhom (A B : Type) (h : A -> B) (x : M A) : M B :=
  (M # [the {hom [CT] A -> B} of h]) x.

Lemma Fhom_id A : Fhom (fun x => x) = @id (M A).
Proof. by rewrite /Fhom category.Fhom_id. Qed.

Lemma Fhom_comp A B C (g : B -> C) (h : A -> B) :
  Fhom (g \o h) = Fhom g \o Fhom h.
Proof. by rewrite {1}/Fhom category.Fhom_comp. Qed.

HB.instance Definition _ := @hierarchy.isFunctor.Build _ Fhom Fhom_id Fhom_comp.

Local Notation F := (M : functor).

Definition ret_ : forall A, ((idfun : functor) A : Type) -> F A :=
  fun A (a : A) => @category.ret _ M A a.

Definition join_ : forall A, (F \o F : functor) A -> F A :=
  fun A => @category.join _ M A.

Lemma naturality_ret : hierarchy.naturality _ _ ret_.
Proof. exact: (category.natural (@category.ret _ M)). Qed.

HB.instance Definition _ := hierarchy.isNatural.Build _ _ ret_ naturality_ret.

Definition ret : ((idfun : functor) ~> F)%monae := (ret_ : nattrans _ _).

Lemma naturality_join : hierarchy.naturality (F \o F : functor) F join_.
Proof. exact: (category.natural (@category.join _ M)). Qed.

HB.instance Definition _ := hierarchy.isNatural.Build _ _ join_ naturality_join.

Definition join := (join_ : nattrans _ _).

Lemma retE a : ret a = category.ret a. Proof. by []. Qed.

Lemma joinE a : join a = category.join a. Proof. by []. Qed.

Lemma joinretM : hierarchy.JoinLaws.left_unit ret join.
Proof. exact: (@category.joinretM _ M). Qed.

Lemma joinMret : hierarchy.JoinLaws.right_unit ret join.
Proof. exact: (@category.joinMret _ M). Qed.

Lemma joinA : hierarchy.JoinLaws.associativity join.
Proof. exact: (@category.joinA _ M). Qed.

HB.instance Definition _ := @hierarchy.isMonad_ret_join.Build M ret join
  joinretM joinMret joinA.
End def.
End Monad_of_category_monad.
HB.export Monad_of_category_monad.
