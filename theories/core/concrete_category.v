(* monae: Monadic equational reasoning in Rocq                                *)
(* Copyright (C) 2025 monae authors, license: LGPL-2.1-or-later               *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import boolp.
Require Import preamble category.

(**md**************************************************************************)
(* # Formalization of basic concrete category theory                          *)
(*                                                                            *)
(* This file provides definitions of concrete category and related basic      *)
(* constructions.                                                             *)
(*                                                                            *)
(* ```                                                                        *)
(*        concrete_category == type of concrete categories; A concrete        *)
(*                             category C comes with a universe a la Tarski:  *)
(*                             there is a realizer function el that           *)
(*                             associates to each object A the type el A      *)
(*                             of its elements                                *)
(*                  [fn f]  == function corresponding to the morphism f       *)
(*            BindLaws_conc == module that define the element-wise monad laws *)
(*   Monad_of_ret_bind_conc == factory, monad defined by element-wise ret     *)
(*                             and bind operators                             *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope category_scope.

HB.mixin Record isConcreteCategory (obj : Type) of @Category obj := {
  el : obj -> Type ;
  fn : forall {a b : obj}, {hom a -> b} -> el a -> el b ;
  fn_inj : forall a b, injective (@fn a b) ;
  fn_id : forall a : obj , fn (id a) = idfun;
  fn_comp : forall (a b c : obj) (f : {hom a -> b}) (g : {hom b -> c}),
      fn (comp f g) = fn g \o fn f ;
}.
Arguments isConcreteCategory.phant_Build : clear implicits.
#[short(type=concrete_category)]
HB.structure Definition ConcreteCategory := {C of isConcreteCategory C & }.
Arguments fn [C a b] : rename.
Arguments fn_id [C] : rename.
Arguments fn_comp [C] : rename.

Section hom_interface.
Lemma hom_ext (C : concrete_category) (a b : C) (f g : {hom a -> b}) :
  f = g <-> fn f =1 fn g.
Proof. by split; [move-> | by move/funext/fn_inj]. Qed.
End hom_interface.

Section Type_as_a_concrete_category.
(* TODO: consider using universe polymorphism *)
Let UUx := Type@{UU_category}.

HB.instance Definition _ := Category.on UUx.
HB.instance Definition _ :=
  isConcreteCategory.Build
    UUx (fun x => x) (fun _ _ f => f) (fun a b => @inj_id (a -> b))
    (fun _ => erefl) (fun _ _ _ _ _ => erefl).

End Type_as_a_concrete_category.

Module BindLaws_conc.
Section conccat.
Variables (C : concrete_category) (M : C -> C).
Variable bind : forall a b, {hom a -> M b} -> {hom M a -> M b}.
Variable ret : forall a, {hom a -> M a}.
Local Notation "m >>= f" := (fn (bind f) m).

Definition associative :=
  forall a b c (m : el (M a)) (f : {hom a -> M b}) (g : {hom b -> M c}),
  (m >>= f) >>= g = m >>= (bind g \c f).
Definition left_neutral :=
  forall a b (f : {hom a -> M b}), (bind f \c ret a) = f.
Definition right_neutral :=
  forall a (m : el (M a)), m >>= ret a = m.
End conccat.
End BindLaws_conc.

HB.factory Record Monad_of_ret_bind_conc (C : concrete_category) (M : C -> C) :=
{
  ret : forall a, {hom a -> M a} ;
  bind : forall (a b : C), {hom a -> M b} -> {hom M a -> M b} ;
  bindretf : BindLaws_conc.left_neutral bind ret ;
  bindmret : BindLaws_conc.right_neutral bind ret ;
  bindA : BindLaws_conc.associative bind ;
}.
HB.builders Context C M of Monad_of_ret_bind_conc C M.
Let bindret : BindLaws.right_neutral bind ret.
Proof. by move=> a; apply/hom_ext => m; rewrite bindmret fn_id. Qed.
Let bindA' : BindLaws.associative bind.
Proof.
by move=> a b c f g; apply/hom_ext => m; rewrite fn_comp -bindA.
Qed.
HB.instance Definition _ :=  Monad_of_ret_bind.Build C M bindretf bindret bindA'.
HB.end.
