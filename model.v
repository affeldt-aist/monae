Require Import ssreflect ssrmatching ssrfun ssrbool.
From mathcomp Require Import eqtype ssrnat seq choice.
From mathcomp Require Import boolp.

Section choice_cast.

Definition equality_mixin_of_Type (T : Type) : Equality.mixin_of T :=
  EqMixin (fun x y : T => asboolP (x = y)).

Definition choice_of_Type (T : Type) : choiceType :=
  Choice.Pack (Choice.Class (equality_mixin_of_Type T) gen_choiceMixin).

End choice_cast.
