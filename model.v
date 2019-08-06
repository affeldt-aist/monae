Require Import ssreflect ssrmatching ssrfun ssrbool.
From mathcomp Require Import eqtype ssrnat seq choice.
From mathcomp Require boolp.

Section choice_cast.

Definition equality_mixin_of_Type (T : Type) : Equality.mixin_of T :=
  EqMixin (fun x y : T => boolp.asboolP (x = y)).

Definition choice_of_Type (T : Type) : choiceType :=
  Choice.Pack (Choice.Class (equality_mixin_of_Type T) boolp.gen_choiceMixin).

Definition choice_of_Object {T} (t : T) : choice_of_Type T := t.

End choice_cast.
