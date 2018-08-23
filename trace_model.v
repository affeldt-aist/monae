(*
  Sample instantiation of the state-trace monad
*)

Require Import ssreflect ssrfun FunctionalExtensionality Eqdep List.
Import ListNotations.
Require Import monad state_monad trace_monad.

Module ModelMonad.

Section trace.
Variables T S : Type.
Definition m : Type -> Type := fun A => S * list T -> A * (S * list T).
Program Definition M := Monad.Pack (@Monad.Class
  m
  (fun A a => fun s => (a, s)) (* ret *)
  (fun A B m f => fun s => let (a, s') := m s in f a s') (* bind *)
  _ _ _).
Next Obligation. by []. Qed.
Next Obligation. move=> A ma; extensionality s; by case: ma. Qed.
Next Obligation. move=> A B C ma f g; extensionality s; by case: ma. Qed.
End trace.

End ModelMonad.

Module ModelTrace.

Section trace.
Variables T S : Type.
Definition M := @MonadTrace.Mixin _ (ModelMonad.m T S)
  (fun log s => (tt, (s.1, s.2 ++ [log]))).
End trace.

End ModelTrace.

Module ModelState.

Section trace.
Variables T S : Type.
Program Definition M := @MonadState.Class
  _ _ _ (@MonadState.Mixin _ (ModelMonad.M T S)
  (fun s => (s.1, s)) (* get *)
  (fun s' s => (tt, (s', s.2))) (* put *)
  _ _ _ _).
Next Obligation. apply functional_extensionality; by case. Qed.
End trace.

End ModelState.

Module ModelStateTrace.

Section trace.
Local Obligation Tactic := by [].
Variables T S : Type.
Program Definition M :=
  @MonadStateTrace.Pack _ _ _
  (@MonadStateTrace.Class _ _ _ _
  (ModelTrace.M T S)
  (@MonadStateTrace.Mixin _ _ (MonadState.Pack (ModelState.M T S))
     _ (* mark *)
     (fun A m (s : S * list T) => m s) (* run *)
     _ _ _ _ _)).

End trace.

End ModelStateTrace.
