(*
  Sample instantiation of the state-trace monad
*)

Require Import ssreflect ssrfun FunctionalExtensionality Eqdep List.
Import ListNotations.
From mathcomp Require Import seq.
Require Import monad state_monad trace_monad.

Module ModelMonad.

Section trace.
Variables S T : Type.
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

(*Module ModelTrace.

Section trace.
Variables S T : Type.
Definition M := @MonadTrace.Mixin _ (ModelMonad.m S T)
  (fun log s => (tt, (s.1, s.2 ++ [log]))).
End trace.

End ModelTrace.*)

Module ModelStateTrace.

Section trace.
Local Obligation Tactic := idtac.
Variables S T : Type.
Program Definition M :=
  @MonadStateTrace.Pack _ _ _ (@MonadStateTrace.Class _ _ _ (Monad.class (ModelMonad.M S T))
  (@MonadStateTrace.Mixin _ _ _
  (fun s => (s.1, s)) (* get *)
  (fun s' s => (tt, (s', s.2))) (* put *)
  (fun (log : T) s => (tt, (s.1, s.2 ++ [log]))) (* mark *))).
End trace.

End ModelStateTrace.

Module ModelStateTraceRun.

Section trace.
Local Obligation Tactic := by [].
Variables S T : Type.
Program Definition M := @MonadStateTraceRun.Pack _ _ _ (@MonadStateTraceRun.Class _ _
  _ (MonadStateTrace.class (ModelStateTrace.M S T)) (@MonadStateTraceRun.Mixin _ _ _
(fun A m (s : S * list T) => m s) (* run *)
_ _ _ _ _
)).
End trace.

End ModelStateTraceRun.
