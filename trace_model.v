(*
  Sample instantiation of the state-trace monad
*)

Require Import ssreflect ssrfun FunctionalExtensionality Eqdep List.
Import ListNotations.
Require Import monad state_monad trace_monad.

Module StateTraceModel.
Section statetracemodel.

Variables T S : Type.

Let m : Type -> Type := fun A => S * list T -> A * (S * list T).

Program Definition MONAD : monad := Monad.Pack (@Monad.Class
  m
  (fun A a => fun s => (a, s)) (* ret *)
  (fun A B m f => fun s => let (a, s') := m s in f a s') (* bind *)
  _ _ _).
Next Obligation. by []. Qed.
Next Obligation.
compute.
intros.
extensionality s.
destruct (m0 s); reflexivity.
Qed.
Next Obligation.
compute.
intros.
extensionality s.
destruct (m0 s); reflexivity.
Qed.

Program Definition TRACE := @MonadTrace.Mixin T MONAD
  (fun log s => (tt, (s.1, s.2 ++ [log]))).

Program Definition STATE := @MonadState.Class
  S m (Monad.class MONAD) (@MonadState.Mixin S MONAD
  (* get *) (fun s => (s.1, s))
  (* put *) (fun s' s => (tt, (s', s.2)))
  _ _ _ _).
Next Obligation. by []. Qed.
Next Obligation. by []. Qed.
Next Obligation.
compute.
extensionality s.
destruct s; reflexivity.
Qed.
Next Obligation. by []. Qed.

Program Definition STATETRACE : stateTraceMonad T S :=
  @MonadStateTrace.Pack T S m
  (@MonadStateTrace.Class T S m
  STATE
  TRACE
  (@MonadStateTrace.Mixin T S (MonadState.Pack STATE)
     _ (* mark *)
     (fun A (m : MONAD A) (s : S * list T) => m s) (* run *)
     _ _ _ _ _)).
Next Obligation. by []. Qed.
Next Obligation. by []. Qed.
Next Obligation. by []. Qed.
Next Obligation. by []. Qed.
Next Obligation. by []. Qed.

End statetracemodel.
End StateTraceModel.
