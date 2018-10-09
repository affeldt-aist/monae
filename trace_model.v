(*
  Sample instantiation of the state-trace monad
*)

Require Import ssreflect ssrfun FunctionalExtensionality Eqdep List.
Import ListNotations.
From mathcomp Require Import seq.
Require Import monad state_monad trace_monad.

Module ModelMonad.
Section modelmonad.
Variables S T : Type.
Definition m : Type -> Type := fun A => S * list T -> A * (S * list T).
Definition mk : monad.
refine (@Monad.Pack _ (@Monad.Class m
  (fun A a => fun s => (a, s)) (* ret *)
  (fun A B m f => fun s => let (a, s') := m s in f a s') (* bind *) _ _ _)).
by [].
move=> A f; apply functional_extensionality => ?; by case: f.
move=> A B C a b c; apply functional_extensionality => ?; by case: a.
Defined.
End modelmonad.
End ModelMonad.

(*Module ModelTrace.

Section trace.
Variables S T : Type.
Definition M := @MonadTrace.Mixin _ (ModelMonad.m S T)
  (fun log s => (tt, (s.1, s.2 ++ [log]))).
End trace.

End ModelTrace.*)

Module ModelStateTraceMonad.
Definition mk {S T} : stateTraceMonad S T.
refine (
let m := Monad.class (@ModelMonad.mk S T) in
let stm := (@MonadStateTrace.Class S T _ m
  (@MonadStateTrace.Mixin _ _ (Monad.Pack m)
  (fun s => (s.1, s))  (* get *)
  (fun s' s => (tt, (s', s.2)))
  (fun (t : T) s => (tt, (s.1, s.2 ++ t :: nil))))) in
@MonadStateTrace.Pack S T (fun A => S * list T -> A * (S * list T)) stm).
Defined.
End ModelStateTraceMonad.

Module ModelRunMonad.
Definition mk {S T} : runMonad (S * seq T).
refine (@MonadRun.Pack _ _ (@MonadRun.Class _ _ (Monad.class (@ModelMonad.mk S T))
  (@MonadRun.Mixin _ (@ModelMonad.mk S T)
  (fun A m (s : S * list T) => m s) (* run *) _ _))).
by [].
by [].
Defined.
End ModelRunMonad.

Module ModelStateTraceRunMonad.
Definition mk {S T} :
  stateTraceRunMonad S T.
refine (let stm := @ModelStateTraceMonad.mk S T in
@MonadStateTraceRun.Pack S T (fun A => S * list T -> A * (S * list T))
  (@MonadStateTraceRun.Class S T (fun A => S * list T -> A * (S * list T))
    (MonadStateTrace.class stm)
    (MonadRun.mixin (MonadRun.class (@ModelRunMonad.mk S T)))
    (@MonadStateTraceRun.Mixin _ _ (@ModelRunMonad.mk S T) _ _ _ _ _ _))).
by [].
by [].
by [].
Defined.
End ModelStateTraceRunMonad.
