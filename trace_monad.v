Ltac typeof X := type of X.
Require Import FunctionalExtensionality Coq.Program.Tactics ProofIrrelevance.
Require Classical.
Require Import ssreflect ssrmatching ssrfun ssrbool.
From mathcomp Require Import eqtype ssrnat seq choice fintype tuple.

Require Import monad state_monad.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* WIP *)

(*
Contents:
- Module MonadTrace.
- Module MonadStateTrace.
*)

Module MonadTrace.
Record mixin_of T (m : Type -> Type) : Type := Mixin {
  mark : T -> m unit
}.
Record class_of T (m : Type -> Type) : Type := Class {
  base : Monad.class_of m ; mixin : mixin_of T m }.
Structure t T := Pack { m : Type -> Type; class : class_of T m }.
Definition op_mark T (M : t T) : T -> m M unit :=
  let: Pack _ (Class _ (Mixin x)) := M return T -> m M unit in x.
Arguments op_mark {T M} : simpl never.
Definition baseType T (M : t T) := Monad.Pack (base (class M)).
Module Exports.
Notation Mark := op_mark.
Notation traceMonad := t.
Coercion baseType : traceMonad >-> monad.
Canonical baseType.
End Exports.
End MonadTrace.
Export MonadTrace.Exports.

Definition marks T {M : traceMonad T} (l : seq T) : M (seq unit) :=
  sequence (map Mark l).

Module MonadStateTrace.
Record mixin_of T S (M : stateMonad S) (op : T -> M unit) : Type := Mixin {
  run : forall A, M A -> S * seq T -> A * (S * seq T) ;
  _ : forall A (a : A) s, run (Ret a) s = (a, s) ;
  _ : forall A B (m : M A) (f : A -> M B) s,
    run (Do{ a <- m ; f a}) s =
    let: (a', s') := run m s in run (f a') s' ;
  _ : forall s l, run Get (s, l) = (s, (s, l)) ;
  _ : forall s l s', run (Put s') (s, l) = (tt, (s', l)) ;
  _ : forall t s l, run (op t) (s, l) = (tt, (s, l ++ [:: t]))
}.
Record class_of T S (m : Type -> Type) : Type := Class {
  base : MonadState.class_of S m ;
  mixin : MonadTrace.mixin_of T m ;
  ext : @mixin_of _ _ (MonadState.Pack base)
    (@Mark T (MonadTrace.Pack (MonadTrace.Class (MonadState.base base) mixin)))
}.
Structure t (T S : Type) : Type := Pack {
  m : Type -> Type ;
  class : class_of T S m }.
Definition op_run T S (M : t T S) : forall A, m M A -> S * seq T -> A * (S * seq T) :=
  let: Pack _ (Class _ _ (Mixin x _ _ _ _ _)) := M
  return forall A, m M A -> S * seq T -> A * (S * seq T) in x.
Arguments op_run {T S M A} : simpl never.
Definition baseType T S (M : t T S) := MonadState.Pack (base (class M)).
Module Exports.
Notation Run := op_run.
Notation stateTraceMonad := t.
Coercion baseType : stateTraceMonad >-> stateMonad.
Canonical baseType.
Definition trace_of_statetrace T S (M : stateTraceMonad T S) : traceMonad T :=
  @MonadTrace.Pack T _ (MonadTrace.Class
    (MonadState.base (base (class M))) (mixin (class M))).
Canonical Structure trace_of_statetrace.
End Exports.
End MonadStateTrace.
Export MonadStateTrace.Exports.

Section statetrace_lemmas.
Variables (T S : Type) (M : stateTraceMonad T S).
Lemma runret : forall A (a : A) s, Run (Ret a : M _) s = (a, s).
Proof. by case: M => m [? ? []]. Qed.
Lemma runbind : forall A B (ma : M A) (f : A -> M B) s,
  Run (Do{ a <- ma ; f a}) s =
  let: (a'', s'') := Run ma s in Run (f a'') s''.
Proof. by case: M => m [? ? []]. Qed.
Lemma runget : forall s l, Run (Get : M _) (s, l) = (s, (s, l)).
Proof. by case: M => m [? ? []]. Qed.
Lemma runput : forall s l s', Run (Put s' : M _) (s, l) = (tt, (s', l)).
Proof. by case: M => m [? ? []]. Qed.
Lemma runmark : forall t s l, Run (Mark t : M _) (s, l) = (tt, (s, l ++ [:: t])).
Proof. by case: M => m [? ? []]. Qed.
End statetrace_lemmas.

Section statetrace_example.
Variables (T : Type) (m : stateTraceMonad T BinInt.Z).
Variables (log0 log1 : T).

Definition monadtrace_example (m0 m1 m2 : m nat) : m nat :=
  Do{ x <- m0;
    Put (BinInt.Z_of_nat x) >>
      Do{ y <- Get;
        Mark log0 >>
          Do{ z <- m2;
            Mark log1 >>
            Ret (x + BinInt.Z.abs_nat y + z)%nat}}}.

End statetrace_example.

(* WIP *)

Module MonadTrans.
Structure t (m : monad) (u : monad) : Type := Pack {
  lift : forall A, m A -> u A ;
  drop : forall A, u A -> m A
}.
End MonadTrans.
Arguments MonadTrans.lift {m} {u} _ {_}.
Arguments MonadTrans.drop {m} {u} _ {_}.
Notation "'Lift'" := (MonadTrans.lift).
Notation "'Drop'" := (MonadTrans.drop).

Module Tracer.
Record class m (v : traceMonad unit) (mv : MonadTrans.t m v) : Type := Class {
  lift_ret : forall A (a : A), Lift mv (Ret a) = Ret a :> v A ;
  lift_bind : forall A B (m0 : m A) (f : A -> m B),
    Lift mv (m0 >>= f) = Lift mv m0 >>= (@MonadTrans.lift _ _ mv _ \o f) :> v B ;
  drop_ret : forall A (a : A), Drop mv (Ret a) = Ret a :> m A ;
  drop_bind : forall A B (m0 : v B) (f : B -> v A),
    Drop mv (m0 >>= f) = Drop mv m0 >>= (@MonadTrans.drop _ _ mv _ \o f) :> m A ;
  drop_mark : Drop mv (Mark tt) = Ret tt
}.
(* the monad v is a tracer of the monad m *)
Structure t := Pack { m : monad ;
                      v : traceMonad unit ;
                      mv : MonadTrans.t m v ;
                      class_of : class mv }.
End Tracer.
Coercion Tracer.mv : Tracer.t >-> MonadTrans.t.

Section tracer_example.
Variable (M : Tracer.t).
Let v : traceMonad unit := Tracer.v M.
Let m : monad := Tracer.m M.

Definition tracer_example (m0 m1 m2 : m nat) :=
  Do{ x <- Lift M m0;
    Do{ y <- Lift M m1;
      Mark tt >>
        Do{ z <- Lift M m2;
          Ret (x + y + z)%nat}}} : v nat.

End tracer_example.
