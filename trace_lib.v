Ltac typeof X := type of X.
Require Import ZArith.
From mathcomp Require Import all_ssreflect.
From infotheo Require Import ssrZ.
Require Import hierarchy monad_lib.

(******************************************************************************)
(*                     Example using the trace monad                          *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.

Definition marks T {M : traceMonad T} (l : seq T) : M (seq unit) :=
  sequence (map Mark l).

Local Open Scope zarith_ext_scope.

Section statetrace_program_equivalence_example.
Local Open Scope do_notation.
Variable M : stateTraceMonad Z nat.

Let st_none1 : M Z :=
  do _ <- stMark '|0|;
  do n <- stGet;
  do _ <- stPut (n + 1)%Z;
  do _ <- stMark '|n|;
  Ret n.

Let st_none2 : M Z :=
  do n <- stGet;
  do _ <- stMark '|0|;
  do _ <- stMark '|n|;
  do _ <- stPut (n + 1)%Z;
  Ret n.

Goal st_none1 = st_none2.
Proof.
rewrite /st_none1 /st_none2 st_getmark bindA.
bind_ext; case.
bind_ext => n.
by rewrite -bindA st_putmark bindA.
Qed.

End statetrace_program_equivalence_example.

Section statetrace_example.
Local Open Scope do_notation.
Variables (T : Type) (M : stateTraceMonad Z T).
Variables (log0 log1 : T).

Definition monadtrace_example (m0 m1 m2 : M nat) : M nat :=
  do x <- m0;
    stPut (Z_of_nat x) >>
      do y <- stGet;
        stMark log0 >>
          do z <- m2;
            stMark log1 >>
            Ret (x + Z.abs_nat y + z).

End statetrace_example.

Definition assoc {A B C : Type} : (A * B) * C -> A * (B * C) :=
  fun x => (x.1.1, (x.1.2, x.2)).

Definition assoc_inv {A B C : Type} : A * (B * C) -> (A * B) * C :=
  fun x => ((x.1, x.2.1), x.2.2).

Section relation_statetrace_state_trace.
Variables (S T : Type) (MN : stateTraceRunMonad S T).

Lemma stGet_Get (M : stateRunMonad S) s :
  Run (stGet : MN _) s = assoc (Run (Get : M _) s.1, s.2).
Proof. by rewrite runget runstget; case: s. Qed.

Lemma stPut_Put (M : stateRunMonad S) s s' :
  Run (stPut s' : MN _) s = assoc (Run (Put s' : M _) s.1, s.2).
Proof. by rewrite runput runstput. Qed.

Lemma stMark_Mark (M : traceRunMonad T) s t :
  Run (stMark t : MN _) s = let x := Run (Mark t : M _) s.2 in (x.1, (s.1, x.2)).
Proof. by rewrite runtmark runstmark. Qed.

End relation_statetrace_state_trace.

(* wip *)
Module MonadTrans.
Structure t (m : monad) (u : monad) : Type := Pack {
  lift : forall A, m A -> u A ;
  drop : forall A, u A -> m A
}.
End MonadTrans.
Arguments MonadTrans.lift {m} {u} _ {_}.
Arguments MonadTrans.drop {m} {u} _ {_}.
Local Notation "'Lift'" := MonadTrans.lift.
Local Notation "'Drop'" := MonadTrans.drop.

Module Tracer.
Record class m (v : traceMonad unit) (mv : MonadTrans.t m v) : Type := Class {
  (* NB: see also monad_transformer.v *)
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
Local Open Scope do_notation.
Variable (M : Tracer.t).
Let v : traceMonad unit := Tracer.v M.
Let m : monad := Tracer.m M.

Definition tracer_example (m0 m1 m2 : m nat) : v _ :=
  do x <- Lift M m0;
  do y <- Lift M m1;
  Mark tt >>
  do z <- Lift M m2;
  Ret (x + y + z).

End tracer_example.
