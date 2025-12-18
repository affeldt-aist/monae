(* monae: Monadic equational reasoning in Rocq                                *)
(* Copyright (C) 2025 monae authors, license: LGPL-2.1-or-later               *)
Ltac typeof X := type of X.
From mathcomp Require Import all_ssreflect ssralg ssrint.
Require Import ihierarchy imonad_lib.

(**md**************************************************************************)
(* # Example using the trace monad                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.

Definition marks T {M : traceMonad T} (l : seq T) : M (seq unit) :=
  sequence (map mark l).

Local Open Scope ring_scope.

Section statetrace_program_equivalence_example.
Local Open Scope do_notation.
Variable M : stateTraceMonad int nat.

Let st_none1 : M int :=
  do _ <- st_mark `|0|;
  do n <- st_get;
  do _ <- st_put (intZmod.addz n 1);
  do _ <- st_mark `|n|;
  Ret n.

Let st_none2 : M int :=
  do n <- st_get;
  do _ <- st_mark `|0|;
  do _ <- st_mark `|n|;
  do _ <- st_put (intZmod.addz n 1);
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
Variables (T : UU0) (M : stateTraceMonad int T).
Variables (log0 log1 : T).

Definition monadtrace_example (m0 m1 m2 : M nat) : M nat :=
  do x <- m0;
    st_put x%:Z >>
      do y <- st_get;
        st_mark log0 >>
          do z <- m2;
            st_mark log1 >>
            Ret (x + `|y| + z).

End statetrace_example.

Definition assoc {A B C : Type} : (A * B) * C -> A * (B * C) :=
  fun x => (x.1.1, (x.1.2, x.2)).

Definition assoc_inv {A B C : Type} : A * (B * C) -> (A * B) * C :=
  fun x => ((x.1, x.2.1), x.2.2).

Definition assoc_opt
  {A B C : Type} (x : option (A * B) * C) : option (A * (B * C)) :=
match x with
| (None, _) => None
| (Some (a, b), c) => Some (a, (b, c))
end.

Section relation_statetrace_state_trace.
Variables (S T : UU0) (MN : stateTraceReifyMonad S T).

Lemma st_get_get (M : stateReifyMonad S) s :
  reify (st_get : MN _) s = assoc_opt (reify (get : M _) s.1, s.2).
Proof. by case: s => s1 s2; rewrite reifyget reifystget. Qed.

Lemma st_put_put (M : stateReifyMonad S) s s' :
  reify (st_put s' : MN _) s = assoc_opt (reify (put s' : M _) s.1, s.2).
Proof. by case: s => s1 s2; rewrite reifyput reifystput. Qed.

Fail Lemma stMark_Mark (M : traceReifyMonad T) s t :
  Reify (stMark t : MN _) s =
let x := Reify (Mark t : M _) s.2 in
match x with
| None => None
| Some x => Some (x.1, (s.1, x.2))
end.
(*Proof. by rewrite reifytmark reifystmark. Qed.*)

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

(* TODO: hb *)
Module Tracer.
Record class m (v : traceMonad unit) (mv : MonadTrans.t m v) : Type := Class {
  (* NB: see also monad_transformer.v *)
  lift_ret : forall (A : UU0) (a : A), Lift mv (Ret a) = Ret a :> v A ;
  lift_bind : forall A B (m0 : m A) (f : A -> m B),
    Lift mv (m0 >>= f) = Lift mv m0 >>= (@MonadTrans.lift _ _ mv _ \o f) :> v B ;
  drop_ret : forall (A : UU0) (a : A), Drop mv (Ret a) = Ret a :> m A ;
  drop_bind : forall A B (m0 : v B) (f : B -> v A),
    Drop mv (m0 >>= f) = Drop mv m0 >>= (@MonadTrans.drop _ _ mv _ \o f) :> m A ;
  drop_mark : Drop mv (mark tt) = Ret tt
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
  mark tt >>
  do z <- Lift M m2;
  Ret (x + y + z).

End tracer_example.
