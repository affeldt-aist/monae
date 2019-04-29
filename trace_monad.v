Ltac typeof X := type of X.
Require Import ZArith ssreflect ssrmatching ssrfun ssrbool.
From mathcomp Require Import eqtype ssrnat seq choice fintype tuple.
From infotheo Require Import ssrZ.
Require Import monad state_monad.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*
Contents:
- Module MonadTrace.
- Module MonadTraceRun.
- Module MonadStateTrace.
- Module MonadStateTraceRun.
- wip
*)

Module MonadTrace.
Record mixin_of T (m : Type -> Type) : Type := Mixin {
  mark : T -> m unit
}.
Record class_of T (m : Type -> Type) : Type := Class {
  base : Monad.class_of m ; mixin : mixin_of T m }.
Structure t T := Pack { m : Type -> Type; class : class_of T m }.
Definition baseType T (M : t T) := Monad.Pack (base (class M)).
Module Exports.
Definition Mark T (M : t T) : T -> m M unit :=
  let: Pack _ (Class _ (Mixin x)) := M return T -> m M unit in x.
Arguments Mark {T M} : simpl never.
Notation traceMonad := t.
Coercion baseType : traceMonad >-> monad.
Canonical baseType.
End Exports.
End MonadTrace.
Export MonadTrace.Exports.

Definition marks T {M : traceMonad T} (l : seq T) : M (seq unit) :=
  sequence (map Mark l).

Module MonadTraceRun.
Record mixin_of T (M : runMonad (seq T)) (mark : T -> M unit) : Type := Mixin {
  _ : forall t l, Run (mark t) l = (tt, rcons l t)
}.
Record class_of T (m : Type -> Type) : Type := Class {
  base : MonadTrace.class_of T m ;
  base2 : MonadRun.mixin_of _ (Monad.Pack (MonadTrace.base base)) ;
  mixin : @mixin_of _ (MonadRun.Pack (MonadRun.Class base2))
    (@Mark _ (MonadTrace.Pack base));
}.
Structure t T : Type := Pack { m : Type -> Type ;
  class : class_of T m }.
Definition baseType T (M : t T) := MonadTrace.Pack (base (class M)).
Module Exports.
Notation traceRunMonad := t.
Coercion baseType T (M : traceRunMonad T) : traceMonad T := baseType M.
Canonical baseType.
Definition trace_of_run T (M : traceRunMonad T) : runMonad (seq T) :=
  MonadRun.Pack (MonadRun.Class (base2 (class M))).
Canonical trace_of_run.
End Exports.
End MonadTraceRun.
Export MonadTraceRun.Exports.

Section tracerun_lemmas.
Variables (T : Type) (M : traceRunMonad T).
Lemma runtmark : forall s t, Run (Mark t : M _) s = (tt, rcons s t).
Proof. by case: M => m [? ? []]. Qed.
End tracerun_lemmas.

Module MonadStateTrace.
Record mixin_of S T (M : monad) : Type := Mixin {
  st_get : M S ;
  st_put : S -> M unit ;
  st_mark : T -> M unit ;
  _ : forall s s', st_put s >> st_put s' = st_put s' ;
  _ : forall s, st_put s >> st_get = st_put s >> Ret s ;
  _ : st_get >>= st_put = skip ;
  _ : forall k : S -> S -> M S,
      st_get >>= (fun s => st_get >>= k s) = st_get >>= fun s => k s s ;
  _ : forall s e, st_put s >> st_mark e = st_mark e >> st_put s ;
  _ : forall e (k : _ -> _ S), st_get >>= (fun v => st_mark e >> k v) =
                         st_mark e >> st_get >>= k
}.
Record class_of S T (m : Type -> Type) : Type := Class {
  base : Monad.class_of m ;
  mixin : mixin_of S T (Monad.Pack base)
}.
Structure t S T : Type := Pack { m : Type -> Type ; class : class_of S T m }.
Definition baseType S T (M : t S T) := Monad.Pack (base (class M)).
Module Exports.
Definition stGet S T (M : t S T) : m M S :=
  let: Pack _ (Class _ (Mixin x _ _ _ _ _ _ _ _)) := M return m M S in x.
Arguments stGet {S T M} : simpl never.
Definition stPut S T (M : t S T) : S -> m M unit :=
  let: Pack _ (Class _ (Mixin _ x _ _ _ _ _ _ _)) := M return S -> m M unit in x.
Arguments stPut {S T M} : simpl never.
Definition stMark S T (M : t S T) : T -> m M unit :=
  let: Pack _ (Class _ (Mixin _ _ x _ _ _ _ _ _)) := M return T -> m M unit in x.
Arguments stMark {S T M} : simpl never.
Notation stateTraceMonad := t.
Coercion baseType : stateTraceMonad >-> monad.
Canonical baseType.
End Exports.
End MonadStateTrace.
Export MonadStateTrace.Exports.

Section statetrace_lemmas.
Variables (S T : Type) (M : stateTraceMonad S T).
Lemma st_putput s s' : stPut s >> stPut s' = stPut s' :> M _.
Proof. by case: M => m [? []]. Qed.
Lemma st_putget s : stPut s >> stGet = stPut s >> Ret s :> M _.
Proof. by case: M => m [? []]. Qed.
Lemma st_getputskip : stGet >>= stPut = skip :> M _.
Proof. by case: M => m [? []]. Qed.
Lemma st_getget (k : S -> S -> M S) :
  stGet >>= (fun s => stGet >>= k s) = stGet >>= fun s => k s s.
Proof. by case: M k => m [? []]. Qed.
Lemma st_putmark s e : stPut s >> stMark e = stMark e >> stPut s :> M _.
Proof. by case: M => m [? []]. Qed.
Lemma st_getmark e (k : S -> M S) :
  stGet >>= (fun v => stMark e >> k v) = stMark e >> stGet >>= k.
Proof. by case: M k => m [? []]. Qed.
End statetrace_lemmas.

Local Open Scope zarith_ext_scope.

Section statetrace_program_equivalence_example.

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

Module MonadStateTraceRun.
Record mixin_of S T (M : runMonad (S * seq T)) (st_get : M S)
  (st_put : S -> M unit) (st_mark : T -> M unit) : Type := Mixin {
  _ : forall s l, Run st_get (s, l) = (s, (s, l)) ;
  _ : forall s l s', Run (st_put s') (s, l) = (tt, (s', l)) ;
  _ : forall t s l, Run (st_mark t) (s, l) = (tt, (s, rcons l t))
}.
Record class_of S T (m : Type -> Type) : Type := Class {
  base : MonadStateTrace.class_of S T m ;
  base2 : MonadRun.mixin_of (S * seq T) (Monad.Pack (MonadStateTrace.base base)) ;
  mixin : @mixin_of _ _ (MonadRun.Pack (MonadRun.Class base2))
    (@stGet _ _ (MonadStateTrace.Pack base))
    (@stPut _ _ (MonadStateTrace.Pack base))
    (@stMark _ _ (MonadStateTrace.Pack base)) ;
}.
Structure t S T : Type := Pack { m : Type -> Type ;
  class : class_of S T m }.
Definition baseType S T (M : t T S) := MonadStateTrace.Pack (base (class M)).
Module Exports.
Notation stateTraceRunMonad := t.
Coercion baseType (S T : Type) (M : stateTraceRunMonad S T) : stateTraceMonad S T := baseType M.
Canonical baseType.
Definition statetrace_of_run S T (M : stateTraceRunMonad S T) : runMonad (S * seq T) :=
  MonadRun.Pack (MonadRun.Class (base2 (class M))).
Canonical statetrace_of_run.
End Exports.
End MonadStateTraceRun.
Export MonadStateTraceRun.Exports.

Section statetracerun_lemmas.
Variables (S T : Type) (M : stateTraceRunMonad S T).
Lemma runstget : forall s, Run (stGet : M _) s = (s.1, s).
Proof. by case: M => m [? ? [? ? ?]] []. Qed.
Lemma runstput : forall s s', Run (stPut s' : M _) s = (tt, (s', s.2)).
Proof. by case: M => m [? ? [? ? ?]] []. Qed.
Lemma runstmark : forall t s, Run (stMark t : M _) s = (tt, (s.1, rcons s.2 t)).
Proof. by case: M => m [? ? [? ? ?]] t []. Qed.
End statetracerun_lemmas.

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

(* WIP *)

Module MonadTrans.
Structure t (m : monad) (u : monad) : Type := Pack {
  lift : forall A, m A -> u A ;
  drop : forall A, u A -> m A
}.
End MonadTrans.
Arguments MonadTrans.lift {m} {u} _ {_}.
Arguments MonadTrans.drop {m} {u} _ {_}.
Notation "'Lift'" := MonadTrans.lift.
Notation "'Drop'" := MonadTrans.drop.

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

Definition tracer_example (m0 m1 m2 : m nat) : v _ :=
  do x <- Lift M m0;
  do y <- Lift M m1;
  Mark tt >>
  do z <- Lift M m2;
  Ret (x + y + z).

End tracer_example.
