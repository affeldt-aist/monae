Ltac typeof X := type of X.
Require Import FunctionalExtensionality Coq.Program.Tactics ProofIrrelevance.
Require Classical.
Require Import ssreflect ssrmatching ssrfun ssrbool.
From mathcomp Require Import eqtype ssrnat seq choice fintype tuple.

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

Module MonadTraceRun.
Record mixin_of T (M : traceMonad T) : Type := Mixin {
  run : forall A, M A -> seq T -> A * seq T ;
  _ : forall A (a : A) s, run (Ret a) s = (a, s) ;
  _ : forall A B (m : M A) (f : A -> M B) s,
    run (do a <- m ; f a) s =
    let (a', s') := run m s in run (f a') s' ;
  _ : forall t l, run (Mark t) l = (tt, l ++ t :: nil) (* TODO: rcons *)
}.
Record class_of T (m : Type -> Type) : Type := Class {
  base : MonadTrace.class_of T m ;
  mixin : mixin_of (MonadTrace.Pack base)
}.
Structure t T : Type := Pack { m : Type -> Type ;
  class : class_of T m }.
Definition op_run T (M : t T) : forall A, m M A -> seq T -> A * seq T :=
  let: Pack _ (Class _ (@Mixin _ _ x _ _ _)) := M
  return forall A, m M A -> seq T -> A * seq T in x.
Arguments op_run {T M A} : simpl never.
Definition baseType T (M : t T) := MonadTrace.Pack (base (class M)).
Module Exports.
Notation Runt := op_run.
Notation traceRunMonad := t.
Coercion baseType T (M : traceRunMonad T) : traceMonad T := baseType M.
Canonical baseType.
End Exports.
End MonadTraceRun.
Export MonadTraceRun.Exports.

Section tracerun_lemmas.
Variables (S : Type) (M : traceRunMonad S).
Lemma runtret : forall A (a : A) s, Runt (Ret a : M _) s = (a, s).
Proof. by case: M => m [? []]. Qed.
Lemma runtbind : forall A B (ma : M A) (f : A -> M B) s,
  Runt (do a <- ma ; f a) s = let: (a'', s'') := Runt ma s in Runt (f a'') s''.
Proof. by case: M => m [? []]. Qed.
Lemma runtmark : forall s t, Runt (Mark t : M _) s = (tt, s ++ t :: nil). (* TODO: rcons *)
Proof. by case: M => m [? []]. Qed.
End tracerun_lemmas.

Module MonadStateTrace.
Record mixin_of S T (M : monad) : Type := Mixin {
  st_get : M S ;
  st_put : S -> M unit ;
  st_mark : T -> M unit ;
}.
Record class_of S T (m : Type -> Type) : Type := Class {
  base : Monad.class_of m ;
  mixin : mixin_of S T (Monad.Pack base)
}.
Structure t S T : Type := Pack { m : Type -> Type ; class : class_of S T m }.
Definition op_st_get S T (M : t S T) : m M S :=
  let: Pack _ (Class _ (Mixin x _ _)) := M return m M S in x.
Arguments op_st_get {S T M} : simpl never.
Definition op_st_put S T (M : t S T) : S -> m M unit :=
  let: Pack _ (Class _ (Mixin _ x _)) := M return S -> m M unit in x.
Arguments op_st_put {S T M} : simpl never.
Definition op_st_mark S T (M : t S T) : T -> m M unit :=
  let: Pack _ (Class _ (Mixin _ _ x)) := M return T -> m M unit in x.
Arguments op_st_mark {S T M} : simpl never.
Definition baseType S T (M : t S T) := Monad.Pack (base (class M)).
Module Exports.
Notation stGet := op_st_get.
Notation stPut := op_st_put.
Notation stMark := op_st_mark.
Notation stateTraceMonad := t.
Coercion baseType : stateTraceMonad >-> monad.
Canonical baseType.
End Exports.
End MonadStateTrace.
Export MonadStateTrace.Exports.

Require Import ZArith ssrZ.

Example st_nonce {M : stateTraceMonad Z nat} : M Z :=
  do n <- stGet;
  do _ <- stPut (n + 1)%Z;
  do _ <- stMark (Z.abs_nat n);
  Ret n.

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
Record mixin_of S T (M : stateTraceMonad S T) : Type := Mixin {
  run : forall A, M A -> S * seq T -> A * (S * seq T) ;
  _ : forall A (a : A) s, run (Ret a) s = (a, s) ;
  _ : forall A B (m : M A) (f : A -> M B) s,
    run (do a <- m ; f a) s =
    let: (a', s') := run m s in run (f a') s' ;
  _ : forall s l, run stGet (s, l) = (s, (s, l)) ;
  _ : forall s l s', run (stPut s') (s, l) = (tt, (s', l)) ;
  _ : forall t s l, run (stMark t) (s, l) = (tt, (s, l ++ t :: nil)) (* TODO: rcons *)
}.
Record class_of S T (m : Type -> Type) : Type := Class {
  base : MonadStateTrace.class_of S T m ;
  mixin : mixin_of (MonadStateTrace.Pack base)
}.
Structure t S T : Type := Pack { m : Type -> Type ;
  class : class_of S T m }.
Definition op_run S T (M : t S T) : forall A, m M A -> S * seq T -> A * (S * seq T) :=
  let: Pack _ (Class _ (@Mixin _ _ _ x _ _ _ _ _)) := M
  return forall A, m M A -> S * seq T -> A * (S * seq T) in x.
Arguments op_run {S T M A} : simpl never.
Definition baseType S T (M : t T S) := MonadStateTrace.Pack (base (class M)).
Module Exports.
Notation Run := op_run.
Notation stateTraceRunMonad := t.
Coercion baseType (S T : Type) (M : stateTraceRunMonad S T) : stateTraceMonad S T := baseType M.
Canonical baseType.
End Exports.
End MonadStateTraceRun.
Export MonadStateTraceRun.Exports.

Section statetracerun_lemmas.
Variables (S T : Type) (M : stateTraceRunMonad S T).
Lemma runstret : forall A (a : A) s, Run (Ret a : M _) s = (a, s).
Proof. by case: M => m [? []]. Qed.
Lemma runstbind : forall A B (ma : M A) (f : A -> M B) s,
  Run (do a <- ma ; f a) s =
  let: (a'', s'') := Run ma s in Run (f a'') s''.
Proof. by case: M => m [? []]. Qed.
Lemma runstget : forall s l, Run (stGet : M _) (s, l) = (s, (s, l)).
Proof. by case: M => m [? []]. Qed.
Lemma runstput : forall s l s', Run (stPut s' : M _) (s, l) = (tt, (s', l)).
Proof. by case: M => m [? []]. Qed.
Lemma runstmark : forall t s l, Run (stMark t : M _) (s, l) = (tt, (s, l ++ t :: nil)). (* TODO: rcons *)
Proof. by case: M => m [? []]. Qed.
End statetracerun_lemmas.

Definition mkStateTraceMonad {S T} : stateTraceMonad S T.
refine (
let m := (@Monad.Class (fun A => S * list T -> A * (S * list T))
  (fun A a => fun s => (a, s)) (* ret *)
  (fun A B m f => fun s => let (a, s') := m s in f a s') (* bind *) _ _ _) in
let stm := (@MonadStateTrace.Class S T _ m
  (@MonadStateTrace.Mixin _ _ (Monad.Pack m)
  (fun s => (s.1, s))  (* get *)
  (fun s' s => (tt, (s', s.2)))
  (fun (t : T) s => (tt, (s.1, s.2 ++ t :: nil))))) in
@MonadStateTrace.Pack S T (fun A => S * list T -> A * (S * list T)) stm).
by [].
move=> A f; apply functional_extensionality => ?; by case: f.
move=> A B C a b c; apply functional_extensionality => ?; by case: a.
Defined.

Definition mkStateTraceRunMonad {S T} :
  stateTraceRunMonad S T.
exact: (let stm := mkStateTraceMonad in
@MonadStateTraceRun.Pack S T (fun A => S * list T -> A * (S * list T))
  (@MonadStateTraceRun.Class S T (fun A => S * list T -> A * (S * list T))
    (MonadStateTrace.class stm)
    (@MonadStateTraceRun.Mixin _ _ stm
      (fun A m (s : S * list T) => m s) (* run *) _ _ _ _ _))).
Defined.

Definition assoc {A B C : Type} (x : (A * B) * C) : A * (B * C) :=
(fst (fst x), (snd (fst x), snd x)).

Definition assoc_inv {A B C : Type} (x : A * (B * C)) : (A * B) * C :=
((fst x, fst (snd x)), snd (snd x)).

Section tmp.
Variables (S T : Type).
Let MN := @mkStateTraceRunMonad S T.

Lemma stGet_Get (M : stateRunMonad S) s :
  Run (stGet : MN _) s = assoc (Run0 (Get : M _) s.1, s.2).
Proof. rewrite state_monad.runget; by case: s. Qed.

Lemma stPut_Put (M : stateRunMonad S) s s' :
  Run (stPut s' : MN _) s = assoc (Run0 (Put s' : M _) s.1, s.2).
Proof. by rewrite state_monad.runput. Qed.

Lemma stMark_Mark (M : traceRunMonad T) s t :
  Run (stMark t : MN _) s =
    let x := Runt (Mark t : M _) s.2 in (x.1, (s.1, x.2)).
Proof. by rewrite runtmark. Qed.

End tmp.

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

Definition tracer_example (m0 m1 m2 : m nat) :=
  do x <- Lift M m0;
  do y <- Lift M m1;
  Mark tt >>
  do z <- Lift M m2;
  Ret (x + y + z).

End tracer_example.
