Require Import Eqdep JMeq List ssreflect.
Import ListNotations.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import hierarchy monad_lib state_lib trace_lib monad_model.

(******************************************************************************)
(*              Application of monadTrace to program semantics                *)
(*                                                                            *)
(* Inductive program, Inductive continuation:                                 *)
(*   Syntax for an imperative language with a primitive to record execution   *)
(*   trace                                                                    *)
(* Section OperationalSemantics, Inductive step:                              *)
(*   A small-step semantics                                                   *)
(* DenotationalSemantics:                                                     *)
(*   Denotation given in terms of the state/trace monad                       *)
(* Section semantics_equivalence:                                             *)
(*.  Prove that the small-step semantics is equivalent to the denotation      *)
(* nonce, nonce_twice, countdown, etc.                                        *)
(*   Examples of programs using traces and their small-step and denotational  *)
(* semantics.                                                                 *)
(*                                                                            *)
(* reference:                                                                *)
(* - R. Affeldt, D. Nowak, T. Saikawa, A Hierarchy of Monadic Effects for     *)
(* Program Verification using Equational Reasoning, MPC 2019                  *)
(******************************************************************************)

Set Universe Polymorphism.
Unset Universe Minimization ToSet.
Set Polymorphic Inductive Cumulativity.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Obligation Tactic := idtac.

Reserved Notation "'p_do' x <- m ; e"
  (at level 60, x ident, m at level 200, e at level 60).
Reserved Notation "'p_do' x : T <- m ; e"
  (at level 60, x ident, m at level 200, e at level 60).

Section Syntax.

Variables T S : Type.

Inductive program : Type -> Type :=
| p_ret  : forall {A}, A -> program A
| p_bind : forall {A B}, program A -> (A -> program B) -> program B
| p_cond : forall {A}, bool -> program A -> program A -> program A
| p_repeat : nat -> program unit -> program unit
| p_while : nat -> (S -> bool) -> program unit -> program unit
| p_get  : program S
| p_put  : S -> program unit
| p_mark : T -> program unit.

Local Notation "'p_do' x <- m ; e" := (p_bind m (fun x => e)).
Local Notation "'p_do' x : T <- m ; e" :=(p_bind m (fun x : T => e)).

Inductive continuation : Type :=
| stop : forall A, A -> continuation
| cont : forall A, program A -> (A -> continuation) -> continuation.

End Syntax.

Arguments program {_ _} _.
Arguments p_ret {_ _ _} _.
Arguments p_bind {_ _ _ _} _ _.
Arguments p_cond {_ _ _} _ _ _.
Arguments p_repeat {_ _} _ _.
Arguments p_while {_ _} _ _ _.
Arguments p_get {_ _}.
Arguments p_put {_ _} _.
Arguments p_mark {_ _} _.
Arguments continuation {_ _}.
Arguments stop {_ _} _ _.
Arguments cont {_ _} _ _ _.

Notation "'p_do' x <- m ; e" := (@p_bind _ _ _ _ m (fun x => e)).
Notation "'p_do' x : T <- m ; e" := (@p_bind _ _ _ _ m (fun x : T => e)).

Notation "p `; k" := (@cont _ _ _ p k) (at level 50).

Section OperationalSemantics.

Variables T S : Type.

Definition state : Type := S * @continuation T S.

Inductive step : state -> option T -> state -> Prop :=
| s_ret  : forall s A a (k : A -> _), step (s, p_ret a `; k) None (s, k a)
| s_bind : forall s A B p (f : A -> program B) k,
  step (s, p_bind p f `; k) None (s, p `; fun a => f a `; k)
| s_cond_true : forall s A p1 p2 (k : A -> _),
  step (s, p_cond true p1 p2 `; k) None (s, p1 `; k)
| s_cond_false : forall s A p1 p2 (k : A -> _),
  step (s, p_cond false p1 p2 `; k) None (s, p2 `; k)
| s_repeat_O : forall s p k, step (s, p_repeat O p `; k) None (s, k tt)
| s_repeat_S : forall s n p k,
  step (s, p_repeat n.+1 p `; k) None
    (s, p `; fun _ => p_repeat n p `; k)
| s_while_true : forall fuel s c p k, c s = true ->
  step (s, p_while fuel.+1 c p `; k) None
    (s, p `; fun _ => p_while fuel c p `; k)
| s_while_false : forall fuel s c p k, c s = false ->
  step (s, p_while fuel.+1 c p `; k) None (s, k tt)
| s_while_broke : forall s c p k, step (s, p_while O c p `; k) None (s, k tt)
| s_get  : forall s k, step (s, p_get `; k) None (s, k s)
| s_put  : forall s s' k, step (s, p_put s' `; k) None (s', k tt)
| s_mark : forall s t k, step (s, p_mark t `; k) (Some t) (s, k tt).

Inductive step_n : nat -> state -> list T -> state -> Prop :=
| sn_0 : forall sk, step_n O sk [] sk
| sn_S_None : forall n sk1 sk2 sk3 l,
  step sk1 None sk2 -> step_n n sk2 l sk3 ->
  step_n n.+1 sk1 l sk3
| sn_S_Some : forall n sk1 sk2 sk3 t l,
  step sk1 (Some t) sk2 -> step_n n sk2 l sk3 ->
  step_n n.+1 sk1 (t :: l) sk3.

Inductive step_star : state -> list T -> state -> Prop :=
| ss_refl : forall sk, step_star sk [] sk
| ss_step_None : forall sk1 sk2 sk3 l,
  step sk1 None sk2 -> step_star sk2 l sk3 -> step_star sk1 l sk3
| ss_step_Some : forall sk1 sk2 sk3 t l,
  step sk1 (Some t) sk2 -> step_star sk2 l sk3 -> step_star sk1 (t :: l) sk3.

Lemma step_star_transitive sk1 sk2 sk3 l l' :
  step_star sk1 l sk2 -> step_star sk2 l' sk3 -> step_star sk1 (l ++ l') sk3.
Proof.
intro Hss1.
revert sk3 l'.
induction Hss1 as
 [ | sk1 sk2 sk3 l Hstep Hss1 IH | sk1 sk2 sk3 t l Hstep Hss1 IH ];
 intros sk3' l' Hss2; [ assumption | | ].
- apply ss_step_None with (sk2 := sk2).
  + exact Hstep.
  + apply IH; exact Hss2.
- apply ss_step_Some with (sk2 := sk2).
  + exact Hstep.
  + apply IH; exact Hss2.
Qed.

Lemma step_star_stop_inv s A a l sk :
  step_star (s, stop A a) l sk -> l = [] /\ sk = (s, stop A a).
Proof.
intro Hss.
inversion Hss.
- split; reflexivity.
- subst.
  match goal with H : step _ _ _ |- _ => inversion H end.
- subst.
  match goal with H : step _ _ _ |- _ => inversion H end.
Qed.

Lemma step_deterministic ski l1 l2 sk1 sk2 :
  step ski l1 sk1 -> step ski l2 sk2 -> l1 = l2 /\ sk1 = sk2.
Proof.
intro Hstep1.
revert l2 sk2.
induction Hstep1; intros l2 sk2 Hstep2;
match goal with
| _ : step (?s, ?k) _ _ |- _ => remember (s, k) as sk1 eqn: Heq2
end; inversion Hstep2; clear Hstep2; subst; try discriminate;
match goal with
| H : _ = _ |- _ => injection H; clear H; intros
end; subst;
repeat match goal with
| H : existT _ _ _ = existT _ _ _ |- _ => apply inj_pair2 in H
end; subst; repeat split; congruence.
Qed.

Lemma step_star_confluent ski sk1 sk2 l1 l2 :
  step_star ski l1 sk1 -> step_star ski l2 sk2 ->
  exists l1' l2' skf,
  step_star sk1 l1' skf /\ step_star sk2 l2' skf /\ l1 ++ l1' = l2 ++ l2'.
Proof.
intro Hss1.
revert l2 sk2.
induction Hss1 as [
    s
  | sk1 sk2' sk3 l1 Hstep1 Hss1 IH
  | sk1 sk2' sk3 t1 l1 Hstep1 Hss1 IH
  ].
- intros l2 sk2 Hss2.
  exists l2. exists []. exists sk2.
  split; [ | split ].
  + exact Hss2.
  + apply ss_refl.
  + rewrite cats0; reflexivity.
- intros l2 sk2 Hss2.
  inversion Hss2 as [
    sk1' Hsk1 Hl2 Hsk2
  | sk1' sk2'' sk2''' l2' Hstep2 Hss2' Hsk1 Hl2 Hsl2
  | sk1' sk2'' sk2''' t2 l2' Hstep2 Hss2' Hsk1 Hl2 Hsl2
  ].
  + subst sk1' l2 sk2.
    do 3 eexists.
    split; [ apply ss_refl | ].
    split; [ eapply ss_step_None; eassumption | ].
    rewrite cats0; reflexivity.
  + subst sk1' l2' sk2'''.
    specialize (step_deterministic Hstep1 Hstep2).
    intros [ [] Heq2].
    subst sk2''.
    apply IH.
    exact Hss2'.
  + subst sk1' l2 sk2'''.
    specialize (step_deterministic Hstep1 Hstep2).
    intros [ [=] ?].
- intros l2 sk2 Hss2.
  inversion Hss2 as [
    sk1' Hsk1 Hl2 Hsk2
  | sk1' sk2'' sk2''' l2' Hstep2 Hss2' Hsk1 Hl2 Hsl2
  | sk1' sk2'' sk2''' t2 l2' Hstep2 Hss2' Hsk1 Hl2 Hsl2
  ].
  + subst sk1' l2 sk2.
    do 3 eexists.
    split; [ apply ss_refl | ].
    split; [ eapply ss_step_Some; eassumption | ].
    rewrite cats0; reflexivity.
  + subst sk1' l2' sk2'''.
    specialize (step_deterministic Hstep1 Hstep2).
    intros [ [=] ?].
  + subst sk1' l2 sk2'''.
    specialize (step_deterministic Hstep1 Hstep2).
    intros [ [= Heq1] Heq2].
    subst t2 sk2''.
    apply IH in Hss2'.
    destruct Hss2' as (l1' & l2'' & skf & Hss3 & Hss4 & Heq).
    do 3 eexists.
    do 2 (split; [ eassumption | ]).
    cbn.
    f_equal.
    exact Heq.
Qed.

Lemma step_star_deterministic ski l1 l2 s1 s2 A1 A2 a1 a2 :
  step_star ski l1 (s1, stop A1 a1) -> step_star ski l2 (s2, stop A2 a2) ->
  l1 = l2 /\ s1 = s2 /\ A1 = A2 /\ JMeq a1 a2.
Proof.
intros Hss1 Hss2.
specialize (step_star_confluent Hss1 Hss2).
intros (l1' & l2' & skf & Hss1' & Hss2' & Heq).
apply step_star_stop_inv in Hss1'.
apply step_star_stop_inv in Hss2'.
destruct Hss1' as [ Heq11 Heq12 ].
destruct Hss2' as [ Heq21 Heq22 ].
subst l1' l2' skf .
do 2 rewrite cats0 in Heq.
injection Heq22; clear Heq22; intros; subst.
match goal with
| H : existT _ _ _ = existT _ _ _ |- _ => apply inj_pair2 in H
end.
subst.
repeat split.
Qed.

Definition run_s {A : Type} (p : program A) (f : A -> continuation) (s : S) :
  {o & {f' & {s' | step (s, p `; f) o (s', f') } } }.
Proof.
destruct p as [ A a | A B p g | A b p1 p2 | n p | fuel c p | | s' | t ];
 try (repeat eexists; constructor).
- destruct b; repeat eexists; constructor.
- destruct n; repeat eexists; constructor.
- destruct fuel.
  + repeat eexists; constructor.
  + case_eq (c s); intro Hcs; repeat eexists.
    * apply s_while_true.
      exact Hcs.
    * apply s_while_false.
      exact Hcs.
Defined.

Definition run_s_n (n : nat)
  {A : Type} (p : program A) (f : A -> continuation) (s : S) :
  option {l & {f' & {s' | step_n n (s, p `; f) l (s', f') } } }.
Proof.
revert n A p f s.
fix run_s_n 1.
intros [ | n' ] A p f s.
- apply Some.
  exists []. exists (cont A p f). exists s.
  apply sn_0.
- destruct (run_s p f s) as (o & [ B b | B p' f' ] & s' & Hstep).
  + destruct n' as [ | n'' ].
    * apply Some.
      destruct o as [ t | ]; repeat eexists.
      -- eapply sn_S_Some.
         ++ exact Hstep.
         ++ apply sn_0.
      -- eapply sn_S_None.
         ++ exact Hstep.
         ++ apply sn_0.
    * apply None.
  + destruct (run_s_n n' B p' f' s') as [ (l & f'' & s'' & Hstep_n') | ].
    * apply Some.
      destruct o as [ t | ]; repeat eexists.
      -- eapply sn_S_Some.
         ++ exact Hstep.
         ++ exact Hstep_n'.
      -- eapply sn_S_None.
         ++ exact Hstep.
         ++ exact Hstep_n'.
    * exact None.
Defined.

Definition run_gen
  {A : Type} (p : program A) (f : A -> continuation) (s : S) :
  {l & {a : A & {s' | step_star (s, p `; f) l (s', f a) } } }.
Proof.
revert f s.
induction p as [ A a | A B p IHp g IHg | A b p1 IHp1 p2 IHp2 |
  n p IHp | fuel c p IHp | | s' | t ];
 intros f s.
- exists []. exists a. exists s.
  abstract (eapply ss_step_None; [ apply s_ret | apply ss_refl ]).
- specialize (IHp (fun a => g a `; f) s).
  destruct IHp as (l1 & a & s' & Hss1).
  specialize (IHg a f s').
  destruct IHg as (l2 & b & s'' & Hss2).
  exists (l1 ++ l2). exists b. exists s''.
  abstract (eapply step_star_transitive; [
    eapply ss_step_None; [ apply s_bind  | apply Hss1 ]
  | exact Hss2
  ]).
- case b.
  + specialize (IHp1 f s).
    destruct IHp1 as (l & a & s' & Hss).
    exists l.
    exists a.
    exists s'.
    abstract (eapply ss_step_None; [ apply s_cond_true | apply Hss ]).
  + specialize (IHp2 f s).
    destruct IHp2 as (l & a & s' & Hss).
    exists l.
    exists a.
    exists s'.
    abstract (eapply ss_step_None; [ apply s_cond_false | apply Hss ]).
- revert s.
  induction n as [ | n' IHn ]; intro s.
  + exists []; exists tt; exists s.
    abstract (eapply ss_step_None; [ apply s_repeat_O | apply ss_refl ]).
  + destruct (IHp (fun _ => p_repeat n' p `; f) s) as (l1 & a1 & s1 & Hss1).
    destruct (IHn s1) as (l2 & a2 & s2 & Hss2).
    exists (l1 ++ l2); exists a2; exists s2.
    eapply ss_step_None; [ apply s_repeat_S | ].
    eapply step_star_transitive; [ eexact Hss1 | exact Hss2 ].
- revert s.
  induction fuel as [ | fuel' IHfuel ]; intro s.
  + exists []; exists tt; exists s.
    abstract (eapply ss_step_None; [ apply s_while_broke | apply ss_refl ]).
  + case_eq (c s); [ intro Htrue | intro Hfalse ].
    * destruct (IHp (fun _ => p_while fuel' c p `; f) s) as (l1 & a1 & s1 & Hss1).
      destruct (IHfuel s1) as (l2 & a2 & s2 & Hss2).
      exists (l1 ++ l2); exists a2; exists s2.
      eapply ss_step_None; [ apply s_while_true; exact Htrue | ].
      eapply step_star_transitive; [ eexact Hss1 | exact Hss2 ].
    * exists []; exists tt; exists s.
      abstract (eapply ss_step_None; [ apply s_while_false; exact Hfalse | apply ss_refl ]).
- exists []. exists s. exists s.
  abstract (eapply ss_step_None; [ apply s_get | apply ss_refl ]).
- exists []. exists tt. exists s'.
  abstract (eapply ss_step_None; [ apply s_put | apply ss_refl ]).
- exists [t]. exists tt. exists s.
  abstract (eapply ss_step_Some; [ apply s_mark | apply ss_refl ]).
Defined.

Definition run_ss {A : Type} (p : program A) (s : S) :
  {l & {a : A & {s' |
  step_star (s, p `; stop A) l (s', stop A a) } } } :=
  run_gen p (stop A) s.

End OperationalSemantics.

Arguments step {_ _} _ _ _.
Arguments step_star {_ _} _ _ _.
Arguments run_s {_ _ _} _ _ _.
Arguments run_s_n {_ _} _ {_} _ _ _.
Arguments run_ss {_ _ _} _ _.

Local Open Scope monae_scope.

Section DenotationalSemantics.

Variables S T : Type.
Variable M : stateTraceMonad S T.

Fixpoint denote {A} (p : program A) : M A :=
  match p with
  | p_ret _ v => Ret v
  | p_bind _ _ m f => denote m >>= (denote \o f)
  | p_cond _ b p1 p2 => if b then denote p1 else denote p2
  | p_repeat n p => (fix loop m : M unit :=
    if m is m'.+1 then denote p >> loop m' else Ret tt) n
  | p_while fuel c p => (fix loop m : M unit :=
    if m is m'.+1 then
      (stGet >>= (fun s =>
      if c s then denote p >> loop m' else Ret tt))
    else Ret tt) fuel
  | p_get => stGet
  | p_put s' => stPut s'
  | p_mark t => stMark t
  end.

Notation "'Repeat' n {{ p }}" := (
  (fix loop (m : nat) : MonadStateTrace.acto M unit :=
   match m with
   | 0 => Ret tt
   | m'.+1 => denote p >> loop m'
   end) n) (at level 200).

Notation "'While' fuel @ c {{ p }}" := (
  (fix loop (m : nat) : MonadStateTrace.acto M unit :=
   match m with
   | 0 => Ret tt
   | m'.+1 =>
     stGet >>= (fun s =>
     if c s then denote p >> loop m' else Ret tt)
   end) fuel) (at level 200).

Fixpoint denote_continuation (k : continuation) : M (@continuation T S) :=
  match k with
  | stop A a => Ret (stop A a)
  | p `; f => denote p >>= (denote_continuation \o f)
  end.

Definition stateTrace_sub A (m : M A) : Type :=
  { p | denote p = m }.

Definition continuation_sub (m : M continuation) : Type :=
  {k | denote_continuation k = m }.

End DenotationalSemantics.

Arguments denote {S} {T} M A.
Arguments denote_continuation {S} {T} M.

Section semantics_equivalence.

Variables S T : Type.
Variable M : stateTraceRunMonad S T.

Lemma denote_prefix_preserved A (m : M A) :
  stateTrace_sub m -> forall s s' l1 l a,
  Run m (s, l1) = (a, (s', l)) ->
  exists l2, l = l1 ++ l2.
Proof.
case=> p <-{m}.
induction p as [ A a | A B p IHp g IHg | A b p1 IHp1 p2 IHp2 |
  n p IHp | fuel c p IHp | | s0 | t ]; cbn;
 intros s s' l1 l a' Heq.
- exists [].
  rewrite cats0.
  by move: Heq; rewrite runret => -[].
- rewrite runbind in Heq.
  case_eq (Run (denote M _ p) (s, l1)).
  intros a (s0, l0) Hp.
  rewrite Hp in Heq.
  move/IHp : Hp => [l2 Hp].
  move/IHg : Heq => [l2' Heq].
  exists (l2 ++ l2').
  by rewrite Heq Hp catA.
- destruct b; [ eapply IHp1 | eapply IHp2 ]; exact Heq.
- revert s l1 Heq.
  induction n as [ | n' IH ]; intros s l1 Heq.
  + exists [].
    rewrite cats0.
    by move: Heq; rewrite runret => -[].
  + rewrite runbind in Heq.
    case_eq (Run (denote M _ p) (s, l1)).
    intros a (s0, l0) Hp.
    move: (IHp _ _ _ _ _ Hp) => [l2 ?].
    subst l0.
    rewrite Hp in Heq.
    move: (IH _ _ Heq) => [l3 ?].
    exists (l2 ++ l3).
    by rewrite catA.
- revert s l1 Heq.
  induction fuel as [ | fuel' IH ]; intros s l1 Heq.
  + exists [].
    rewrite cats0.
    by move: Heq; rewrite runret => -[].
  + rewrite runbind runstget in Heq.
    destruct (c (s, l1).1).
    * rewrite runbind in Heq.
      case_eq (Run (denote M _ p) (s, l1)).
      intros a (s0, l0) Hp.
      move: (IHp _ _ _ _ _ Hp) => [l2 ?].
      subst l0.
      rewrite Hp in Heq.
      move: (IH _ _ Heq) => [l3 ?].
      exists (l2 ++ l3).
      by rewrite catA.
    * exists [].
      rewrite cats0.
      by move: Heq; rewrite runret => -[].
- exists [].
  rewrite cats0.
  by move: Heq; rewrite runstget => -[].
- exists [].
  rewrite cats0.
  by move: Heq; rewrite runstput => -[].
- exists [t].
  by move: Heq; rewrite runstmark -cats1 => -[].
Qed.

Lemma denote_prefix_independent A (m : M A) :
  stateTrace_sub m -> forall s l1 l2,
  Run m (s, l1 ++ l2) =
  let res := Run m (s, l2) in
  (res.1, (res.2.1, l1 ++ res.2.2)).
Proof.
intros [ p Hp ] s l1 l2.
subst m.
elim: p s l1 l2 => /= {A} [A a|A B p1 IH1 p2 IH2|A b p1 IH1 p2 IH2|
  n p IHp|fuel c p IHp||s'|t] s l1 l2.
- by rewrite !runret.
- rewrite [in LHS]runbind [in LHS]IH1.
  rewrite [in RHS]runbind.
  case: (Run (denote M _ p1) (s, l2)) => a' [s' l'] /=.
  by rewrite IH2.
- by case: ifPn => _; [rewrite IH1|rewrite IH2].
- revert s l2.
  induction n as [ | n' IH ]; intros s l2.
  + by rewrite !runret.
  + do 2 rewrite runbind.
    rewrite IHp.
    clear IHp.
    case_eq (Run (denote M _ p) (s, l2)).
    intros a (s0, l0) Hp.
    exact: IH.
- revert s l2.
  induction fuel as [ | fuel' IH ]; intros s l2.
  + by rewrite !runret.
  + do 2 rewrite runbind runstget.
    cbn.
    destruct (c s).
    * do 2 rewrite runbind.
      rewrite IHp.
      clear IHp.
      case_eq (Run (denote M _ p) (s, l2)).
      intros a (s0, l0) Hp.
      exact: IH.
    * by rewrite !runret.
- by rewrite !runstget.
- by rewrite !runstput.
- by rewrite !runstmark rcons_cat.
Qed.

Lemma denote_continuation_prefix_independent (m : M _) :
  continuation_sub m -> forall s l1 l2,
  Run m (s, l1 ++ l2) =
  let res := Run m (s, l2) in
  (res.1, (res.2.1, l1 ++ res.2.2)).
Proof.
intros [ k Hk ].
subst m.
elim: k => // [A a s l1 l2|A p k IH s l1 l2].
by rewrite !runret.
rewrite /= !runbind.
rewrite denote_prefix_independent /=; [ | now exists p ].
destruct (Run (denote M _ p) (s, l2)) as [ a (s', l) ].
by rewrite IH.
Qed.

Lemma step_None_correct s s' k k' l :
  step (s, k) None (s', k') ->
  Run (denote_continuation M k) (s, l) = Run (denote_continuation M k') (s', l).
Proof.
intro Hstep.
remember (s, k) as sk eqn: Heq.
remember None as o eqn: Heqo.
remember (s', k') as sk' eqn: Heq'.
revert s s' k k' l Heq Heq' Heqo.
induction Hstep as
 [ s A a f | s A B p f g | s A p1 p2 k | s A p1 p2 k |
   s p k | s n p k | fuel s c p k Htrue | fuel s c p k Hfalse | s c p k |
   s f | s s' f | s t f ];
 intros s1 s2 k1 k2 l [= Hs1 Hk1] [= Hs2 Hk2] Heqo.
- subst s1 k1 s2 k2.
  by rewrite /= runbind runret.
- subst s1 k1 s2 k2.
  cbn.
  by rewrite bindA.
- subst s1 s2 k1 k2.
  reflexivity.
- subst s1 s2 k1 k2.
  reflexivity.
- subst.
  cbn.
  rewrite bindretf.
  reflexivity.
- subst.
  cbn.
  rewrite bindA.
  reflexivity.
- subst.
  cbn.
  rewrite bindA runbind runstget Htrue bindA.
  reflexivity.
- subst.
  cbn.
  rewrite bindA runbind runstget Hfalse bindretf.
  reflexivity.
- subst.
  cbn.
  rewrite bindretf.
  reflexivity.
- subst s1 k1 s2 k2.
  by rewrite /= runbind runstget.
- subst s1 k1 s2 k2.
  by rewrite /= runbind runstput.
- discriminate Heqo.
Qed.

Lemma step_Some_correct s s' k k' t l :
  step (s, k) (Some t) (s', k') ->
  Run (denote_continuation M k) (s, l) =
  Run (denote_continuation M k') (s', rcons l t).
Proof.
intro Hstep.
remember (s, k) as sk eqn: Heq.
remember (Some t) as o eqn: Heqo.
remember (s', k') as sk' eqn: Heq'.
revert s s' k k' l Heq Heq' Heqo.
induction Hstep as
 [ s A a f | s A B p f g | s A p1 p2 k | s A p1 p2 k |
   s p k | s n p k | fuel s c p k Htrue | fuel s c p k Hfalse | s c p k |
   s f | s s' f | s t' f ];
 intros s1 s2 k1 k2 l [= Hs1 Hk1] [= Hs2 Hk2] Heqo; try discriminate Heqo.
subst s1 k1 s2 k2.
injection Heqo; intro; subst t.
by rewrite /= runbind runstmark.
Qed.

Lemma step_star_correct_gen s s' k k' l l' :
  step_star (s, k) l' (s', k') ->
  Run (denote_continuation M k) (s, l) = Run (denote_continuation M k') (s', l++l').
Proof.
intro Hstep_star.
remember (s, k) as sk eqn: Heq.
remember (s', k') as sk' eqn: Heq'.
revert s s' k k' l Heq Heq'.
induction Hstep_star as
 [ s |
  (s, k) (s', k') (s'', k'') l' Hstep Hstep_star IH |
  (s, k) (s', k') (s'', k'') t l' Hstep Hstep_star IH ];
 intros s1 s2 k1 k2 l1 Heq1 Heq2.
- rewrite cats0.
  by move: Heq2; rewrite Heq1 => -[<- <-].
- move: Heq1 Heq2 => [<- <-] [<- <-].
  apply step_None_correct with (l := l1) in Hstep.
  rewrite Hstep.
  apply IH; reflexivity.
- move: Heq1 Heq2 => [<- <-] [<- <-].
  apply step_Some_correct with (l := []) in Hstep.
  rewrite <- cats0 at 1.
  rewrite denote_continuation_prefix_independent; [ | now exists k ].
  rewrite -> Hstep, (IH _ s'' _ k'');
   [ | reflexivity | reflexivity ].
  cbn.
  rewrite denote_continuation_prefix_independent; [ reflexivity | ].
  now eexists.
Qed.

Proposition step_star_correct
  (s s' : S) (A : Type) (a : A) (p : program A) (l : list T) :
  step_star (s, p `; stop A) l (s', stop A a) ->
  Run (denote M _ p) (s, []) = (a, (s', l)).
Proof.
intro Hss.
apply step_star_correct_gen with (l := []) in Hss.
move: Hss.
rewrite /= runret runbind.
destruct (Run (denote M _ p) (s, [])) as [a'' [s'' l'']].
rewrite runret => -[Heq3 <- <-].
apply inj_pair2 in Heq3.
by rewrite Heq3.
Qed.

Lemma step_star_complete_gen
  (s s' : S) (A : Type) (a : A) (p : program A) (l1 l2 : list T) f :
  Run (denote M _ p) (s, l1) = (a, (s', l1 ++ l2)) ->
  step_star (s, p `; f) l2 (s', f a).
Proof.
revert s s' a l1 l2 f.
induction p as [ A a | A B p IHp g IHg | A b p1 IHp1 p2 IHp2 |
  n p IHp | fuel c p IHp | | s0' | t ]; cbn;
 intros s s' a' l1 l2 f Heq.
- rewrite runret in Heq.
  injection Heq; clear Heq; intros; subst a' s'.
  replace l2 with (@nil T) by
   (revert l2 H; induction l1; [ tauto | intros ? [=]; firstorder ]).
  eapply ss_step_None; [ apply s_ret | apply ss_refl ].
- eapply ss_step_None.
  + apply s_bind.
  + move: Heq.
    rewrite runbind.
    case_eq (Run (denote M _ p) (s, l1)).
    intros a (s0, l0) Hp Heq.
    move: (denote_prefix_preserved ltac:(now eexists) Hp) => [l3 Hl3].
    rewrite Hl3 in Hp.
    apply IHp with (f := (fun a => g a `; f)) in Hp.
    clear IHp.
    move: (denote_prefix_preserved ltac:(now eexists) Heq) => [l4 Hl4].
    rewrite Hl4 in Heq.
    apply IHg with (f := f) in Heq.
    clear IHg.
    subst l0.
    replace l2 with (l3 ++ l4) by
     (induction l1; cbn in Hl4; [ congruence | injection Hl4; tauto ]).
    eapply step_star_transitive.
    * exact Hp.
    * exact Heq.
- destruct b; [
    eapply ss_step_None; [
      apply s_cond_true
    | apply IHp1 with (l1 := l1); exact Heq ]
  | eapply ss_step_None; [
      apply s_cond_false
    | apply IHp2 with (l1 := l1); exact Heq ]
  ].
- revert s l1 l2 Heq.
  induction n as [ | n' IHn ]; intros s l1 l2 Heq.
  + rewrite runret in Heq.
    injection Heq; clear Heq; intros; subst a' s'.
    replace l2 with (@nil T) by
     (revert l2 H; induction l1; [ tauto | intros ? [=]; firstorder ]).
    eapply ss_step_None; [ apply s_repeat_O | apply ss_refl ].
  + rewrite runbind in Heq.
    case_eq (Run (denote M _ p) (s, l1)).
    intros a (s0, l0) Hp.
    rewrite Hp in Heq.
    move: (denote_prefix_preserved ltac:(now eexists) Hp) => [l3 Hl3].
    rewrite Hl3 {l0 Hl3} in Hp, Heq.
    specialize (IHp _ _ _ _ _ (fun _ => p_repeat n' p `; f) Hp).
    assert (Heq':
     Run (denote M _ (p_repeat n' p)) (s0, l1 ++ l3) = (a', (s', l1 ++ l2)))
     by apply Heq.
    move: (denote_prefix_preserved ltac:(now eexists) Heq') => [l4 Hl4].
    rewrite Hl4 in Heq.
    eapply ss_step_None; [ apply s_repeat_S | ].
    have -> : l2 = l3 ++ l4.
      by move/(congr1 (drop (size l1))) : Hl4; rewrite -catA ?drop_size_cat.
    eapply step_star_transitive; [ eexact IHp | eapply IHn; eexact Heq ].
- revert s l1 l2 Heq.
  induction fuel as [ | fuel' IHn ]; intros s l1 l2 Heq.
  + rewrite runret in Heq.
    injection Heq; clear Heq; intros; subst a' s'.
    replace l2 with (@nil T) by
     (revert l2 H; induction l1; [ tauto | intros ? [=]; firstorder ]).
    eapply ss_step_None; [ apply s_while_broke | apply ss_refl ].
  + rewrite runbind runstget in Heq.
    cbn in Heq.
    case_eq (c s); [ intro Htrue | intro Hfalse ].
    * rewrite Htrue runbind in Heq.
      case_eq (Run (denote M _ p) (s, l1)).
      intros a (s0, l0) Hp.
      rewrite Hp in Heq.
      move: (denote_prefix_preserved ltac:(now eexists) Hp) => [l3 Hl3].
      rewrite Hl3 {l0 Hl3} in Hp, Heq.
      specialize (IHp _ _ _ _ _ (fun _ => p_while fuel' c p `; f) Hp).
      assert (Heq':
       Run (denote M _ (p_while fuel' c p)) (s0, l1 ++ l3) = (a', (s', l1 ++ l2)))
       by apply Heq.
      move: (denote_prefix_preserved ltac:(now eexists) Heq') => [l4 Hl4].
      rewrite Hl4 in Heq.
      eapply ss_step_None; [ apply s_while_true; exact Htrue | ].
      have -> : l2 = l3 ++ l4.
        by move/(congr1 (drop (size l1))) : Hl4; rewrite -catA ?drop_size_cat.
      eapply step_star_transitive; [ eexact IHp | eapply IHn; eexact Heq ].
    * move: Heq; rewrite Hfalse runret.
      move=> [<- <-] /(congr1 (drop (size l1))).
      rewrite drop_size_cat // drop_size => <-.
      eapply ss_step_None; [ apply s_while_false; exact Hfalse | apply ss_refl ].
- move: Heq; rewrite runstget.
  move=> [<- <-] /(congr1 (drop (size l1))).
  rewrite drop_size_cat // drop_size => <-.
  eapply ss_step_None; [ apply s_get | apply ss_refl ].
- move: Heq; rewrite runstput.
  move=> [<- <-] /(congr1 (drop (size l1))).
  rewrite drop_size_cat // drop_size => <-.
  eapply ss_step_None; [ apply s_put | apply ss_refl ].
- move: Heq; rewrite runstmark.
  move=> [<- <-] /(congr1 (drop (size l1))).
  rewrite drop_size_cat // drop_rcons // drop_size => <-.
  eapply ss_step_Some; [ apply s_mark | apply ss_refl ].
Qed.

Proposition step_star_complete
  (s s' : S) (A : Type) (a : A) (p : program A) (l : list T) :
  Run (denote M _ p) (s, []) = (a, (s', l)) ->
  step_star (s, p `; stop A) l (s', stop A a).
Proof.
intro Hp.
apply step_star_complete_gen with (l1 := []).
exact Hp.
Qed.

End semantics_equivalence.

Notation "'eT' x y" := (@existT _ _ x y) (at level 200).
Notation "'e' x" := (@exist _ _ x _) (at level 200).

Definition p_nonce : program nat :=
  p_do n <- p_get;
  p_do _ <- p_put (S n);
  p_do _ <- p_mark n;
  p_ret n.

Definition M := @ModelStateTraceRun.mk.

Eval unfold denote, p_nonce in denote (M nat nat) nat p_nonce.

Local Open Scope do_notation.

Definition nonce : M nat nat nat :=
  do n : nat <- stGet;
  do _ : unit <- stPut (S n);
  do _ : unit <- stMark n;
  Ret n.

Compute nonce (0, []).
Compute (denote (M nat nat) nat p_nonce) (0, []).
Compute run_ss p_nonce 0.

Remark denote_p_nonce : denote (M nat nat) nat p_nonce = nonce.
Proof. by []. Qed.

Program Example p_nonce_twice : program bool_eqType :=
  p_do nonce <- p_ret (
    p_do n : nat <- p_get;
    p_do _ : unit <- p_put (S n);
    p_do _ : unit <- p_mark n;
    p_ret n ) ;
  p_do x <- nonce ;
  p_do y <- nonce ;
  p_ret (x == y).

Example nonce_twice : M _ _ _ :=
  do nonce <- Ret (
    do n : nat <- stGet;
    do _ : unit <- stPut (S n);
    do _ : unit <- stMark n;
    Ret n ) ;
  do x <- nonce ;
  do y <- nonce ;
  Ret (Nat.eqb x y).

Compute nonce_twice (0, []).
Compute (denote (M nat nat) bool p_nonce_twice) (0, []).
Compute run_ss p_nonce_twice 0.

Remark denote_p_nonce_twice :
  denote (M nat nat) bool p_nonce_twice = nonce_twice.
Proof. by []. Qed.

Fixpoint countdown (fuel : nat) : M nat bool unit :=
  match fuel with
  | O => Ret tt
  | S fuel' =>
    do n <- stGet ;
    if (n == 0) then
      stMark true
    else
      do _ <- stMark false ; do _ <- stPut (n-1) ; countdown fuel'
  end.

Fixpoint p_countdown (fuel : nat) : program unit :=
  match fuel with
  | O => p_ret tt
  | S fuel' =>
    p_do n <- p_get ;
    p_cond (n == 0) (
      p_mark true
    ) (
      p_do _ <- p_mark false ; p_do _ <- p_put (n-1) ; p_countdown fuel'
    )
  end.

Compute (countdown 100) (5, []).
Compute (denote (M nat bool) unit (p_countdown 100)) (5, []).
Compute run_ss (p_countdown 100) 5.

Remark denote_countdown fuel :
  denote (M nat bool) unit (p_countdown fuel) = countdown fuel.
Proof.
elim: fuel => // n.
rewrite [countdown (S n)]/=.
by move <-.
Qed.

Example p_multiply (a b : nat) : program (T := unit) unit :=
  p_do _ <- p_put 0 ;
  p_repeat b (
    p_do x <- p_get ;
    p_put (a + x)
  ).

Compute run_ss (p_multiply 3 7) 0.

Example p_division (a b : nat) : program (T := unit) unit :=
  p_do _ <- p_put (a, 0);
  p_while a (fun s => b <= fst s) (
    p_do s <- p_get ;
    p_put (fst s - b, S (snd s))
  ).

Compute run_ss (p_division 22 7) (0, 0).

Compute run_s_n 15 (p_division 22 7) (stop unit) (0, 0).
