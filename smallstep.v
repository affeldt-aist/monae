(*
  A small-step semantics for an imperative language with a primitive to record
  execution trace.
*)

Require Import Eqdep JMeq List ssreflect.
Import ListNotations.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.
Set Polymorphic Inductive Cumulativity.

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
| p_get  : program S
| p_put  : S -> program unit
| p_mark : T -> program unit.

Local Notation "'p_do' x <- m ; e" := (p_bind m (fun x => e)).
Local Notation "'p_do' x : T <- m ; e" :=(p_bind m (fun x : T => e)).

Inductive continuation : Type :=
| stop : forall (A : Type), A -> continuation
| cont : forall (A : Type), program A -> (A -> continuation) -> continuation.

End Syntax.

Arguments program {_ _} _.
Arguments p_ret {_ _ _} _.
Arguments p_bind {_ _ _ _} _ _.
Arguments p_cond {_ _ _} _ _ _.
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
| s_bind : forall s A B p f (k : B -> _),
  step (s, p_bind p f `; k) None (s, p `; fun a : A => f a `; k)
| s_cond_true : forall s A p1 p2 (k : A -> _),
  step (s, p_cond true p1 p2 `; k) None (s, p1 `; k)
| s_cond_false : forall s A p1 p2 (k : A -> _),
  step (s, p_cond false p1 p2 `; k) None (s, p2 `; k)
| s_get  : forall s k, step (s, p_get `; k) None (s, k s)
| s_put  : forall s s' k, step (s, p_put s' `; k) None (s', k tt)
| s_mark : forall s t k, step (s, p_mark t `; k) (Some t) (s, k tt).

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
end; subst; repeat split.
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
  + rewrite app_nil_r; reflexivity.
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
    rewrite app_nil_r; reflexivity.
  + subst sk1' l2' sk2'''.
    specialize (step_deterministic _ _ _ _ _ Hstep1 Hstep2).
    intros [ [] Heq2].
    subst sk2''.
    apply IH.
    exact Hss2'.
  + subst sk1' l2 sk2'''.
    specialize (step_deterministic _ _ _ _ _ Hstep1 Hstep2).
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
    rewrite app_nil_r; reflexivity.
  + subst sk1' l2' sk2'''.
    specialize (step_deterministic _ _ _ _ _ Hstep1 Hstep2).
    intros [ [=] ?].
  + subst sk1' l2 sk2'''.
    specialize (step_deterministic _ _ _ _ _ Hstep1 Hstep2).
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
specialize (step_star_confluent _ _ _ _ _ Hss1 Hss2).
intros (l1' & l2' & skf & Hss1' & Hss2' & Heq).
apply step_star_stop_inv in Hss1'.
apply step_star_stop_inv in Hss2'.
destruct Hss1' as [ Heq11 Heq12 ].
destruct Hss2' as [ Heq21 Heq22 ].
subst l1' l2' skf .
do 2 rewrite app_nil_r in Heq.
injection Heq22; clear Heq22; intros; subst.
match goal with
| H : existT _ _ _ = existT _ _ _ |- _ => apply inj_pair2 in H
end.
subst.
repeat split.
Qed.

Definition run_gen
  {A : Type} (p : program A) (f : A -> continuation) (s : S) :
  {l & {a : A & {s' | step_star (s, p `; f) l (s', f a) } } }.
Proof.
revert f s.
induction p as [ A a | A B p IHp g IHg | A b p1 IHp1 p2 IHp2 | | s' | t ];
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
Arguments run_ss {_ _ _} _ _.
