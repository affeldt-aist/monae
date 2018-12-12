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
| p_repeat : nat -> program unit -> program unit
| p_while : nat -> (S -> bool) -> program unit -> program unit
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
  step (s, p_repeat (Datatypes.S n) p `; k) None
    (s, p `; fun _ => p_repeat n p `; k)
| s_while_true : forall fuel s c p k, c s = true ->
  step (s, p_while (Datatypes.S fuel) c p `; k) None
    (s, p `; fun _ => p_while fuel c p `; k)
| s_while_false : forall fuel s c p k, c s = false ->
  step (s, p_while (Datatypes.S fuel) c p `; k) None (s, k tt)
| s_while_broke : forall s c p k, step (s, p_while O c p `; k) None (s, k tt)
| s_get  : forall s k, step (s, p_get `; k) None (s, k s)
| s_put  : forall s s' k, step (s, p_put s' `; k) None (s', k tt)
| s_mark : forall s t k, step (s, p_mark t `; k) (Some t) (s, k tt).

Inductive step_n : nat -> state -> list T -> state -> Prop :=
| sn_0 : forall sk, step_n O sk [] sk
| sn_S_None : forall n sk1 sk2 sk3 l,
  step sk1 None sk2 -> step_n n sk2 l sk3 ->
  step_n (Datatypes.S n) sk1 l sk3
| sn_S_Some : forall n sk1 sk2 sk3 t l,
  step sk1 (Some t) sk2 -> step_n n sk2 l sk3 ->
  step_n (Datatypes.S n) sk1 (t :: l) sk3.

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
