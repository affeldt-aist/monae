Require Import ssreflect ssrfun ssrbool Eqdep List.
Import ListNotations.
Require Import monad state_monad trace_monad smallstep.
From mathcomp Require Import seq.

(* contents:
  Denotation of the imperative language given in terms of the state/trace monad.
  Prove that the small-step semantics is equivalent to the denotation.
  1. Section DenotationalSemantics
  2. Section semantics_equivalence
*)

Set Bullet Behavior "Strict Subproofs".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section DenotationalSemantics.

Variables S T : Type.
Variable M : stateTraceMonad S T.

Fixpoint denote A (p : program A) : M A :=
  match p with
  | p_ret _ v => Ret v
  | p_bind _ _ m f => do a <- denote m; denote (f a)
  | p_cond _ b p1 p2 => if b then denote p1 else denote p2
  | p_repeat n p => (fix loop (m : nat) : M unit :=
    match m with
    | 0 => Ret tt
    | Datatypes.S m' => denote p >> loop m'
    end) n
  | p_while fuel c p => (fix loop (m : nat) : M unit :=
    match m with
    | 0 => Ret tt
    | Datatypes.S m' =>
      do s <- stGet ;
      if c s then denote p >> loop m' else Ret tt
    end) fuel
  | p_get => stGet
  | p_put s' => stPut s'
  | p_mark t => stMark t
  end.

Notation "'Repeat' n {{ p }}" := (
  (fix loop (m : nat) : MonadStateTrace.m M unit :=
   match m with
   | 0 => Ret tt
   | Datatypes.S m' => denote p >> loop m'
   end) n) (at level 200).

Notation "'While' fuel @ c {{ p }}" := (
  (fix loop (m : nat) : MonadStateTrace.m M unit :=
   match m with
   | 0 => Ret tt
   | Datatypes.S m' =>
     do s <- stGet ;
     if c s then denote p >> loop m' else Ret tt
   end) fuel) (at level 200).

Fixpoint denote_continuation (k : continuation) : M (@continuation T S) :=
  match k with
  | stop A a => Ret (stop A a)
  | p `; f =>
      do a <- denote p ;
      denote_continuation (f a)
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
