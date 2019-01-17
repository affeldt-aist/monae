Require Import FunctionalExtensionality Coq.Program.Tactics ProofIrrelevance.
Require Classical.
Require Import ssreflect ssrmatching ssrfun ssrbool.
From mathcomp Require Import eqtype ssrnat seq choice fintype tuple.
From mathcomp Require Import boolp classical_sets.

Require Import monad state_monad trace_monad.

(* Contents:
   sample models for the monads in monad.v, state_monad.v, trace_monad.v *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

Section classical_sets_extra.

Hypothesis prop_ext : ClassicalFacts.prop_extensionality.

Lemma bigset1U A B a (f : A -> set B) : bigsetU [set a] f = f a.
Proof.
apply functional_extensionality => b; apply prop_ext.
split => [[a' <-] //| ?]; by exists a.
Qed.
Lemma bigsetU1 A (s : set A) : bigsetU s (@set1 A) = s.
Proof.
apply functional_extensionality => b; apply prop_ext.
split.
- by move=> -[a ?]; rewrite /set1 => ->.
- by move=> ?; rewrite /bigsetU; exists b.
Qed.
Lemma bigsetUA A B C (s : set A) (f : A -> set B) (g : B -> set C) :
  bigsetU (bigsetU s f) g = bigsetU s (fun x => bigsetU (f x) g).
Proof.
apply functional_extensionality => c; apply prop_ext.
split => [[b [a' aa' ?] ?]|[a' aa' [b ? ?]]].
by exists a' => //; exists b.
by exists b => //; exists a'.
Qed.

Lemma setUDl : Laws.bind_left_distributive (fun I A => @bigsetU A I) (@setU).
Proof.
move=> A B /= p q r; apply functional_extensionality => b; apply prop_ext; split.
move=> -[a [?|?] ?]; by [left; exists a | right; exists a].
rewrite /setU => -[[a ? ?]|[a ? ?]]; exists a; tauto.
Qed.

End classical_sets_extra.

Module ModelMonad.

Section identity.
Local Obligation Tactic := by [].
Program Definition identity_class : Monad.class_of id :=
  @Monad.Class _ (fun A (a : A) => a)
  (fun A B (a : id A) (f : A -> id B) => f a) _ _ _.
Definition identity := Monad.Pack identity_class.
End identity.

Section list.
Local Obligation Tactic := idtac.
Program Definition list_class := @Monad.Class _ (fun A (a : A) => [:: a])
  (fun A B (a : seq A) (f : A -> seq B) => flatten (map f a)) _ _ _.
Next Obligation. move=> ? ? ? ? /=; by rewrite cats0. Qed.
Next Obligation. move=> ? ?; by rewrite flatten_seq1. Qed.
Next Obligation.
move=> A B C; elim=> // h t IH f g /=; by rewrite map_cat flatten_cat IH.
Qed.
Definition list := Monad.Pack list_class.
End list.

Section option.
Local Obligation Tactic := idtac.
Program Definition option_class : Monad.class_of option :=
  @Monad.Class _ (@Some) (fun A B (a : option A) (f : A -> option B) =>
    if a isn't Some x then None else f x) _ _ _.
Next Obligation. by []. Qed.
Next Obligation. by []. Qed.
Next Obligation. move=> ?; by case. Qed.
Next Obligation. move=> ? ? ?; by case. Qed.
Definition option := Monad.Pack option_class.
End option.

Section set.
Hypothesis prop_ext : ClassicalFacts.prop_extensionality.
Local Obligation Tactic := idtac.
Program Definition set_class := @Monad.Class _ (@set1) (fun I A => @bigsetU A I) _ _ _.
Next Obligation. move=> ? ? ? ?; exact: bigset1U. Qed.
Next Obligation. move=> ? ?; exact: bigsetU1. Qed.
Next Obligation. move=> ? ? ? ? ? ?; exact: bigsetUA. Qed.
Definition set := Monad.Pack set_class.
End set.

Section state.
Variables S T : Type.
Let m0 := fun A => S * list T -> A * (S * list T).
Definition state : monad.
refine (@Monad.Pack _ (@Monad.Class m0
  (fun A a => fun s => (a, s)) (* ret *)
  (fun A B m f => fun s => let (a, s') := m s in f a s') (* bind *) _ _ _)).
by [].
move=> A f; apply functional_extensionality => ?; by case: f.
move=> A B C a b c; apply functional_extensionality => ?; by case: a.
Defined.
End state.

End ModelMonad.

Module ModelFail.

Section option.
Local Obligation Tactic := by [].
Program Definition option_class := @MonadFail.Class _ _
  (@MonadFail.Mixin ModelMonad.option (@None) _).
Definition option := MonadFail.Pack option_class.
End option.

Section list.
Local Obligation Tactic := by [].
Program Definition list_class := @MonadFail.Class _ _
  (@MonadFail.Mixin ModelMonad.list (@nil) _).
Definition list := MonadFail.Pack list_class.
End list.

Section set.
Hypothesis prop_ext : ClassicalFacts.prop_extensionality.
Local Obligation Tactic := idtac.
Program Definition set_class := @MonadFail.Class _ _
  (@MonadFail.Mixin (ModelMonad.set prop_ext) (@set0) _).
Next Obligation.
move=> A B f /=; apply functional_extensionality => b; apply prop_ext.
by split=> // -[a []].
Qed.
Definition set := MonadFail.Pack set_class.
End set.

End ModelFail.

Module ModelAlt.

Section list.
Local Obligation Tactic := idtac.
Program Definition list_class := @MonadAlt.Class _ _
  (@MonadAlt.Mixin ModelMonad.list (@cat) catA _).
Next Obligation.
move=> A B /= s1 s2 k; by rewrite /Bind /= map_cat flatten_cat.
Qed.
Definition list := MonadAlt.Pack list_class.
End list.

Section set.
Hypothesis prop_ext : ClassicalFacts.prop_extensionality.
Local Obligation Tactic := idtac.
Program Definition set_class := @MonadAlt.Class _ _
  (@MonadAlt.Mixin (ModelMonad.set prop_ext) (@setU) _ _).
Next Obligation. exact: setUA. Qed.
Next Obligation. exact: setUDl. Qed.
Definition set := MonadAlt.Pack set_class.
End set.

End ModelAlt.

Module ModelAltCI.

(* finite sets form the initial model *)
Section set.
Hypothesis prop_ext : ClassicalFacts.prop_extensionality.
Local Obligation Tactic := idtac.
Program Definition set_class := @MonadAltCI.Class _
  (ModelAlt.set_class prop_ext) (@MonadAltCI.Mixin _ (@setU) _ _).
Next Obligation. exact: setUid. Qed.
Next Obligation. exact: setUC. Qed.
Definition set := MonadAltCI.Pack set_class.
End set.

End ModelAltCI.

Module ModelNondet.

Section list.
Local Obligation Tactic := idtac.
Program Definition list_class := @MonadNondet.Class _
  ModelFail.list_class (MonadAlt.mixin ModelAlt.list_class) _.
Next Obligation. apply: MonadNondet.Mixin => //= A l; by rewrite cats0. Qed.
Definition list := MonadNondet.Pack list_class.
End list.

Section set.
Hypothesis prop_ext : ClassicalFacts.prop_extensionality.
Local Obligation Tactic := idtac.
Program Definition set_class := @MonadNondet.Class _
  (ModelFail.set_class _) (MonadAlt.mixin (ModelAlt.set_class prop_ext)) _.
Next Obligation.
apply: MonadNondet.Mixin => //= A p; apply functional_extensionality => a;
  apply prop_ext; rewrite /Fail /= /set0 /setU; split; tauto.
Qed.
Definition set := MonadNondet.Pack list_class.
End set.

End ModelNondet.

Module ModelStateTrace.

Section st.
Variables (S T : Type).
Local Obligation Tactic := idtac.
Program Definition mk : stateTraceMonad S T :=
let m := Monad.class (@ModelMonad.state S T) in
let stm := @MonadStateTrace.Class S T _ m
(@MonadStateTrace.Mixin _ _ (Monad.Pack m)
 (fun s => (s.1, s)) (* st_get *)
 (fun s' s => (tt, (s', s.2))) (* st_put *)
 (fun t s => (tt, (s.1, rcons s.2 t))) (* st_mark *)
 _ _ _ _ _ _) in
@MonadStateTrace.Pack S T _ stm.
Next Obligation. by []. Qed.
Next Obligation. by []. Qed.
Next Obligation. move=> *; by apply functional_extensionality; case. Qed.
Next Obligation. by []. Qed.
Next Obligation. by []. Qed.
Next Obligation. by []. Qed.
End st.
End ModelStateTrace.

Module ModelRun.

Definition mk {S T} : runMonad (S * seq T).
set m := @ModelMonad.state S T.
refine (@MonadRun.Pack _ _ (@MonadRun.Class _ _ (Monad.class m)
  (@MonadRun.Mixin _ m
  (fun A m (s : S * list T) => m s) (* run *) _ _))).
by [].
by [].
Defined.

End ModelRun.

Module ModelStateTraceRun.

Definition mk {S T} :
  stateTraceRunMonad S T.
refine (let stm := @ModelStateTrace.mk S T in
        let run := @ModelRun.mk S T in
@MonadStateTraceRun.Pack S T (fun A => S * list T -> A * (S * list T))
  (@MonadStateTraceRun.Class S T (fun A => S * list T -> A * (S * list T))
    (MonadStateTrace.class stm)
    (MonadRun.mixin (MonadRun.class run))
    (@MonadStateTraceRun.Mixin _ _ run _ _ _ _ _ _))).
by [].
by [].
by [].
Defined.

End ModelStateTraceRun.
