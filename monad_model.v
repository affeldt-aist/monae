Require Import FunctionalExtensionality Coq.Program.Tactics ProofIrrelevance.
Require Classical.
Require Import ssreflect ssrmatching ssrfun ssrbool.
From mathcomp Require Import eqtype ssrnat seq choice fintype tuple.

Require Import monad state_monad trace_monad.

(* Contents:
   sample models for the monads in monad.v, state_monad.v, trace_monad.v *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* TODO: use mathcomp-analysis's classical_sets here *)
Section classical_sets.

Definition cset A := A -> Prop.
Definition sing A a : cset A := fun a' => a = a'.
Definition set_bind A B sa (f : A -> cset B) : cset B :=
    fun b => exists x, sa x /\ f x b.
Definition set_false A : cset A := fun=> False.
Definition union A (a b : cset A) : cset A := fun x => a x \/ b x.

Hypothesis prop_ext : ClassicalFacts.prop_extensionality.

Lemma sing_bind A B a (f : A -> cset B) : set_bind (sing a) f = f a.
Proof.
apply functional_extensionality => b; apply prop_ext.
split => [[a' [<-]] //| ?]; by exists a.
Qed.
Lemma bind_sing A (sa : cset A) : set_bind sa (@sing A) = sa.
Proof.
apply functional_extensionality => b; apply prop_ext.
split => [[a [? <-]] //|?]; by exists b.
Qed.
Lemma set_bindA A B C (sa : cset A) (f : A -> cset B) (g : B -> cset C) :
  set_bind (set_bind sa f) g = set_bind sa (fun x => set_bind (f x) g).
Proof.
apply functional_extensionality => c; apply prop_ext.
split=> [[b [[a'] [aa' ?]] ?]| [a' [aa' [b [? ?]]]]].
by exists a'; split => //; exists b.
by exists b; split => //; exists a'.
Qed.
Lemma unionA A : associative (@union A).
Proof.
move=> /= p q r; apply functional_extensionality => a.
rewrite /union; apply prop_ext; tauto.
Qed.
Lemma unionDl : Laws.bind_left_distributive set_bind union.
Proof.
move=> A B /= p q r; apply functional_extensionality => b; apply prop_ext; split.
move=> -[a [[?|?] ?]]; by [left; exists a | right; exists a].
rewrite /union; move=> [] [a [? ?]]; exists a; tauto.
Qed.
Lemma unionI A : idempotent (@union A).
Proof.
move=> sa; apply functional_extensionality => a; apply prop_ext; split;
  rewrite /union; tauto.
Qed.
Lemma unionC A : commutative (@union A).
Proof.
move=> sa sa'; apply functional_extensionality => a; apply prop_ext; split;
  rewrite /union; tauto.
Qed.

End classical_sets.

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
Program Definition set_class := @Monad.Class _ sing (@set_bind) _ _ _.
Next Obligation. move=> ? ? ? ?; exact: sing_bind. Qed.
Next Obligation. move=> ? ?; exact: bind_sing. Qed.
Next Obligation. move=> ? ? ? ? ? ?; exact: set_bindA. Qed.
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
  (@MonadFail.Mixin (ModelMonad.set prop_ext) set_false _).
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
  (@MonadAlt.Mixin (ModelMonad.set prop_ext) union _ _).
Next Obligation. exact: unionA. Qed.
Next Obligation. exact: unionDl. Qed.
Definition set := MonadAlt.Pack set_class.
End set.

End ModelAlt.

Module ModelAltCI.

(* finite sets form the initial model *)
Section set.
Hypothesis prop_ext : ClassicalFacts.prop_extensionality.
Local Obligation Tactic := idtac.
Program Definition set_class := @MonadAltCI.Class _
  (ModelAlt.set_class prop_ext) (@MonadAltCI.Mixin _ union _ _).
Next Obligation. exact: unionI. Qed.
Next Obligation. exact: unionC. Qed.
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
  apply prop_ext; rewrite /Fail /= /set_false /union; split; tauto.
Qed.
Definition set := MonadNondet.Pack list_class.
End set.

End ModelNondet.

Module ModelStateTrace.

Section st.
Variables (S T : Type).
Definition mk : stateTraceMonad S T :=
let m := Monad.class (@ModelMonad.state S T) in
let stm := @MonadStateTrace.Class S T _ m
(@MonadStateTrace.Mixin _ _ (Monad.Pack m)
 (fun s => (s.1, s)) (* st_get *)
 (fun s' s => (tt, (s', s.2))) (* st_put *)
 (fun t s => (tt, (s.1, rcons s.2 t)))) (* st_mark *) in
@MonadStateTrace.Pack S T _ stm.
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
