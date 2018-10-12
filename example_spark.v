Require Import FunctionalExtensionality Coq.Program.Tactics ProofIrrelevance.
Require Classical.
Require Import ssreflect ssrmatching ssrfun ssrbool.
From mathcomp Require Import eqtype ssrnat seq path div choice fintype tuple.
From mathcomp Require Import finfun bigop.
Require Import monad.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* from mu2017 *)

Section spark_aggregation.
Local Open Scope mu_scope.

Section definitions.
Variable M : altMonad.

Variables (A B : Type).

Definition deterministic A B (f : A -> M B) := exists g : A -> B, f = Ret \o g.

Variables (b : B) (mul : B -> A -> B) (add : B -> B -> B).

Let Partition A := seq A.
Let RDD A := seq (Partition A).

Definition aggregate : RDD A -> M B :=
  foldl add b (o) (perm \o map (foldl mul b)).

End definitions.
Arguments aggregate {M A B}.

Section aggregate_deterministic.

Section foldl_perm_deterministic1.
Variable M : altCIMonad.
Variables (A B : Type) (op : B -> A -> B) (b : B).
Local Notation "x (.) y" := (op x y) (at level 11).
Hypothesis opP : forall (x y : A) (w : seq A), (foldl op b w (.) x) (.) y = (foldl op b w (.) y) (.) x.

(* from mu2017 *)
Lemma lemma_35 a :
  foldl op b (o) insert a = Ret \o foldl op b \o (rcons^~ a) :> (_ -> M _).
Proof.
apply functional_extensionality => xs; move: xs; elim/last_ind => [/=|xs y IH].
  by rewrite fcomp_ext insertE fmap_ret.
rewrite fcomp_ext.
rewrite insert_rcons.
rewrite naturality_nondeter fmap_ret.
rewrite -fmap_comp.
have H : forall w, foldl op b \o rcons^~ w = op^~ w \o foldl op b.
  by move=> w; apply functional_extensionality => ws /=; rewrite -cats1 foldl_cat.
rewrite (H y).
rewrite fmap_comp.
rewrite fcomp_ext in IH.
rewrite IH.
rewrite -[in X in _ [~i] X]bindretf.
rewrite bindretf.
rewrite -{1}compA.
rewrite fmap_ret.
rewrite (H a).
rewrite [in X in _ [~i] X]/=.
rewrite opP.
rewrite /= -!cats1 -catA /=.
rewrite foldl_cat /=.
by rewrite altmm.
Qed.

End foldl_perm_deterministic1.

Section foldl_perm_deterministic.
Variable M : altCIMonad.
Variables (A B : Type) (op : B -> A -> B).
Local Notation "x (.) y" := (op x y) (at level 11).
Hypothesis opP : forall (x y : A) (w : B), (w (.) x) (.) y = (w (.) y) (.) x.

Lemma lemma_34 b : foldl op b (o) perm = Ret \o foldl op b :> (_ -> M _).
Proof.
apply functional_extensionality => xs; move: xs b; elim => [/=|x xs IH] b.
  by rewrite fcomp_ext fmap_ret.
rewrite fcomp_ext [in LHS]/= fmap_bind.
have opP' : forall (x y : A) (w : seq A), (foldl op b w (.) x) (.) y = (foldl op b w (.) y) (.) x.
  move=> ? ? ?.
  by rewrite opP.
rewrite_ (lemma_35 M opP').
transitivity ((Ret \o foldl op (b (.) x)) xs : M _); last by [].
rewrite -IH.
rewrite [in RHS]fcomp_ext.
rewrite /fmap.
bind_ext => ys.
rewrite /= -cats1 foldl_cat /=.
congr (Ret _ : M _).
elim: ys b opP' => // y ys ih /= b opP'.
rewrite ih //=.
rewrite -/(foldl op b [::]).
by rewrite opP'.
Qed.

End foldl_perm_deterministic.

Section theorem36.
Variable M : altCIMonad.
Variables (A B : Type) (b : B) (mul : B -> A -> B) (add : B -> B -> B).
Hypotheses (addA : associative add) (addC : commutative add).

(* theorem 3.6 in mu2017, with foldr it is theorem 9 in netys2017 *)
Lemma aggregateE :
  aggregate b mul add = Ret \o foldl add b \o map (foldl mul b) :> (_ -> M _).
Proof.
(* NB: mu2017 is using perm_map (lemma 3.1) and (7) but that does not seem useful*)
rewrite compA -[in RHS]lemma_34 // => x ??; by rewrite -addA (addC x) addA.
Qed.

Lemma deter_aggregate : deterministic (aggregate b mul add : _ -> M _).
Proof. rewrite /deterministic aggregateE //; eexists; reflexivity. Qed.


End theorem36.

End aggregate_deterministic.

End spark_aggregation.
