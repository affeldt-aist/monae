Require Import JMeq.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import finmap.
From mathcomp Require boolp.
From mathcomp Require Import classical_sets.
From infotheo Require convex classical_sets_ext.
Require Import preamble.
From HB Require Import structures.
Require Import hierarchy.

Set Implicit Arguments.

Module Function.
Section function.
Variable I : UU0.
Definition FuncList (A : UU0) := I -> A.
Definition pure (A : UU0) (a : A) : FuncList A := fun i => a.
Definition zipMap {A B C : UU0} (f : FuncList (A -> B -> C)) (a : FuncList A) (b : FuncList B) 
  : FuncList C := fun i => f i (a i) (b i).
Definition apply (A B : UU0) (f : FuncList (A -> B)) (a : FuncList A) : FuncList B := fun i => 
  f i (a i).
Let afidentity : ApplicativeLaws.identity pure apply.
Proof. by []. Qed.
Let afcomposition : ApplicativeLaws.composition pure apply.
Proof. by []. Qed.
Let afhomomorphism : ApplicativeLaws.homomorphism pure apply.
Proof. by []. Qed.
Let afinterchange : ApplicativeLaws.interchange pure apply.
Proof. by []. Qed.
HB.instance Definition _ :=
  isApplicative.Build FuncList afidentity afcomposition afhomomorphism afinterchange.
End function.
End Function.

Module Tuple.
Section tuple.

Definition pure (n : nat) (A : UU0) (a : A) : n.-tuple A := 
  [tuple of (nseq n a)].


Definition apply (n : nat) (A B : UU0) (fs : n.-tuple (A -> B)) (xs : n.-tuple A) : n.-tuple B :=
  [ tuple (tnth fs i) (tnth xs i) | i < n ].

Variable n : nat.
Lemma afidentity : ApplicativeLaws.identity (pure n) (@apply n).
Proof.
move => A.
apply: boolp.funext => xs.
apply: eq_from_tnth => i.
by rewrite /apply /pure tnth_mktuple tnth_nseq. 
Qed.

Lemma apply_nil (A B : UU0) (u : 0.-tuple A): @apply 0 A B (nil_tuple _) u = (nil_tuple _) .
Proof.
apply: eq_from_tnth => i.
by case: i => m h. 
Qed.

Lemma apply_nil' (A B : UU0) (u : 0.-tuple (A -> B)): @apply 0 A B u (nil_tuple _) = (nil_tuple _) .
Proof.
apply: eq_from_tnth => i.
by case: i => m h. 
Qed.

Lemma afcomposition : ApplicativeLaws.composition (pure n) (@apply n).
Proof.
move => A B C u v.
apply: boolp.funext => xs.
apply: eq_from_tnth => i.
by rewrite /apply /pure !tnth_mktuple tnth_nseq.
Qed.

Lemma afhomomorphism : ApplicativeLaws.homomorphism (pure n) (@apply n).
Proof.
move => A B f x.
apply: eq_from_tnth => i.
by rewrite /apply /pure !tnth_mktuple !tnth_nseq.
Qed.

Let afinterchange : ApplicativeLaws.interchange (pure n) (@apply n).
Proof.
move => A B fs x.
apply: eq_from_tnth => i.
by rewrite /apply /pure !tnth_mktuple !tnth_nseq.
Qed.

HB.instance Definition _ :=
  isApplicative.Build (n.-tuple) afidentity afcomposition afhomomorphism afinterchange.
End tuple.
End Tuple.

Module Const.
Section const.

Variable (T : UU0) (e : T) (op : Monoid.law e).
Definition Const (T : UU0) (e : T) (op : Monoid.law e) (A : UU0) : UU0 := T.
Definition pure (A : UU0) (a : A) : Const op A := e.  
Definition apply (A B : UU0) (f : Const op (A -> B)) (a : Const op A) : Const op B := op f a.

Let afidentity : ApplicativeLaws.identity pure apply.
Proof. 
move => A.
apply: boolp.funext => x.
by rewrite /apply /pure Monoid.mul1m.
Qed.

Let afcomposition : ApplicativeLaws.composition pure apply.
Proof.
move => A B C u v.
apply: boolp.funext => x.
by rewrite /apply /comp /pure Monoid.mul1m Monoid.mulmA.
Qed. 

Let afhomomorphism : ApplicativeLaws.homomorphism pure apply.
Proof. 
move => A B f x.
by rewrite /apply /pure Monoid.mul1m.
Qed.

Let afinterchange : ApplicativeLaws.interchange pure apply.
Proof. 
move => A B f x.
by rewrite /apply /pure Monoid.mul1m Monoid.mulm1.
Qed.

HB.instance Definition _ :=
  isApplicative.Build (Const op) afidentity afcomposition afhomomorphism afinterchange.
End const.
End Const.
