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

Local Open Scope monae_scope.

Module Function.
Section function.
Variable I : UU0.
Implicit Types A B C : UU0.

Definition Func A := I -> A.
Definition pure A (a : A) : Func A := fun i => a.
Definition zipMap {A B C}
  (f : Func (A -> B -> C)) (a : Func A) (b : Func B) :
  Func C := fun i => f i (a i) (b i).
Definition apply A B (f : Func (A -> B)) (a : Func A) :
  Func B := fun i => f i (a i).
Let afidentity : ApplicativeLaws.identity pure apply.
Proof. by []. Qed.
Let afcomposition : ApplicativeLaws.composition pure apply.
Proof. by []. Qed.
Let afhomomorphism : ApplicativeLaws.homomorphism pure apply.
Proof. by []. Qed.
Let afinterchange : ApplicativeLaws.interchange pure apply.
Proof. by []. Qed.
HB.instance Definition _ :=
  isApplicativeFunctor.Build Func
    afidentity afcomposition afhomomorphism afinterchange.

Section func_diag.

Definition F := Func.

Let join' : F \o F ~~> F := 
  fun A t i => t i i.
    
Let join_naturality : naturality (F \o F) F join'.
Proof.
by move=> a b h; apply: boolp.funext => t; apply: boolp.funext => i.
Qed.

Let ret_naturality : naturality idfun F pure.
Proof.
by move=> a b h; apply: boolp.funext => t; apply: boolp.funext => i.
Qed.

HB.instance Definition _ := isNatural.Build _ _ _ join_naturality.
HB.instance Definition _ := isNatural.Build _ _ _ ret_naturality.

Let join : F \o F ~> F := join'.

Let joinretM : JoinLaws.left_unit ret join.
Proof.
by move=> A; apply: boolp.funext => t; apply: boolp.funext => i.
Qed.

Let joinMret : JoinLaws.right_unit ret join.
Proof.
by move=> A; apply: boolp.funext => t; apply: boolp.funext => i.
Qed.

Let joinA : JoinLaws.associativity join.
Proof.
by move=> A; apply: boolp.funext => t; apply: boolp.funext => i.
Qed.
HB.instance Definition _ :=
  isMonad_ret_join.Build Func joinretM joinMret joinA.
End func_diag.
End function.
End Function.

Module Tuple.

Section def.
Implicit Types (n : nat) (A B : UU0).

Definition pure n A  (a : A) : n.-tuple A :=
  [tuple of (nseq n a)].

Definition apply n A B (fs : n.-tuple (A -> B)) (xs : n.-tuple A) : n.-tuple B :=
  [ tuple (tnth fs i) (tnth xs i) | i < n ].
End def.

Section theory.
Variable n : nat.

Lemma afidentity : ApplicativeLaws.identity (pure n) (@apply n).
Proof.
move=> A.
apply: boolp.funext => xs.
apply: eq_from_tnth => i.
by rewrite /apply /pure tnth_mktuple tnth_nseq.
Qed.

Lemma apply_nil A B (u : 0.-tuple A): @apply 0 A B (nil_tuple _) u = (nil_tuple _) .
Proof. by apply: eq_from_tnth => i; case: i => m h. Qed.

Lemma apply_nil' (A B : UU0) (u : 0.-tuple (A -> B)): @apply 0 A B u (nil_tuple _) = (nil_tuple _) .
Proof. by apply: eq_from_tnth => i; case: i => m h. Qed.

Lemma afcomposition : ApplicativeLaws.composition (pure n) (@apply n).
Proof.
move=> A B C u v.
apply: boolp.funext => xs.
apply: eq_from_tnth => i.
by rewrite /apply /pure !tnth_mktuple tnth_nseq.
Qed.

Lemma afhomomorphism : ApplicativeLaws.homomorphism (pure n) (@apply n).
Proof.
move=> A B f x.
apply: eq_from_tnth => i.
by rewrite /apply /pure !tnth_mktuple !tnth_nseq.
Qed.

Let afinterchange : ApplicativeLaws.interchange (pure n) (@apply n).
Proof.
move=> A B fs x.
apply: eq_from_tnth => i.
by rewrite /apply /pure !tnth_mktuple !tnth_nseq.
Qed.

HB.instance Definition _ :=
  isApplicativeFunctor.Build (n.-tuple)
    afidentity afcomposition afhomomorphism afinterchange.

Let F := n.-tuple.

Section join_first.
Let join A :=
  match n as m return m.-tuple (m.-tuple A) -> m.-tuple A with
  | 0 => fun=> [tuple of [::]]
  | m.+1 => fun t => tnth t ord0
  end.

Let join_naturality : naturality (F \o F) F join.
Proof.
move=> a b h.
subst F join.
rewrite /actm /= /apply /pure /=.
rewrite /actm /=.
apply: boolp.funext.
case: n => [|m] x /=.
- by rewrite tuple0.
- apply: eq_from_tnth => j.
  rewrite tnth_mktuple.
  by rewrite /apply /pure !tnth_mktuple.
Qed.

Let ret_naturality : naturality idfun F ret.
Proof.
move=> a b h.
rewrite /actm /= /pure /apply.
apply: boolp.funext => t /=.
apply: eq_from_tnth => j.
by rewrite tnth_mktuple !tnth_nseq.
Qed.

Let joinretM : JoinLaws.left_unit ret join.
Proof.
move=> A; apply: boolp.funext.
subst join => /=.
rewrite /pure.
case: n => [|m] t /=.
  by rewrite (tuple0 t).
by rewrite tnth_nseq.
Qed.

Let joinMret : JoinLaws.right_unit ret join.
Proof.
move=> A; apply: boolp.funext.
subst join => /=.
rewrite /actm /= /apply /pure.
case: n => [|m] t /=.
  by rewrite (tuple0 t).
rewrite tnth_mktuple tnth_nseq.
Abort.
(* Cannot be a monad *)

Lemma joinA : JoinLaws.associativity join.
Proof.
move=> A; apply: boolp.funext.
subst join => /=.
rewrite /actm /= /apply /pure.
case: n => [|m] t //=.
by rewrite tnth_mktuple tnth_nseq.
Qed.
End join_first.

Section join_diag.
Let join' : F \o F ~~> F :=
  fun A (t : F (F A)) => [tuple tnth (tnth t i) i | i < n].

Let join_naturality : naturality (F \o F) F join'.
Proof.
move=> a b h; apply: boolp.funext => t /=.
subst F join'.
apply: eq_from_tnth => j.
rewrite /actm /= /apply.
by rewrite !tnth_mktuple /= /actm /= /apply /pure !(tnth_nseq,tnth_mktuple).
Qed.

Let ret_naturality : naturality idfun F (pure n).
Proof.
move=> a b h.
rewrite /actm /= /pure /apply.
apply: boolp.funext => t /=.
apply: eq_from_tnth => j.
by rewrite tnth_mktuple !tnth_nseq.
Qed.

HB.instance Definition _ := isNatural.Build _ _ _ join_naturality.
HB.instance Definition _ := isNatural.Build _ _ _ ret_naturality.

Let join : F \o F ~> F := join'.

Let joinretM : JoinLaws.left_unit ret join.
Proof.
move=> A; apply: boolp.funext => t.
subst join => /=.
rewrite /pure.
apply: eq_from_tnth => j.
by rewrite tnth_mktuple !tnth_nseq.
Qed.

Let joinMret : JoinLaws.right_unit ret join.
Proof.
move=> A; apply: boolp.funext => t.
subst join => /=.
rewrite /pure.
apply: eq_from_tnth => j.
by rewrite tnth_mktuple /actm /= /apply /pure tnth_mktuple !tnth_nseq.
Qed.

Let joinA : JoinLaws.associativity join.
Proof.
move=> A; apply: boolp.funext.
subst join => /= t.
rewrite /actm /= /apply /pure.
apply: eq_from_tnth => j.
by rewrite !(tnth_mktuple,tnth_nseq).
Qed.

HB.instance Definition _ :=
  isMonad_ret_join.Build (n.-tuple) joinretM joinMret joinA.
End join_diag.

End theory.
End Tuple.

Module Const.

Section def.
Definition Const (T : UU0) (e : T) (op : Monoid.law e) (A : UU0) : UU0 := T.
End def.

Section theory.
Variable (T : UU0) (e : T) (op : Monoid.law e).
Implicit Types A B : UU0.

Definition pure A (a : A) : Const op A := e.
Definition apply A B (f : Const op (A -> B)) (a : Const op A) : Const op B := op f a.

Let afidentity : ApplicativeLaws.identity pure apply.
Proof.
move=> A.
apply: boolp.funext => x.
by rewrite /apply /pure Monoid.mul1m.
Qed.

Let afcomposition : ApplicativeLaws.composition pure apply.
Proof.
move=> A B C u v.
apply: boolp.funext => x.
by rewrite /apply /comp /pure Monoid.mul1m Monoid.mulmA.
Qed.

Let afhomomorphism : ApplicativeLaws.homomorphism pure apply.
Proof.
move=> A B f x.
by rewrite /apply /pure Monoid.mul1m.
Qed.

Let afinterchange : ApplicativeLaws.interchange pure apply.
Proof.
move=> A B f x.
by rewrite /apply /pure Monoid.mul1m Monoid.mulm1.
Qed.

HB.instance Definition _ :=
  isApplicativeFunctor.Build
    (Const op) afidentity afcomposition afhomomorphism afinterchange.

Section join.
Let F := Const op.

Let join' : F \o F ~~> F := fun A t => t.

Let join_naturality : naturality (F \o F) F join'.
Proof. by []. Qed.

Let ret_naturality : naturality idfun F ret.
Proof.
move=> a b h.
apply: boolp.funext => t /=.
by rewrite /actm /= /pure /apply Monoid.mul1m.
Qed.

HB.instance Definition _ := isNatural.Build _ _ _ join_naturality.
HB.instance Definition _ := isNatural.Build _ _ _ ret_naturality.

Let join : F \o F ~> F := join'.

Let joinretM : JoinLaws.left_unit ret join.
Proof.
move=> A; apply: boolp.funext => /= t /=.
rewrite /pure.
Abort.
(* Seems impossible, for any definition of join: how can one recover t ? *)

Let joinMret : JoinLaws.right_unit ret join.
Proof.
move=> A; apply: boolp.funext => /= t /=.
by rewrite /join /actm /= /join' /pure /apply Monoid.mul1m.
Qed.

Let joinA : JoinLaws.associativity join.
Proof. by []. Qed.
End join.

End theory.
End Const.

Module Validation.

Section validation.
Inductive Validation (E : UU0) (op : SemiGroup.law E) (T : UU0) : UU0 :=
  | Fail of E 
  | Succ of T.

Variable (E : UU0) (op : SemiGroup.law E).
Definition pure A (a : A) : Validation op A := Succ _ a. 
Definition apply A B (f : Validation op (A -> B)) (a : Validation op A) : 
  Validation op B := 
  match f, a with 
  | Fail fe, Fail ae => Fail _ _ (op fe ae)
  | Fail fe, Succ a' => Fail _ _ fe
  | Succ f', Fail ae => Fail _ _ ae 
  | Succ f', Succ a' => Succ _ (f' a')
  end.

Let afidentity : ApplicativeLaws.identity pure apply.
Proof.
move=> A.
apply: boolp.funext => x.
rewrite /apply /pure.
by case: x; move => i //.
Qed.

Let afcomposition : ApplicativeLaws.composition pure apply.
Proof.
move=> A B C u v.
apply: boolp.funext => x.
rewrite /apply /pure.
case: u; move => ?; case: v; move => ?; case: x; move => ? // /=.
by rewrite SemiGroup.mulmA.
Qed.

Let afhomomorphism : ApplicativeLaws.homomorphism pure apply.
Proof.
move=> A B f x.
by rewrite /apply /pure //.
Qed.

Let afinterchange : ApplicativeLaws.interchange pure apply.
Proof.
move=> A B f x.
by rewrite /apply /pure.
Qed.

HB.instance Definition _ :=
  isApplicativeFunctor.Build
    (Validation op) afidentity afcomposition afhomomorphism afinterchange.

End validation.
End Validation.