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


(* ----------------------------------------------------------------- *)
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

Section non_monad.

(* For any join, with law,*)
Variable join : F \o F ~> F.
Variable lu : JoinLaws.left_unit ret join.

Let lu_expand : forall A (x : F A), join A (Ret x) = x.
Proof.
move => A x.
(* TODO: better way? *)
have H : forall (A B : UU0) (f : B -> A) (g : A -> B) (x : A), (f \o g) x = id x -> f (g x) = x.
- by [].
apply H.
by rewrite lu //.
Qed.

Lemma necessarity (e' : T): e = e'.
Proof.
have H := lu_expand e'.
have H' := lu_expand e.
suff G: join T (Ret e') = e.
by rewrite -(H T).
by rewrite -H' /= /pure.
Qed.

End non_monad.
End join.
End theory.

Theorem constNonmonadic (T : UU0) (e : T) (op : Monoid.law e): 
  ApplicativeFunctor_isMonad (Const op) -> forall (e' : T), e = e'.
move => H.
by exact (necessarity (ApplicativeFunctor_isMonad.join H) (ApplicativeFunctor_isMonad.joinretM H)).
Qed.
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

Section non_monad.
Let F := Validation op.
Let FF := F \o F.
Variable join : FF ~> F. 
Variable ru : JoinLaws.right_unit pure join.
Variable applyE : forall A B (f : F (A -> B)) (x : F A), 
  apply f x = join B ((_ # fun f' => join _ ((_ # fun x' => pure (f' x')) x)) f).

Let ru_expand : forall A (x : F A), join A ((F # @pure _) x) = x.
Proof.
move => A x.
have H : forall (A B : UU0) (f : B -> A) (g : A -> B) (x : A), (f \o g) x = id x -> f (g x) = x.
- by [].
apply H.
by rewrite ru.
Qed.

Let isFail {A : UU0} (v : F A): UU0 := { e & v = Fail op _ e}.

Let all_fail_is_fmapped A e : (Fail op (F A) e) = (F # @pure _) (Fail op A e).
Proof.
by [].
Qed.

(* join (Fail e) == join (F # pure (Fail e)) =[right unit]= Fail e *)
Let join_fail : forall (A : UU0) (e : E), isFail (join A (Fail op _ e)).
move => A e.
exists e.
by rewrite all_fail_is_fmapped ru_expand.
Defined.

Let j1 (A : UU0) (e : E) : E := 
  projT1 (join_fail A e).

Let j2 (A : UU0) (e : E) : join A (Fail op _ e) = Fail op _ (j1 A e) := 
  projT2 (join_fail A e).

Let j1E A e : j1 A e = e.
Proof.
unfold j1.
by [].
Qed.

Let fmap_fail A B (f : A -> B) (e : E) : (F # f) (Fail op _ e) = Fail op _ e.
Proof.
by [].
Qed.

(* 
apply (Fail a : F (unit -> unit)) (Fail b : F unit) == Fail (op a b)
=[applyE]=    jo ([\f'. jo ([\x'. pure (f' x')] x)] f) [f := Fa, x := Fb]
==            jo ([\f'. jo ([\x'. pure (f' x')] Fb)] Fa)
=[fmap_fail]= jo ([\f'. jo Fb] Fa)
=[fmap_fail]= jo {unit} Fa
=[j2]=        Fail $ f a
*)
Let apply_fail x y : apply (Fail op (unit -> unit) x) (Fail op unit y) = Fail op _ (op x y).
Proof.
by [].
Qed.


Lemma necessarity x y : op x y = x.
Proof.
have H : Fail op unit x = Fail op unit (op x y).
- by rewrite -[in RHS]apply_fail applyE fmap_fail j2.
by case: H.
Qed.

End non_monad.

Let F := Validation op.

Theorem validationNonmonad : ApplicativeFunctor_isMonad F -> forall x y, op x y = x.
Proof.
move => H.
eapply necessarity.
- exact: (ApplicativeFunctor_isMonad.joinMret H).
move => A B f x.
have h := ApplicativeFunctor_isMonad.applyE H.
rewrite /hierarchy.apply /= in h.
rewrite h (ApplicativeFunctor_isMonad.bindE H).
congr (fun x => ApplicativeFunctor_isMonad.join H B ((F # x) f)).
apply: boolp.funext => a.
by rewrite (ApplicativeFunctor_isMonad.bindE H).
Qed.

End validation.

End Validation.
