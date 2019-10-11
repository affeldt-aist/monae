From mathcomp Require Import all_ssreflect.
From mathcomp Require boolp.
Require Import monae_lib monad fail_monad.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* mu2019tr2 *)

Section spark_aggregation.
Local Open Scope mprog.

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

Section foldl_perm_deterministic.
Variable M : altCIMonad.
Variables (A B : Type) (op : B -> A -> B) (b : B).
Local Notation "x (.) y" := (op x y) (at level 11).
Hypothesis opP : forall (x y : A) (w : seq A),
  (foldl op b w (.) x) (.) y = (foldl op b w (.) y) (.) x.

Lemma lemma32 a :
  foldl op b (o) insert a = Ret \o foldl op b \o (rcons^~ a) :> (_ -> M _).
Proof.
rewrite boolp.funeqE; elim/last_ind => [/=|xs y IH].
  by rewrite fcompE insertE fmapE bindretf.
rewrite fcompE.
rewrite insert_rcons.
rewrite naturality_nondeter fmapE bindretf.
rewrite -fmap_oE.
have H : forall w, foldl op b \o rcons^~ w = op^~ w \o foldl op b.
  by move=> w; rewrite boolp.funeqE => ws /=; rewrite -cats1 foldl_cat.
rewrite (H y).
rewrite fmap_oE.
rewrite fcompE in IH.
rewrite IH.
rewrite -[in X in _ [~] X]bindretf.
rewrite bindretf.
rewrite -{1}compA.
rewrite fmapE bindretf.
rewrite (H a).
rewrite [in X in _ [~] X]/=.
rewrite opP.
rewrite /= -!cats1 -catA /=.
rewrite foldl_cat /=.
by rewrite altmm.
Qed.
End foldl_perm_deterministic.

Section foldl_perm_deterministic_contd.
Variable M : altCIMonad.
Variables (A B : Type) (op : B -> A -> B).
Local Notation "x (.) y" := (op x y) (at level 11).
Hypothesis opP : forall (x y : A) (w : B), (w (.) x) (.) y = (w (.) y) (.) x.

Lemma lemma31 b : foldl op b (o) perm = Ret \o foldl op b :> (_ -> M _).
Proof.
rewrite boolp.funeqE => xs; move: xs b; elim => [/=|x xs IH] b.
  by rewrite fcompE fmapE bindretf.
rewrite fcompE fmap_bind.
have opP' : forall (x y : A) (w : seq A), (foldl op b w (.) x) (.) y = (foldl op b w (.) y) (.) x.
  move=> ? ? ?.
  by rewrite opP.
rewrite_ (lemma32 M opP').
transitivity ((Ret \o foldl op (b (.) x)) xs : M _); last by [].
rewrite -IH.
rewrite [in RHS]fcompE.
rewrite fmapE.
bind_ext => ys.
rewrite /= -cats1 foldl_cat /=.
congr (Ret _ : M _).
elim: ys b opP' => // y ys ih /= b opP'.
rewrite ih //=.
rewrite -/(foldl op b [::]).
by rewrite opP'.
Qed.
End foldl_perm_deterministic_contd.

Section theorem43.
Variable M : altCIMonad.
Variables (A B : Type) (b : B) (mul : B -> A -> B) (add : B -> B -> B).
Hypotheses (addA : associative add) (addC : commutative add).

Lemma aggregateE :
  aggregate b mul add = Ret \o foldl add b \o map (foldl mul b) :> (_ -> M _).
Proof.
rewrite -lemma31; last by move=> x ??; rewrite -addA (addC x) addA.
by rewrite /aggregate 2!fcomp_def -compA.
Qed.

Lemma deter_aggregate : deterministic (aggregate b mul add : _ -> M _).
Proof. rewrite /deterministic aggregateE //; eexists; reflexivity. Qed.

End theorem43.

(* TODO: corollary 4.4 *)

End aggregate_deterministic.

Section determinism_implies_homomorphism.

Section homomorphism.
Variables (A B : Type) (add : B -> B -> B) (k : A -> B) (z : B).
Definition is_hom (h : seq A -> B) :=
  h nil = z /\ (forall x : A, h [:: x] = k x) /\
  {morph h : xs ys / xs ++ ys >-> add xs ys}.
End homomorphism.

Section lemma45.

Variable M : nondetMonad.
Variables (A B : Type) (b : B) (mul : B -> A -> B) (add : B -> B -> B).

(* TODO(rei): integrate this into a (new?) monad *)
Hypothesis idempotent_converse :
  forall C m1 m2 x, m1 [~] m2 = Ret x :> M C -> m1 = @RET M _ x /\ m2 = @RET M _ x.
Hypothesis injective_return : forall C x1 x2,
  Ret x1 = Ret x2 :> M C -> x1 = x2.

Hypothesis H : aggregate b mul add = Ret \o foldl mul b \o flatten :> (_ -> M _).

Lemma lemma45a (xss : seq (seq A)) :
  foldl mul b (flatten xss) = foldl add b (map (foldl mul b) xss).
Proof.
case: (perm_is_alt_ret M xss) => m Hm.
have step1 : (Ret \o foldl mul b \o flatten) xss =
  (Ret \o foldl add b \o map (foldl mul b)) xss [~]
  fmap (foldl add b \o map (foldl mul b)) (m : M _).
  rewrite -H /aggregate perm_o_map -fcomp_comp.
  by rewrite fcompE Hm alt_fmapDl fmapE /= bindretf.
apply esym, idempotent_converse in step1.
case: step1 => step11 step12.
apply injective_return in step11.
by rewrite -step11.
Qed.

Lemma lemma45b (m : M _) (xss yss : seq (seq A)) : perm xss = Ret yss [~] m ->
  foldl add b (map (foldl mul b) xss) = foldl add b (map (foldl mul b) yss).
Proof.
move=> K.
have step1 : (Ret \o foldl mul b \o flatten) xss =
  (Ret \o foldl add b \o map (foldl mul b)) yss [~]
  fmap (foldl add b \o map (foldl mul b)) m.
  rewrite -H /aggregate perm_o_map -fcomp_comp.
  by rewrite fcompE K alt_fmapDl fmapE /= bindretf.
have step2 : (foldl mul b \o flatten) xss =
             (foldl add b \o map (foldl mul b)) yss.
  apply esym, idempotent_converse in step1.
  case: step1 => step11 step12.
  apply injective_return in step11.
  by rewrite compE -step11.
by rewrite -lemma45a.
Qed.

End lemma45.

Section theorem46.
Variable M : nondetMonad.
Variables (A B : Type) (b : B) (mul : B -> A -> B) (add : B -> B -> B).

Hypothesis idempotent_converse :
  forall C m1 m2 x, m1 [~] m2 = Ret x :> M C -> m1 = @RET M _ x /\ m2 = @RET M _ x.
Hypothesis injective_return : forall C x1 x2,
  Ret x1 = Ret x2 :> M C -> x1 = x2.

Lemma theorem46lid z zs : z = foldl mul b zs ->
  aggregate b mul add = Ret \o foldl mul b \o flatten :> (_ -> M _) ->
  z = add b z.
Proof.
move=> zzs H.
transitivity (foldl mul b (flatten [:: zs])).
  by rewrite /= cats0.
transitivity (foldl add b (map (foldl mul b) [:: zs])).
  have Hm : perm [:: zs] = Ret [:: zs] [~] (@Fail M _).
    by rewrite /= bindretf insertE altmfail.
  by rewrite (lemma45a idempotent_converse injective_return H).
by rewrite /= -zzs.
Qed.

Lemma theorem46rid z zs : z = foldl mul b zs ->
  aggregate b mul add = Ret \o foldl mul b \o flatten :> (_ -> M _) ->
  z = add z b.
Proof.
move=> zzs H.
transitivity (foldl mul b (flatten [:: zs; [::]])).
  by rewrite /= cats0.
transitivity (foldl add b (map (foldl mul b) [:: zs; [::]])).
  have [m Hm] : exists m : M _, perm [:: zs; [::]] = Ret [:: zs; [::]] [~] m.
    exact: perm_is_alt_ret.
  by rewrite (lemma45a idempotent_converse injective_return H).
rewrite /= -zzs.
by rewrite -(@theorem46lid _ zs).
Qed.

End theorem46.

Section theorem46_contd.
Variable M : nondetCIMonad.
Variables (A B : Type) (b : B) (mul : B -> A -> B) (add : B -> B -> B).

Hypothesis idempotent_converse :
  forall C m1 m2 x, m1 [~] m2 = Ret x :> M C -> m1 = @RET M _ x /\ m2 = @RET M _ x.
Hypothesis injective_return : forall C x1 x2,
  Ret x1 = Ret x2 :> M C -> x1 = x2.

Lemma theorem46C x xs y ys :
 x = foldl mul b xs -> y = foldl mul b ys ->
 aggregate b mul add = Ret \o foldl mul b \o flatten :> (_ -> M _) ->
 add x y = add y x.
Proof.
move=> xxs yys.
transitivity (add x (add y b)).
  by rewrite -(theorem46rid idempotent_converse injective_return yys).
transitivity (foldl add b (map (foldl mul b) [:: xs; ys])).
  rewrite /= -xxs -yys.
  rewrite -(theorem46rid idempotent_converse injective_return yys) //.
  by rewrite -(theorem46lid idempotent_converse injective_return xxs).
transitivity (foldl add b (map (foldl mul b) [:: ys; xs])).
  have [m Hm] : exists m : M _, perm [:: xs; ys] = Ret [:: ys; xs] [~] m.
    have [m Hm] := perm_is_alt_ret M [:: ys; xs].
    by exists m; rewrite -Hm /= !bindretf !insertE !fmapE !bindretf /= altC.
  by rewrite (lemma45b idempotent_converse injective_return H Hm).
by rewrite /= -xxs -yys -(theorem46lid idempotent_converse injective_return yys).
Qed.

(* TODO *)
Lemma theorem46A x xs y ys z zs :
  x = foldl mul b xs -> y = foldl mul b ys -> z = foldl mul b zs ->
  aggregate b mul add = Ret \o foldl mul b \o flatten :> (_ -> M _) ->
  add x (add y z) = add (add x y) z.
Proof.
move=> xxs yys zzs H.
rewrite {1}(theorem46rid (add := add) idempotent_converse injective_return zzs) //.
Abort.

End theorem46_contd.

Section theorem47.
Variable M : nondetCIMonad.
Variables (A B : Type) (b : B) (mul : B -> A -> B) (add : B -> B -> B).

Hypothesis idempotent_converse :
  forall C m1 m2 x, m1 [~] m2 = Ret x :> M C -> m1 = @RET M _ x /\ m2 = @RET M _ x.
Hypothesis injective_return : forall C x1 x2,
  Ret x1 = Ret x2 :> M C -> x1 = x2.

Lemma theorem47 :
 aggregate b mul add = Ret \o foldl mul b \o flatten :> (_ -> M _) ->
 is_hom add (mul b) b (foldl mul b).
Proof.
move=> H.
split; first by [].
split; first by [].
move=> xs ys.
rewrite (_ : xs ++ ys = flatten [:: xs; ys]); last by rewrite /= cats0.
transitivity (foldl add b (map (foldl mul b) [:: xs; ys])).
  case: (perm_is_alt_ret M [:: xs; ys]) => m Hm.
  by rewrite (lemma45a idempotent_converse injective_return H).
transitivity (add (foldl mul b xs) (add (foldl mul b ys) b)).
  rewrite /=.
  rewrite /= -(theorem46lid (zs := xs) (mul := mul) idempotent_converse injective_return _ H) //.
  by rewrite /= -(theorem46rid (zs := ys) (mul := mul) idempotent_converse injective_return _ H).
by rewrite /= -(theorem46rid (zs := ys) (mul := mul) idempotent_converse injective_return _ H).
Qed.

End theorem47.

(* TODO: corollary 4.8 *)

End determinism_implies_homomorphism.

End spark_aggregation.
