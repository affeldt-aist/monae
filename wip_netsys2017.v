Require Import FunctionalExtensionality Coq.Program.Tactics ProofIrrelevance.
Require Classical.
Require Import ssreflect ssrmatching ssrfun ssrbool.
From mathcomp Require Import eqtype ssrnat seq path div choice fintype tuple.
From mathcomp Require Import finfun bigop.
Require Import monae_lib hierarchy monad_lib fail_lib example_spark.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* wip (netys2017) *)

Axiom Ret_inj : forall (M : altMonad) A (a1 a2 : A),
  Ret a1 = Ret a2 :> M _ -> a1 = a2.

Axiom alt_Ret : forall (M : altMonad) A (m1 m2 : M A) (a : A),
  m1 [~] m2 = Ret a -> m1 = Ret a /\ m2 = Ret a.

Section list_homomorphism.
Variables (A : Type) (a : A) (add : A -> A -> A).

Definition list_homo B (h : seq B -> A) : Prop :=
  (h [::] = a) /\ (forall s1 s2, h (s1 ++ s2) = add (h s1) (h s2)).
End list_homomorphism.

Section foldl_perm_deterministic.
Variable M : altCIMonad.
Variables (A B : Type) (op : B -> A -> B).
Local Notation "x (.) y" := (op x y) (at level 11).
Hypothesis opP : forall (x y : A) (w : B), (w (.) x) (.) y = (w (.) y) (.) x.

Local Open Scope monae_scope.
Local Open Scope mprog.

(* netys2017 *)
Lemma lemma_1 a b : let op' a b := op b a in
  foldr op' b (o) insert a = Ret \o foldr op' b \o cons a :> (_ -> M _).
Proof.
cbv zeta.
rewrite -mfoldl_rev rev_insert.
rewrite fcomp_def compA.
have opP' : forall (x y : A) (w : seq A), (foldl op b w (.) x) (.) y = (foldl op b w (.) y) (.) x.
  move=> x y w.
  by rewrite opP.
move: (lemma_35 M opP' a); rewrite fcomp_def => ->.
apply functional_extensionality => s /=.
by rewrite -cats1 foldl_cat /= /= -foldl_rev.
Qed.

(* netys2017 *)
Lemma lemma_2 b : let op' a b := op b a in
  foldr op' b (o) perm(*shuffle!*) = Ret \o foldr op' b :> (_ -> M _).
Proof.
move=> op'.
apply functional_extensionality; elim => [|h t IH].
  by rewrite fcompE fmapE bindretf.
rewrite fcompE /= fmap_bind lemma_1.
transitivity (do x <- perm t; (Ret \o (fun x => op' h x) \o foldr op' b) x : M _).
  by [].
by rewrite -(@bind_fmap _ _ _ _ (foldr op' b)) -fcompE IH bindretf.
Qed.

End foldl_perm_deterministic.

Section corollary10.

Variable M : altCIMonad.
Variables (A B : Type) (b : B) (mul : B -> A -> B) (add : B -> B -> B).
Hypotheses (addA : associative add) (addC : commutative add).

Lemma lemma_6 (h : seq A -> B) (addb0 : right_id b add) : list_homo b add h <->
  foldr add b \o map h = h \o flatten.
Proof.
split => H.
  apply functional_extensionality => xss /=.
  elim: xss => [|s ss IH /=]; first by rewrite /= (proj1 H).
  by rewrite (proj2 H) IH.
split; [by move/(congr1 (fun x => x [::])) : H | move=> s1 s2].
rewrite (_ : _ ++ _ = flatten [:: s1; s2]); last by rewrite /= cats0.
by rewrite -(compE h) -H /= addb0.
Qed.

Lemma lemma_6_foldl (h : seq A -> B) (add0b : left_id b add) :
  list_homo b add h <->
  foldl add b \o map h = h \o flatten.
Proof.
split => H.
  apply functional_extensionality => xss /=.
  elim: xss => [|s ss IH]; first by rewrite /= (proj1 H).
  rewrite (proj2 H) -IH /=.
  (* TODO: lemma? bigop? *)
  generalize (h s) => b0.
  elim: ss b0 {IH} => [b0|u v IH b0] /=; first by rewrite addC.
  by rewrite -addA IH -addA IH.
split; [by move/(congr1 (fun x => x [::])) : H | move=> s1 s2].
rewrite (_ : _ ++ _ = flatten [:: s1; s2]); last by rewrite /= cats0.
by rewrite -(compE h) -H /= add0b.
Qed.

Corollary corollary_10 (add0b : left_id b add) :
  list_homo b add (foldl mul b) ->
  aggregate M b mul add = Ret \o foldl mul b \o flatten :> (_ -> M _).
Proof.
move/(proj1 (lemma_6_foldl _ add0b)) => H.
by rewrite aggregateE // -compA  -[in RHS]compA H.
Qed.

End corollary10.

Section deterministic_aggregate.

Variable M : altCIMonad.

Variables (A B : Type) (b : B) (mul : B -> A -> B) (add : B -> B -> B).

Local Open Scope mu_scope.

Lemma lemma_11_a s :
  (forall (x y w : B), add (add w x) y = add (add w y) x) ->
  aggregate _ b mul add = Ret \o foldl mul b \o flatten :> (_ -> M _) ->
  (foldl mul b \o flatten) s = (foldl add b \o (map (foldl mul b))) s.
Proof.
move=> Hadd H1; apply (@Ret_inj M).
move/(congr1 (fun x => x s)) : H1 => /= <-.
by rewrite /aggregate fcomp_def compA -fcomp_def (@lemma_34 M _ _ _ Hadd b).
Qed.

Lemma lemma_11_b s s' (m : M _) :
  aggregate _ b mul add = Ret \o foldl mul b \o flatten :> (_ -> M _) ->
  perm s = Ret s' [~] m ->
  (foldl mul b \o flatten) s = (foldl add b \o (map (foldl mul b))) s'.
Proof.
move=> H1 H2.
have /esym H : Ret ((foldl mul b \o flatten) s) =
    fmap (foldl add b \o map (foldl mul b)) (Ret s') [~]
    fmap (foldl add b \o map (foldl mul b)) m.
  move/(congr1 (fun x => x s)) : H1 => /= <-.
  by rewrite /aggregate perm_map -fcomp_comp fcompE H2 alt_fmapDl.
apply (@Ret_inj M).
case: (alt_Ret H) => <- _.
by rewrite -(compE (fmap _)) /= fmapE bindretf.
Qed.

Definition prop_In1 {T1 T2} (d : T2 -> T1) (P : T1 -> Prop) :=
  forall x, (exists x', x = d x') -> P x.

Definition prop_In11 {T1 T2} (d : T2 -> T1) (P : T1 -> T1 -> Prop) :=
  forall x y, (exists x', x = d x') -> (exists y', y = d y') -> P x y.

Definition prop_In111 {T1 T2} (d : T2 -> T1) (P : T1 -> T1 -> T1 -> Prop) :=
  forall x y z, (exists x', x = d x') -> (exists y', y = d y') -> (exists z', z = d z') -> P x y z.

Notation "{ 'In' d , P }" := (prop_In1 d P)
  (at level 0, format "{ 'In'  d ,  P }").

Notation "{ 'In2' d , P }" := (prop_In11 d P)
  (at level 0, format "{ 'In2'  d ,  P }").

Notation "{ 'In3' d , P }" := (prop_In111 d P)
  (at level 0, format "{ 'In3'  d ,  P }").

Lemma theorem12_a : (forall (x y w : B), add (add w x) y = add (add w y) x) ->
  aggregate M b mul add = Ret \o foldl mul b \o flatten ->
  {In foldl mul b, (fun y => add b y = y)}.
Proof.
move=> Hadd H y [s sy].
apply/esym.
rewrite {1}sy (_ : s = flatten [:: s]); last by rewrite /= cats0.
transitivity (((foldl mul b) \o flatten) [:: s]); first by [].
by rewrite lemma_11_a //= -sy.
Qed.

Lemma theorem12_b : (forall (x y w : B), add (add w x) y = add (add w y) x) ->
  aggregate M b mul add = Ret \o foldl mul b \o flatten ->
  {In foldl mul b, (fun y => add y b = y)}.
Proof.
move=> Hadd H y [s sy].
apply/esym.
rewrite {1}sy (_ : s = flatten [:: s; [::]]); last by rewrite /= cats0.
have [m Hm] : exists m, perm [:: s; [::]] = Ret [:: s; [::]] [~] m :> M _.
  eexists.
  rewrite /= bindretf insertE bindretf insertE /=; reflexivity.
move: (@lemma_11_b [:: s; [::]] _ _  H Hm) => /= ->.
rewrite -sy theorem12_a //; by exists s.
Qed.

(* netys2017 *)
Lemma theorem_13 :
  (forall x y w : B, add (add w x) y = add (add w y) x) ->
  aggregate M b mul add = Ret \o foldl mul b \o flatten ->
  list_homo b add (foldl mul b).
Proof.
move=> Hadd H; split; [by [] |move=> s1 s2].
rewrite (_ : s1 ++ s2 = flatten [:: s1; s2]); last by rewrite /= cats0.
transitivity (foldl add b (map (foldl mul b) [:: s1; s2])).
  transitivity ((foldl mul b \o flatten) [:: s1; s2]); first by [].
  by rewrite lemma_11_a.
rewrite /= theorem12_a //; by exists s1.
Qed.

Corollary corollary_14 :
  aggregate M b mul add = Ret \o foldl mul b \o flatten <->
  {In foldl mul b, (fun x => add b x = x)} /\
  {In foldl mul b, (fun x => add x b = x)} /\
  {In3 foldl mul b, (fun x y z => add x (add y z) = add (add x y) z)} /\
  {In2 foldl mul b, (fun x y => add x y = add y x)}
  /\ list_homo b add (foldl mul b).
Proof.
split => [H|[H1 [H2 [H3 [H4 H5]]]]].
  set h3 := ({In3 _, _}).
  have H3 : h3.
   rewrite {}/h3.
   admit.
  set h2 := ({In2 _, _}).
  have H2 : h2.
   rewrite {}/h2.
   admit.
  split.
  apply theorem12_a => //.
  admit.
  split.
  apply theorem12_b => //.
  admit.
  split => //.
  split => //.
  apply theorem_13 => //.
  admit.
apply corollary_10 => //.
Abort.
End deterministic_aggregate.
:
