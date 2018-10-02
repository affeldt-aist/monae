Require Import FunctionalExtensionality Coq.Program.Tactics ProofIrrelevance.
Require Import Coq.Logic.IndefiniteDescription.
Require Classical.
Require Import ssreflect ssrmatching ssrfun ssrbool.
From mathcomp Require Import eqtype ssrnat seq choice fintype tuple.
Require Import ZArith ssrZ.
Require Import monad state_monad.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*Lemma opze z e : nondetState_sub e -> op z e = do x <- e; op z (Ret x).
Proof.
move=> H.
rewrite SyntaxNondet.commute_nondetState // /op /opdot_queens /opdot.
bind_ext => st.
rewrite !bindA [in RHS]SyntaxNondet.commute_nondetState // bindA.
bind_ext; case.
bind_ext; case.
by rewrite_ fmap_ret.
Qed.

Lemma opze_foldr u {A} (v : A -> M (seq Z)) e : nondetState_sub e ->
  (foldr op (do x0 <- e; v x0) u) = do x0 <- e; (foldr op (v x0) u).
Proof.
elim: u v e => // h t IH v e He /=.
rewrite IH // {1}/op /opdot_queens /opdot.
transitivity (do st <- Get;
  (guard (queens_ok (queens_next st h)) >> Put (queens_next st h)) >>
  do x0 <- e; cons h ($) (foldr op (v x0) t)).
  bind_ext => st.
  bind_ext; case.
  by rewrite fmap_bind.
transitivity (do st <- Get;
  (guard (queens_ok (queens_next st h)) >> (do x0 <- e; Put (queens_next st h) >>
  cons h ($) foldr op (v x0) t))).
  bind_ext => st.
  rewrite bindA.
  bind_ext; case.
  by rewrite [in RHS]SyntaxNondet.commute_nondetState.
transitivity (do st <- Get;
  (do x0 <- e; guard (queens_ok (queens_next st h)) >>
  Put (queens_next st h) >> cons h ($) foldr op (v x0) t)).
  bind_ext => st.
  rewrite_ bindA.
  by rewrite [in RHS]SyntaxNondet.commute_nondetState.
by rewrite -SyntaxNondet.commute_nondetState.
Qed.

Lemma opze_op e u  (v : seq Z -> M _) b : nondetState_sub e ->
  op b (do x0 <- e; foldr op (v x0) u) =
  do x0 <- e; op b (foldr op (v x0) u).
Proof.
move=> He.
rewrite {1}/op /opdot_queens /opdot [in RHS]SyntaxNondet.commute_nondetState //.
bind_ext => st.
rewrite [in RHS]SyntaxNondet.commute_nondetState //.
bind_ext; case.
by rewrite fmap_bind.
Qed.*)

Module Stash.

(* tentative proof of lemma 5.4, not sure we got it right, anyway not used *)
Module Lemma54.
Section syntax_nondetmonad_specialized.
Variable A : Type.

Inductive nondetmonad : Type :=
| nRet : A -> nondetmonad
| nBind : nondetmonad -> (A -> nondetmonad) -> nondetmonad
| nFail : nondetmonad
| nAlt : nondetmonad -> nondetmonad -> nondetmonad.

Fixpoint denote {M : nondetMonad} (m : nondetmonad) : M A :=
  match m with
  | nRet a => Ret a
  | nBind m f => denote m >>= (fun x => denote (f x))
  | nFail => Fail
  | nAlt m1 m2 => denote m1 [~i] denote m2
  end.

Definition is_nondet {S} (N : nondetStateMonad S) (n : N A) : Type :=
  {m : nondetmonad | denote m = n}.

Lemma commute_nondetState S (M : nondetStateMonad S)
  (m : M A) B (n : M B) C (f : A -> B -> M C) :
  is_nondet m -> commute m n f.
Proof.
case => x.
elim: x m n f => /= [s m n f <- | n IH1 m IH2 m' n' f <- | m n f <-
  | n IH1 m IH2 m' n' f <-] .
- rewrite /commute bindretf.
  by rewrite_ bindretf.
- rewrite /commute !bindA.
  transitivity (do x <- denote n; do y <- n' : M _; do x0 <- denote (m x); f x0 y).
    bind_ext => s.
    by rewrite (IH2 s).
  rewrite IH1 //.
  by rewrite_ bindA.
- rewrite /commute.
  rewrite_ bindfailf.
  by rewrite bindfailf bindmfail.
- rewrite /commute alt_bindDl.
  rewrite_ alt_bindDl.
  rewrite alt_bindDr; congr (_ [~i] _).
  by rewrite IH1.
  by rewrite IH2.
Qed.
End syntax_nondetmonad_specialized.

Lemma opdot_queensP (M : nondetStateMonad (Z * seq Z * seq Z)%type) (x : Z) (m : M (seq Z)) :
  (* Assuming that state and non-determinism commute, and m >>= 0 = 0 *)
  is_nondet m ->
  opdot_queens x m = do x0 <- m; (opdot_queens x \o Ret) x0.
Proof.
case => y.
move: m.
induction y => m.
- rewrite /= => <-.
  by rewrite /opdot_queens /opdot /= bindretf.
- rewrite /= => <-.
  rewrite bindA.
  transitivity (do x0 <- denote y; opdot_queens x (denote (n x0) : M _)); last first.
    bind_ext => s.
    by rewrite (H s).
  rewrite /opdot_queens /opdot /= (@commute_nondetState _ _ M (denote y) _ Get); last first.
    by exists y.
  bind_ext => st.
  transitivity (guard (queens_ok (queens_next st x)) >>
    do x0 <- denote y;
    (Put (queens_next st x)) >> fmap (cons x) (denote (n x0)) : M _).
    rewrite !bindA.
    bind_ext; case.
    rewrite (@commute_nondetState _ _ M (denote y) _ (Put (queens_next st x))); last first.
      by exists y.
    bind_ext; case.
    rewrite fmap_bind.
    by bind_ext.
  rewrite guardsC; last exact: bindmfail.
  rewrite !bindA; bind_ext => s.
  rewrite !bindA guardsC; last exact: bindmfail.
  by rewrite !bindA; bind_ext.
- rewrite /= => <-.
  rewrite /opdot_queens /opdot bindfailf.
  transitivity (do st <- Get ; Fail : M (seq Z)).
    bind_ext => st.
    by rewrite fmap_fail bindmfail.
  by rewrite bindmfail.
- rewrite /= => <-.
  rewrite /opdot_queens /opdot commute_nondetState; last by exists (nAlt y1 y2).
  bind_ext => st.
  rewrite guardsC; last exact: bindmfail.
  rewrite !bindA commute_nondetState; last by exists (nAlt y1 y2).
  rewrite bindA.
  bind_ext; case.
  bind_ext; case.
  rewrite /fmap.
  by rewrite_ bindretf.
Qed.

End Lemma54.

(* tentative proof of theorem 4.2, not sure we got it right,
   it mimics the pencil-and-paper proof but seems too general
   to be used on the n-queens puzzle, we did without it anyway *)
(* actually a specialization of section 4.4 of mu2017,
   to a seeding function returning lists *)
Module Theorem42.

Local Open Scope mu_scope.

Definition qm {M : monad} {D} (q : pred D) : M D -> D -> Prop :=
  fun x x' => (x = Ret x') /\ q x'.
Definition seed {M : monad} {A B} (p : pred B) (f : B -> M (A * B)%type) : B -> B -> Prop :=
  fun x1 x2 => qm p (snd ($) (@rbind M B (A * B) f (Ret x1))) x2.
(* NB: we do not use this seed, we specialize it instead to the relation
   fun _ _ x1 x2 => size x1 < size x2 in theorem 4.2 *)

Section theorem42.
Variables (M : failMonad) (A B' : Type).
Let B := seq B'.
Variable (C : Type).
Variables (op : A -> M C -> M C) (p : pred B) (f : B -> M (A * B)%type).
Hypothesis Hseed : bassert_size f.

Notation unfoldM := (unfoldM (@well_founded_size _)).

Lemma base_case e y : p y -> (foldr op (Ret e) >=> unfoldM p f) y = Ret e.
Proof.
move=> py.
transitivity (foldr op (Ret e) =<< Ret [::]).
  by rewrite /kleisli /rbind bindretf /= join_fmap unfoldME // py bindretf.
by rewrite /rbind bindretf.
Qed.

Lemma inductive_case e y :
  (forall x m, op x m = do x0 <- m; (op x \o Ret) x0) ->
  ~~ p y ->
  (foldr op (Ret e) >=> unfoldM p f) y =
  do xz <- f y; op xz.1 ((foldr op (Ret e) >=> unfoldM p f) xz.2).
Proof.
move=> H1 py.
transitivity (unfoldM p f y >>= foldr op (Ret e)).
  by rewrite /kleisli /= join_fmap.
transitivity (f y >>= (fun xz => cons xz.1 ($) unfoldM p f xz.2) >>= foldr op (Ret e)).
  by rewrite unfoldME // (negbTE py).
transitivity (f y >>= (fun xz => unfoldM p f xz.2 >>= (fun xs => op xz.1 (foldr op (Ret e) xs)))).
  rewrite bindA.
  by rewrite_ bind_fmap.
transitivity (do xz <- f y; unfoldM p f xz.2 >>= (foldr op (Ret e) <=< (op xz.1 \o Ret))).
  bind_ext => ba.
  bind_ext => xs.
  set h := foldr _ _.
  transitivity (h xs >>= (op ba.1 \o Ret)).
    by rewrite H1.
  by rewrite /= /rkleisli /= /kleisli /= join_fmap.
transitivity (do xz <- f y; unfoldM p f xz.2 >>= foldr op (Ret e) >>= (op xz.1 \o Ret)).
  bind_ext => ba.
  by rewrite bind_kleisli !bindA.
transitivity (do xz <- f y; op xz.1 (unfoldM p f xz.2 >>= foldr op (Ret e))).
  bind_ext => ba.
   by rewrite H1.
bind_ext => ba.
by rewrite /kleisli /= join_fmap.
Qed.

Lemma theorem_42 : (forall x m, op x m = m >>= (op x \o Ret)) ->
  forall e, (foldr op (Ret e) >=> unfoldM p f) =1 hyloM op e p f _ (@well_founded_size _).
Proof.
move=> H1 e.
apply: (well_founded_induction (@well_founded_size _)) => y IH.
rewrite hyloME //.
case/boolP : (p y) => py.
  rewrite base_case //; exact: decr_size_select.
rewrite inductive_case // Hseed /bassert !bindA; bind_ext => -[b a] /=.
rewrite /assert /guard /=.
case: ifPn => ay; last by rewrite !bindfailf.
by rewrite bindskipf !bindretf /= IH.
Qed.

End theorem42.

End Theorem42.

(* tentative to complete section 5.2, abort *)
Module Section42.

Variable M : nondetStateMonad (Z * seq Z * seq Z).

Lemma queensBodyE : queensBody M =
  hyloM (@opdot_queens M) [::] (@nilp _) select seed_select (@well_founded_size _).
Proof.
rewrite /queensBody; apply functional_extensionality.
case => [|h t].
  rewrite /= permsE /= hyloME; last 2 first.
    by rewrite bindretf.
    exact: decr_size_select.
rewrite [h :: t]lock -Theorem42.theorem_42; last 2 first.
  exact: decr_size_select.
(*  move=> x m; apply: opdot_queensP.*) admit.
by rewrite /kleisli /= join_fmap perms_mu_perm.
Abort.

End Section42.

End Stash.
