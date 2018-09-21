Require Import FunctionalExtensionality Coq.Program.Tactics ProofIrrelevance.
Require Classical.
Require Import ssreflect ssrmatching ssrfun ssrbool.
From mathcomp Require Import eqtype ssrnat seq choice fintype tuple.
Require Import ZArith ssrZ.
Require Import monad state_monad.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section mu2017_wip.

Local Open Scope mu_scope.

Axiom bool_of_Prop : Prop -> bool.
Axiom bool_of_PropP : forall x, bool_of_Prop x = true -> x.

Section hyloM.
Variables (M : monad) (A B C : Type).
Variables (op : B -> M C -> M C) (e : C) (p : ssrbool.pred A) (f : A -> M (B * A)%type).
Variable seed : forall (p : ssrbool.pred A) (f : A -> M (B * A)%type), A -> A -> Prop.
Hypothesis H : well_founded (seed p f).

Local Obligation Tactic := idtac.
Definition hyloM' (y : A) (g : forall y', seed p f y' y -> M C) : M C :=
  if p y then Ret e else f y >>=
    (fun xz => match Bool.bool_dec (bool_of_Prop (seed p f xz.2 y)) true with
            | left H => op xz.1 (g xz.2 (bool_of_PropP H))
            | right H => Ret e
            end).

Definition hyloM := Fix H (fun _ => M _) hyloM'.

Lemma hyloME y : hyloM y = if p y then Ret e else f y >>= (fun xz =>
  if bool_of_Prop (seed p f xz.2 y) then op xz.1 (hyloM xz.2) else Ret e).
Proof.
rewrite /hyloM Fix_eq; last first.
  move => b g g' K; rewrite /hyloM'; case: ifPn => // pb.
  bind_ext => -[a' b'] /=.
  destruct Bool.bool_dec => //.
  congr op.
  by rewrite K.
rewrite /hyloM'; case: ifPn => // py; bind_ext => -[a' b'] /=.
destruct Bool.bool_dec; first by rewrite e0.
by move/negP/negbTE : n => ->.
Qed.

End hyloM.
Arguments hyloM {M} {A} {B} {C} _ _ _ _ _.

Definition qm {M : monad} {D : Type} (q : ssrbool.pred D) : M D -> D -> Prop :=
  fun x x' => (x = Ret x') /\ q x'.

Definition seed {M : monad} {A B : Type} (p : ssrbool.pred B) (f : B -> M (A * B)%type) : B -> B -> Prop :=
  (fun x1 x2 => (qm (negb \o p) \o snd (o) rbind f \o Ret) x2 x1).

Section theorem_42.
Variables (M : nondetMonad) (B' : Type).
Let B := seq B'.
Variable (A : Type).
Variable (C : Type).
Variables (op : A -> M C -> M C).
Variable p : ssrbool.pred B.
Variable f : B -> M (A * B)%type.

Hypothesis well_founded_seed : well_founded (seed p f).
Hypothesis decr_size_f : decr_size f.

Theorem theorem_42 : (forall x (m : M C), op x m = m >>= (op x \o Ret)) ->
  forall e : C, (foldr op (Ret e) >=> unfoldM p f) =1 hyloM op e p f _ well_founded_seed.
Proof.
move=> H1 e.
apply: (well_founded_induction well_founded_seed) => y IH.
rewrite hyloME.
case/boolP : (p y) => py.
  transitivity (foldr op (Ret e) =<< Ret [::]).
    by rewrite /kleisli /rbind bindretf /= join_fmap unfoldME py bindretf.
  by rewrite /rbind bindretf.
transitivity (unfoldM p f y >>= foldr op (Ret e)).
  by rewrite /kleisli /= join_fmap.
transitivity (f y >>= (fun xz => cons xz.1 ($) unfoldM p f xz.2) >>= foldr op (Ret e)).
  rewrite {1}unfoldME (negbTE py).
  rewrite !bindA.
  rewrite -(decr_size_f y).
  rewrite /bassert !bindA.
  bind_ext => -[b a].
  rewrite /assert /guard /=.
  case: ifPn => ay.
    by rewrite !bindretf /= ay.
  by rewrite !bindfailf.
transitivity (f y >>= (fun xz => unfoldM p f xz.2 >>= (fun xs => op xz.1 (foldr op (Ret e) xs)))).
  rewrite bindA.
  by rewrite_ bind_fmap.
transitivity (do xz <- f y; unfoldM p f xz.2 >>= (foldr op (Ret e) <=< (op xz.1 \o Ret))).
  bind_ext => ba.
  bind_ext => xs.
  set h := foldr op (Ret e).
  transitivity (h xs >>= (op ba.1 \o Ret)); first by rewrite H1.
  by rewrite /= /rkleisli /= /kleisli /= join_fmap.
transitivity (do xz <- f y; unfoldM p f xz.2 >>= foldr op (Ret e) >>= (op xz.1 \o Ret)).
  bind_ext => ba.
  by rewrite bind_kleisli !bindA.
transitivity (do xz <- f y; op xz.1 (unfoldM p f xz.2 >>= foldr op (Ret e))).
  bind_ext => ba.
  by rewrite H1.
transitivity (do xz <- f y; op xz.1 ((foldr op (Ret e) >=> unfoldM p f) xz.2)).
  bind_ext => ba.
  congr op.
  by rewrite /kleisli /= join_fmap.
bind_ext => -[b a] /=.
case: ifPn => Hseed.
  rewrite IH //.
  exact: bool_of_PropP.
Admitted.

End theorem_42.

Section section_52_contd.

Variable M : nondetStateMonad (Z * seq Z * seq Z).

Hypothesis well_founded_seed : well_founded (seed (@nilp _) (@select M Z)).

Lemma opdot_queensP (x : Z) (m : M (seq Z)) : opdot_queens x m = do x0 <- m; (opdot_queens x \o Ret) x0.
Proof.
rewrite {1}/opdot_queens.
rewrite {1}/opdot.
rewrite {1}/fmap.
transitivity (do st <- Get; (guard (queens_ok (queens_next st x)) >> (do x0 <- m; Put (queens_next st x) >> (Ret \o cons x) x0))).
  bind_ext => st.
  rewrite bindA.
  bind_ext; case.
  admit. (* state and non-determinism commute *)
transitivity (do st <- Get; (do x0 <- m; (guard (queens_ok (queens_next st x)) >> Put (queens_next st x) >> (Ret \o cons x) x0))).
  bind_ext => st.
  rewrite guardsC; last exact: bindmfail.
  rewrite bindA.
  bind_ext => b.
  rewrite !bindA.
  rewrite guardsC; last exact: bindmfail.
  by rewrite bindA.
transitivity ((do x0 <- m; do st <- Get; (guard (queens_ok (queens_next st x)) >> Put (queens_next st x) >> (Ret \o cons x) x0))).
  admit. (* state and non-determinism commute *)
bind_ext => b.
rewrite /opdot_queens.
rewrite /opdot /=.
bind_ext => st.
bind_ext; case.
rewrite /fmap /=.
by rewrite bindretf.
Admitted.

Lemma queensBodyE : queensBody M =
  hyloM (@opdot_queens M) [::] (@nilp _) select seed well_founded_seed.
Proof.
rewrite /queensBody.
apply functional_extensionality => xs.
case: xs => [|h t].
  by rewrite /= permsE /= hyloME /= bindretf.
rewrite [h :: t]lock -theorem_42; last 2 first.
  exact: decr_size_select.
  exact: opdot_queensP.
by rewrite /kleisli /= join_fmap perms_mu_perm.
Qed.

End section_52_contd.

End mu2017_wip.
