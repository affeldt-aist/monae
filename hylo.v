Require Import FunctionalExtensionality Coq.Program.Tactics ProofIrrelevance.
Require Classical.
Require Import ssreflect ssrmatching ssrfun ssrbool.
From mathcomp Require Import eqtype ssrnat seq choice fintype tuple.
Require Import ZArith ssrZ.
Require Import monad state_monad.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* sections 4-5, part related to monadic hylo-fusion only *)
Section mu2017_wip.

Local Open Scope mu_scope.

(* from section 4.4 of mu2017 *)
Section hyloM.
Variables (M : failMonad) (A B C : Type).
Variables (op : A -> M C -> M C) (e : C) (p : pred B) (f : B -> M (A * B)%type).
Variable seed : forall (p : pred B) (f : B -> M (A * B)%type), B -> B -> bool.

Definition hyloM' (y : B) (g : forall y', seed p f y' y -> M C) : M C :=
  if p y then Ret e else f y >>=
    (fun xz => match Bool.bool_dec (seed p f xz.2 y) true with
            | left H => op xz.1 (g xz.2 H)
            | right H => Ret e
            end).

Hypothesis well_founded_seed : well_founded (seed p f).

Definition hyloM := Fix well_founded_seed (fun _ => M _) hyloM'.

Hypothesis Hdecr_seed : bassert_hylo f p seed.

Lemma hyloME y : hyloM y = if p y then
                             Ret e
                           else
                             f y >>= (fun xz => op xz.1 (hyloM xz.2)).
Proof.
rewrite /hyloM Fix_eq; last first.
  move => b g g' K; rewrite /hyloM'; case: ifPn => // pb.
  bind_ext => -[a' b'] /=.
  destruct Bool.bool_dec => //.
  by rewrite K.
rewrite {1}/hyloM'; case: ifPn => // py.
rewrite Hdecr_seed /bassert !bindA /assert /guard; bind_ext => -[b' a'].
case: ifPn => Hseed; last by rewrite !bindfailf.
by rewrite !bindskipf !bindretf Hseed.
Qed.

End hyloM.
Arguments hyloM {M} {A} {B} {C} _ _ _ _ _.

Definition qm {M : monad} {D} (q : pred D) : M D -> D -> Prop :=
  fun x x' => (x = Ret x') /\ q x'.
Definition seed {M : monad} {A B} (p : pred B) (f : B -> M (A * B)%type) : B -> B -> Prop :=
  fun x1 x2 => qm p (snd ($) (@rbind M B (A * B) f (Ret x1))) x2.
(* NB: we do not use this seed, we specialize it instead to the relation
   fun _ _ x1 x2 => size x1 < size x2 in theorem 4.2 *)

(* specialization of section 4.4 of mu2017,
   to a seeding function returning lists *)
Section theorem_42.
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
  set h := foldr op (Ret e).
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

Theorem theorem_42 : (forall x m, op x m = m >>= (op x \o Ret)) ->
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

End theorem_42.

Definition seed_select {M : nondetStateMonad (Z * seq Z * seq Z)%type} :=
  fun (p : pred (seq Z)) (f : seq Z -> M (Z * seq Z)%type)
  (a b : seq Z) => size a < size b.

Section section_52_contd.
(* completes the derivation from section_52 modulo one axiom *)

Variable M : nondetStateMonad (Z * seq Z * seq Z).

(*Hypothesis alt_bindDr (* law (10) *) : Laws.bind_right_distributive (@Bind M) [~p].*)
(* NB: law (11) bindmfail holds from nondetStateMonad *)
(* see incipit of section 3 *)

Lemma opdot_queensP (x : Z) (m : M (seq Z)) :
  (* Assuming that state and non-determinism commute, and m >>= 0 = 0 *)
  opdot_queens x m = do x0 <- m; (opdot_queens x \o Ret) x0.
Proof.
rewrite /opdot_queens /opdot /=.
Admitted.

Lemma queensBodyE : queensBody M =
  hyloM (@opdot_queens M) [::] (@nilp _) select seed_select (@well_founded_size _).
Proof.
rewrite /queensBody; apply functional_extensionality.
case => [|h t].
  rewrite /= permsE /= hyloME; last 2 first.
    by rewrite bindretf.
    exact: decr_size_select.
rewrite [h :: t]lock -theorem_42; last 2 first.
  exact: decr_size_select.
  move=> x m; apply: opdot_queensP.
by rewrite /kleisli /= join_fmap perms_mu_perm.
Qed.

Lemma queensBodyE' xs : queensBody M xs = if xs is [::] then Ret [::] else
  select xs >>= (fun xys =>
  Get >>= (fun st => guard (queens_ok (queens_next st xys.1)) >>
  Put (queens_next st xys.1) >> (cons xys.1 ($) queensBody M xys.2))).
Proof.
case: xs => [|h t].
  rewrite queensBodyE // hyloME //; exact: decr_size_select.
rewrite {1}queensBodyE hyloME; last exact: decr_size_select.
rewrite {-1}[h :: t]lock /=.
rewrite decr_size_select /bassert 2!bindA.
bind_ext => -[x ys] /=.
rewrite /assert /guard /=.
case: ifPn => ysht.
  rewrite bindskipf !bindretf.
  rewrite /opdot_queens /opdot.
  bind_ext => st.
  rewrite !bindA; bind_ext; case.
  bind_ext; case => /=.
  by rewrite queensBodyE.
by rewrite !bindfailf.
Qed.

End section_52_contd.

End mu2017_wip.
