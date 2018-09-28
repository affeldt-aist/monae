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

(* definition 5.1, mu2017 *)
Definition commute {M : monad} A B (m : M A) (n : M B) C (f : A -> B -> M C) : Prop :=
  m >>= (fun x => n >>= (fun y => f x y)) = n >>= (fun y => m >>= (fun x => f x y)) :> M _.

Module SyntaxNondet.

Inductive t : Type -> Type :=
| ret : forall A, A -> t A
| bind : forall B A, t B -> (B -> t A) -> t A
| fail : forall A, t A
| alt : forall A, t A -> t A -> t A.

Fixpoint denote {M : nondetMonad} {A} (m : t A) : M A :=
  match m with
  | ret A a => Ret a
  | bind A B m f => denote m >>= (fun x => denote (f x))
  | fail A => Fail
  | alt A m1 m2 => denote m1 [~i] denote m2
  end.

Definition nondetState_sub {S} {N : nondetStateMonad S} B (n : N B) : Type :=
  {m : t B | denote m = n}.

(* theorem 5.2, mu2017 *)
Lemma commute_nondetState {S} {M : nondetStateMonad S} B (m : M B) {A} (n : M A) C (f : B -> A -> M C) :
  nondetState_sub m -> commute m n f.
Proof.
case => x.
elim: x m n f => [A0 a m n f <-| B0 n n0 H0 n1 H1 m n2 f <- |
  A0 m n f <- | A0 n0 H0 n1 H1 m n2 f <-].
- rewrite /commute bindretf.
  by rewrite_ bindretf.
- rewrite /commute /=.
  rewrite !bindA.
  transitivity (do x <- denote n0; do y <- n2 : M _; do x0 <- denote (n1 x); f x0 y).
    bind_ext => s.
    by rewrite (H1 s).
  rewrite H0 //.
  bind_ext => a.
  by rewrite bindA.
- rewrite /commute /= bindfailf.
  transitivity (do y <- n; Fail : M C); last first.
    bind_ext => a.
    by rewrite bindfailf.
  by rewrite bindmfail.
- rewrite /commute /= alt_bindDl.
  transitivity (do y <- n2; ((do x <- denote n0 ; f x y) [~i] do x <- denote n1; f x y)); last first.
    bind_ext => a.
    by rewrite alt_bindDl.
  by rewrite alt_bindDr H0 // H1.
Qed.

Module Exports.
Notation nondetSyntax := t.
Notation ndAlt := alt.
Notation ndRet := ret.
Notation ndBind := bind.
Notation ndFail := fail.
Notation nondetState_sub := nondetState_sub.
Notation ndDenote := denote.
End Exports.
End SyntaxNondet.
Export SyntaxNondet.Exports.

Lemma select_is_nondetState S {M : nondetStateMonad S} {A} :
  forall s, nondetState_sub (@select M A s).
Proof.
elim => [/= | u v [x /= <-]]; first by exists (@ndFail _).
by exists (ndAlt (ndRet (u, v)) (ndBind x (fun x => ndRet (x.1, u :: x.2)))).
Qed.

Lemma unfoldM_is_nondetState S (M : nondetStateMonad S) A B
  (f : seq B -> M (A * seq B)%type) :
  (forall s, nondetState_sub (f s)) -> bassert_size f ->
  forall s, nondetState_sub (unfoldM (@well_founded_size B) (@nilp _) f s).
Proof.
move=> Hf size_f s.
suff : exists m, ndDenote m = unfoldM (@well_founded_size B) (@nilp B) f s.
  by move/constructive_indefinite_description.
move: s; apply: (well_founded_induction (@well_founded_size _)) => s IH.
have {IH}IH : forall x, size x < size s ->
  { m | ndDenote m = unfoldM (@well_founded_size B) (@nilp B) f x}.
  move=> y ys; exact/constructive_indefinite_description/IH.
case: s IH => [|h t] IH.
  rewrite unfoldME //=; by exists (ndRet [::]).
rewrite unfoldME //=.
case: (Hf (h :: t)) => x Hx.
rewrite -Hx /fmap.
set g := fun y : seq B =>
           match Bool.bool_dec (size y < size (h :: t)) true with
           | left H => match IH _ H with exist x _ => x end
           | right _ => ndRet [::]
           end.
refine (ex_intro _ (ndBind x (fun x => (ndBind (g x.2) (@ndRet _ \o cons x.1 )))) _) => /=.
rewrite Hx size_f /bassert !bindA.
bind_ext => -[x1 x2].
rewrite /assert /guard /= ltnS.
case: ifPn => b1b2; last by rewrite !bindfailf.
rewrite !bindskipf !bindretf /= /g.
case: Bool.bool_dec => //= x2t.
by case: (IH x2) => // x0 <-.
Qed.

Module SyntaxNondet_test.
Section tmp.
Variable B : Type.

Inductive nondetmonad : Type :=
| nRet : B -> nondetmonad
| nBind : nondetmonad -> (B -> nondetmonad) -> nondetmonad
| nFail : nondetmonad
| nAlt : nondetmonad -> nondetmonad -> nondetmonad.

Fixpoint denote {M : nondetMonad} (m : nondetmonad) : M B :=
match m with
| nRet a => Ret a
| nBind m f => denote m >>= (fun x => denote (f x))
| nFail => Fail
| nAlt m1 m2 => denote m1 [~i] denote m2
end.

Definition is_nondet {S} (N : nondetStateMonad S) (n : N B) : Type :=
  {m : nondetmonad | denote m = n}.

Lemma commute_nondetState {S} {M : nondetStateMonad S} (m : M B) {A} (n : M A) C (f : B -> A -> M C) :
  is_nondet m -> commute m n f.
Proof.
case => x.
elim: x m n f => /= [s m n f| n IH1 m IH2 m' n' f <-| m n f <-| n IH1 m IH2 m' n' f <-] .
- move=> <-.
  rewrite /commute bindretf.
  by rewrite_ bindretf.
- rewrite /commute.
  rewrite !bindA.
  transitivity (do x <- denote n; do y <- n' : M _; do x0 <- denote (m x); f x0 y).
    bind_ext => s.
    by rewrite (IH2 s).
  rewrite IH1 //.
  by rewrite_ bindA.
- rewrite /commute.
  rewrite_ bindfailf.
  by rewrite bindfailf bindmfail.
- rewrite /commute.
  rewrite alt_bindDl.
  rewrite_ alt_bindDl.
  rewrite alt_bindDr.
  congr (_ [~i] _).
  rewrite IH1 //.
  rewrite IH2 //.
Qed.
End tmp.

Lemma opdot_queensP {M : nondetStateMonad (Z * seq Z * seq Z)%type} (x : Z) (m : M (seq Z)) :
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

End SyntaxNondet_test.

(* sections 4-5, part related to monadic hylo-fusion only *)
Section mu2017_hylo.

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

(* specialization of section 4.4 of mu2017, to a seeding function returning lists;
   too general to be used on the n-queens puzzle *)
Section theorem_42_wip.
Variables (M : failMonad) (A B' : Type).
Let B := seq B'.
Variable (C : Type).
Variables (op : A -> M C -> M C) (p : pred B) (f : B -> M (A * B)%type).
Hypothesis Hseed : bassert_size f.

Notation unfoldM := (unfoldM (@well_founded_size _)).

Lemma base_case_wip e y : p y -> (foldr op (Ret e) >=> unfoldM p f) y = Ret e.
Proof.
move=> py.
transitivity (foldr op (Ret e) =<< Ret [::]).
  by rewrite /kleisli /rbind bindretf /= join_fmap unfoldME // py bindretf.
by rewrite /rbind bindretf.
Qed.

Lemma inductive_case_wip e y :
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

Lemma theorem_42_wip : (forall x m, op x m = m >>= (op x \o Ret)) ->
  forall e, (foldr op (Ret e) >=> unfoldM p f) =1 hyloM op e p f _ (@well_founded_size _).
Proof.
move=> H1 e.
apply: (well_founded_induction (@well_founded_size _)) => y IH.
rewrite hyloME //.
case/boolP : (p y) => py.
  rewrite base_case_wip //; exact: decr_size_select.
rewrite inductive_case_wip // Hseed /bassert !bindA; bind_ext => -[b a] /=.
rewrite /assert /guard /=.
case: ifPn => ay; last by rewrite !bindfailf.
by rewrite bindskipf !bindretf /= IH.
Qed.

End theorem_42_wip.

Definition seed_select {M : nondetStateMonad (Z * seq Z * seq Z)%type} :=
  fun (p : pred (seq Z)) (f : seq Z -> M (Z * seq Z)%type)
  (a b : seq Z) => size a < size b.

Section section_52_contd_wip.
(* completes the derivation from section_52 modulo one axiom *)

Variable M : nondetStateMonad (Z * seq Z * seq Z).

Lemma queensBodyE_wip : queensBody M =
  hyloM (@opdot_queens M) [::] (@nilp _) select seed_select (@well_founded_size _).
Proof.
rewrite /queensBody; apply functional_extensionality.
case => [|h t].
  rewrite /= permsE /= hyloME; last 2 first.
    by rewrite bindretf.
    exact: decr_size_select.
rewrite [h :: t]lock -theorem_42_wip; last 2 first.
  exact: decr_size_select.
(*  move=> x m; apply: opdot_queensP.*) admit.
by rewrite /kleisli /= join_fmap perms_mu_perm.
Abort.

End section_52_contd_wip.

(* direct proof of theorem 4.2 *)
Section theorem_42.
Variables (M : nondetStateMonad (Z * seq Z * seq Z)%type).

Local Open Scope mu_scope.

Notation unfoldM := (unfoldM (@well_founded_size _)).

Let op := @opdot_queens M.
Let p := @nilp Z.

Lemma base_case y : p y -> (foldr op (Ret [::]) >=> unfoldM p select) y = Ret [::].
Proof.
move=> py.
transitivity (foldr op (Ret [::]) =<< Ret [::]).
  rewrite /kleisli /rbind bindretf /= join_fmap unfoldME; last exact: decr_size_select.
  by rewrite py bindretf.
by rewrite /rbind bindretf.
Qed.

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

Lemma theorem_42 :
  (foldr op (Ret [::]) >=> unfoldM p select) =1
  @hyloM _ _ _ _ op [::] p select seed_select (@well_founded_size _).
Proof.
apply: (well_founded_induction (@well_founded_size _)) => y IH.
rewrite hyloME; last exact: decr_size_select.
case/boolP : (p y) => py.
  by rewrite base_case.
rewrite /rkleisli /kleisli /= join_fmap.
rewrite unfoldME; last exact: decr_size_select.
rewrite (negbTE py) bindA.
rewrite(@decr_size_select _ _) /bassert !bindA; bind_ext => -[b a] /=.
rewrite /assert /guard /=.
case: ifPn => ay; last by rewrite !bindfailf.
rewrite bindskipf !bindretf /= -IH // bind_fmap /kleisli /= join_fmap.
suff : do x <- unfoldM p select a; op b (foldr op (Ret [::]) x) =
  op b (do x <- unfoldM p select a; foldr op (Ret [::]) x) by done.
rewrite {ay}.
move: a b.
apply: (well_founded_induction (@well_founded_size _)) => a IH' b.
destruct a as [|u v] => //.
  rewrite unfoldME /=; last exact: decr_size_select.
  by rewrite !bindretf /=.
rewrite unfoldME /=; last exact: decr_size_select.
rewrite !bindA.
transitivity (do x <- Ret (u, v) [~i] (do y_ys <- select v; Ret (y_ys.1, u :: y_ys.2));
  op b (do x0 <- cons x.1 ($) unfoldM p select x.2; foldr op (Ret [::]) x0)); last first.
  apply/esym.
  rewrite {1}/op /opdot_queens /opdot fmap_bind.
  transitivity (do st <- Get;
  (guard (queens_ok (queens_next st b)) >> do x <- Ret (u, v) [~i] (do y_ys <- select v; Ret (y_ys.1, u :: y_ys.2));
   (Put (queens_next st b)) >>
  ((cons b
    (o) (fun x : Z * seq Z => do x0 <- cons x.1 ($) unfoldM p select x.2; foldr op (Ret [::]) x0)) x))).
    bind_ext => st.
    rewrite !bindA.
    bind_ext; case.
    rewrite -SyntaxNondet.commute_nondetState //.
    case: (@select_is_nondetState _ M _ v) => x <-.
    by exists (ndAlt (ndRet (u, v)) (ndBind x (fun y => ndRet (y.1, u :: y.2)))).
  transitivity (do st <- Get;
  (do x <- Ret (u, v) [~i] (do y_ys <- select v; Ret (y_ys.1, u :: y_ys.2)) : M _;
  guard (queens_ok (queens_next st b)) >>
   Put (queens_next st b) >>
   (cons b
    (o) (fun x0 : Z * seq Z => do x1 <- cons x0.1 ($) unfoldM p select x0.2; foldr op (Ret [::]) x1))
     x)).
    bind_ext => st.
    rewrite -bindA guardsC; last exact: bindmfail.
    rewrite !bindA.
    bind_ext => x.
    rewrite !bindA.
    bind_ext; case.
    by rewrite bindretf.
  rewrite -SyntaxNondet.commute_nondetState //.
  case: (@select_is_nondetState _ M _ v) => x <-.
  by exists (ndAlt (ndRet (u, v)) (ndBind x (fun y => ndRet (y.1, u :: y.2)))).
bind_ext => x.
rewrite {1}/op /opdot_queens /opdot.
rewrite SyntaxNondet.commute_nondetState; last first.
  rewrite /fmap.
  case: (unfoldM_is_nondetState (@select_is_nondetState _ M Z) (@decr_size_select M _) x.2).
  move=> m <-.
  by exists (ndBind m (fun y => ndRet (x.1 :: y))).
rewrite {2}/op /opdot_queens /opdot.
bind_ext => st.
rewrite SyntaxNondet.commute_nondetState //; last first.
   case: (unfoldM_is_nondetState (@select_is_nondetState _ M Z) (@decr_size_select _ _) x.2).
   move=> m <-.
   by exists (ndBind m (fun y => ndRet (x.1 :: y))).
bind_ext; case.
rewrite !bind_fmap !fmap_bind.
by bind_ext.
Qed.

End theorem_42.

Section section_52_contd.

Variables (M : nondetStateMonad (Z * seq Z * seq Z)%type).

Local Open Scope mu_scope.

Lemma queensBodyE : queensBody M =
  hyloM (@opdot_queens M) [::] (@nilp _) select seed_select (@well_founded_size _).
Proof.
rewrite /queensBody; apply functional_extensionality.
case => [|h t].
  rewrite /= permsE /= hyloME; last 2 first.
    by rewrite bindretf.
    exact: decr_size_select.
rewrite [h :: t]lock -theorem_42.
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
rewrite {-1}[h :: t]lock /= decr_size_select /bassert 2!bindA.
bind_ext => -[x ys] /=.
rewrite /assert /guard /=.
case: ifPn => ysht; last by rewrite !bindfailf.
rewrite bindskipf !bindretf /opdot_queens /opdot.
bind_ext => st.
rewrite !bindA; bind_ext; case.
bind_ext; case => /=.
by rewrite queensBodyE.
Qed.

End section_52_contd.

End mu2017_hylo.
