Ltac typeof X := type of X.
Require Import FunctionalExtensionality Coq.Program.Tactics ProofIrrelevance.
Require Classical.
Require Import ssreflect ssrmatching ssrfun ssrbool.
From mathcomp Require Import eqtype ssrnat seq path div choice fintype tuple.
From mathcomp Require Import finfun bigop.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Contents:
- generic Haskell-like functions and notations
- Module Laws.
    definition of algebraic laws to be used with monads
- Module Monad.
    definition of standard notations
- Section fmap_and_join.
- Section rep.
    simple effect of counting
- Module MonadFail.
    definition of guard
- Module MonadAlt.
    non-deterministic choice
  Section subsequences_of_a_list.
  Section permutation_and_insertion.
    examples of non-deterministic programs
- Module MonadAltCI.
  Section spark_aggregation.
    example
- Module MonadNondet
  Section permutations.
    example
- Module MonadExcept.
    example of the fast product
*)

Reserved Notation "A `2" (format "A `2", at level 3).
Reserved Notation "f `^2" (format "f `^2", at level 3).
Reserved Notation "l \\ p" (at level 50).
Reserved Notation "m >>= f" (at level 50).
Reserved Notation "f =<< m" (at level 50).
Reserved Notation "'do' x <- m ; e"
  (at level 60, x ident, m at level 200, e at level 60).
Reserved Notation "'do' x : T <- m ; e"
  (at level 60, x ident, m at level 200, e at level 60).
Reserved Notation "m >=> n" (at level 50).
Reserved Notation "n <=< m" (at level 50).
Reserved Notation "x '[~i]' y" (at level 50).
Reserved Notation "'[~p]'".
Reserved Notation "f ($) m" (at level 11).
Reserved Notation "f (o) g" (at level 11).

Definition Square (A : Type) := (A * A)%type.
Notation "A `2" := (Square A).
Definition square (A B : Type) (f : A -> B) := fun x => (f x.1, f x.2).
Notation "f `^2" := (square f).
Notation "l \\ p" := ([seq x <- l | x \notin p]).

(* some Haskell-like functions *)
Definition foldr1 (A : Type) (def : A) (f : A -> A -> A) (s : seq A) :=
  match s with
    | [::] => def
    | [:: h] => def
    | h :: h' :: t => foldr f h [:: h' & t]
  end.

Definition cp {A B} (x : seq A) (y : seq B) := [seq (x', y') | x' <- x, y' <- y].

Lemma cp1 {A B} (x : A) (y : seq B) : cp [:: x] y = map (fun y' => (x, y')) y.
Proof. elim: y => // h t /= <-; by rewrite cats0. Qed.

Section fold.
Variables (T R : Type) (f : T -> R -> R) (r : R).

Section universal.
Variable (g : seq T -> R).
Hypothesis H1 : g nil = r.
Hypothesis H2 : forall h t, g (h :: t) = f h (g t).
Lemma foldr_universal : g = foldr f r.
Proof.
apply functional_extensionality; elim => // h t ih /=; by rewrite H2 ih.
Qed.
Lemma foldr_universal_ext x : g x = foldr f r x.
Proof. by rewrite -(foldr_universal). Qed.
End universal.

Section fusion_law.
Variables (U : Type) (h : U -> R) (w : U) (g : T -> U -> U).
Hypothesis H1 : h w = r.
Hypothesis H2 : forall x y, h (g x y) = f x (h y).
Lemma foldr_fusion : h \o foldr g w = foldr f r.
Proof.
apply functional_extensionality; elim => // a b /= ih; by rewrite H2 ih.
Qed.
Lemma foldr_fusion_ext x : (h \o foldr g w) x = foldr f r x.
Proof. by rewrite -foldr_fusion. Qed.
End fusion_law.

End fold.

Definition uncurry {A B C} (f : A -> B -> C) : ((A * B)%type -> C) :=
  fun x => let: (x1, x2) := x in f x1 x2.

Definition ucat {A} := uncurry (@cat A).

Definition uaddn := uncurry addn.

Definition curry {A B C} (f : (A * B)%type -> C) : (A -> B -> C) :=
  fun a b => f (a, b).

Lemma lift_if A B C (f : A -> B -> C) b m1 m2 :
  f (if b then m1 else m2) = if b then f m1 else f m2.
Proof. by case: ifP. Qed.

Lemma if_ext A B (f g : A -> B) (x : A) b :
  (if b then f else g) x = if b then f x else g x.
Proof. by case: ifP. Qed.

Definition const A B (b : B) := fun _ : A => b.

Definition wrap {A} (a : A) := [:: a].

Lemma compA {A B C D} (f : C -> D) (g : B -> C) (h : A -> B) : f \o (g \o h) = (f \o g) \o h.
Proof. by []. Qed.

Fixpoint scanl A B (op : B -> A -> B) (b : B) (s : seq A) : seq B :=
  if s isn't x :: xs then [::] else (op b x) :: scanl op (op b x) xs.

Module Laws.
Section laws.
Variables (M : Type -> Type).

Variable b : forall A B, M A -> (A -> M B) -> M B.

Local Notation "m >>= f" := (b m f).

Definition associative := forall A B C (m : M A) (f : A -> M B) (g : B -> M C),
  (m >>= f) >>= g = m >>= (fun x => (f x >>= g)).

Definition bind_right_distributive (add : forall B, M B -> M B -> M B) :=
  forall A B (m : M A) (k1 k2 : A -> M B),
    m >>= (fun x => add _ (k1 x) (k2 x)) = add _ (m >>= k1) (m >>= k2).

Definition bind_left_distributive (add : forall B, M B -> M B -> M B) :=
  forall A B (m1 m2 : M A) (k : A -> M B),
    (add _ m1 m2) >>= k = add _ (m1 >>= k) (m2 >>= k).

Definition right_zero (f : forall A, M A) :=
  forall A B (g : M B), g >>= (fun _ => f A) = f A.

Definition left_zero (f : forall A, M A) := forall A B g, f A >>= g = f B.

Definition left_neutral (r : forall A, A -> M A) :=
  forall A B (x : A) (f : A -> M B), r _ x >>= f = f x.

Definition right_neutral (r : forall A, A -> M A) :=
  forall A (m : M A), m >>= r _ = m.

Definition left_id (r : forall A, M A) (add : forall B, M B -> M B -> M B) :=
  forall A (m : M A), add _ (r _) m = m.

Definition right_id (r : forall A, M A) (add : forall B, M B -> M B -> M B) :=
  forall A (m : M A), add _ m (r _) = m.

End laws.
End Laws.

(* map laws of a functor *)
Module Map_laws.
Section map_laws.
Variable M : Type -> Type.
Variable f : forall A B, (A -> B) -> M A -> M B.

(* map identity *)
Definition id := forall A, @f A _ id = id.

(* map composition *)
Definition comp := forall A B C (g : B -> C) (h : A -> B),
  f (g \o h) = f g \o f h.

End map_laws.
End Map_laws.

Module Monad.
Record class_of (m : Type -> Type) : Type := Class {
  op_ret : forall A, A -> m A ;
  op_bind : forall A B, m A -> (A -> m B) -> m B ;
  _ : Laws.left_neutral op_bind op_ret ;
  _ : Laws.right_neutral op_bind op_ret ;
  _ : Laws.associative op_bind }.
Record t : Type := Pack { m : Type -> Type ; class : class_of m }.
Definition ret (M : t) A : A -> m M A :=
  let: Pack _ (Class x _ _ _ _) := M in x A.
Arguments ret {M A} : simpl never.
Definition bind (M : t) A B : m M A -> (A -> m M B) -> m M B :=
  let: Pack _ (Class _ x _ _ _) := M in x A B.
Arguments bind {M A B} : simpl never.
Module Exports.
Notation "m >>= f" := (bind m f).
Notation Bind := bind.
Notation Ret := ret.
Notation monad := t.
Coercion m : monad >-> Funclass.
End Exports.
End Monad.
Export Monad.Exports.

Section monad_lemmas.
Variable M : monad.
Lemma bindretf : Laws.left_neutral (@Bind M) (@Ret _).
Proof. by case: M => m []. Qed.
Lemma bindmret : Laws.right_neutral (@Bind M) (@Ret _).
Proof. by case: M => m []. Qed.
Lemma bindA : Laws.associative (@Bind M).
Proof. by case: M => m []. Qed.
End monad_lemmas.

Notation "'do' x <- m ; e" := (m >>= (fun x => e)).
Notation "'do' x : T <- m ; e" := (m >>= (fun x : T => e)) (only parsing).
Notation "m >> f" := (m >>= fun _ => f) (at level 50).
Definition skip M := @Ret M _ tt.
Arguments skip {M} : simpl never.

Ltac bind_ext :=
  let congr_ext m := ltac:(congr (Monad.bind m); apply functional_extensionality) in
  match goal with
    | |- @Monad.bind _ _ _ ?m ?f1 = @Monad.bind _ _ _ ?m ?f2 =>
      congr_ext m
    | |- @Monad.bind _ _ _ ?m1 ?f1 = @Monad.bind _ _ _ ?m2 ?f2 =>
      first[ simpl m1; congr_ext m1 | simpl m2; congr_ext m2 ]
  end.

(* experimental *)
Tactic Notation "With" tactic(tac) "Open" ssrpatternarg(pat) :=
  ssrpattern pat;
  let f := fresh "f" in
  intro f;
  let g := fresh "g" in
  let typ := typeof f in
  let x := fresh "x" in
  evar (g : typ);
  rewrite (_ : f = g);
  [rewrite {}/f {}/g|
   apply functional_extensionality => x; rewrite {}/g {}/f; tac]; last first.

Tactic Notation "Open" ssrpatternarg(pat) :=
  With (idtac) Open pat.

Tactic Notation "Inf" tactic(tac) :=
  (With (tac; reflexivity) Open (X in @Monad.bind _ _ _ _ X = _ )) ||
  (With (tac; reflexivity) Open (X in _ = @Monad.bind _ _ _ _ X)).

Tactic Notation "rewrite_" constr(lem) :=
  (With (rewrite lem; reflexivity) Open (X in @Monad.bind _ _ _ _ X = _ )) ||
  (With (rewrite lem; reflexivity) Open (X in _ = @Monad.bind _ _ _ _ X)).

Lemma bindmskip (M : monad) (m : M unit) : m >> skip = m.
Proof. by rewrite -[RHS]bindmret; bind_ext; by case. Qed.

Lemma bindskipf (M : monad) A (m : M A) : skip >> m = m.
Proof. exact: bindretf. Qed.

Fixpoint sequence (M : monad) A (s : seq (M A)) : M (seq A) :=
  if s isn't h :: t then Ret [::] else
  do v <- h; do vs <- sequence t; Ret (v :: vs).

Lemma sequence_nil (M : monad) A : sequence [::] = Ret [::] :> M (seq A).
Proof. by []. Qed.

Lemma sequence_cons (M : monad) A h (t : seq (M A)) :
  sequence (h :: t) = do x <- h ; do vs <- sequence t ; Ret (x :: vs).
Proof. by []. Qed.

Section fmap_and_join.

Variable M : monad.

(* monadic counterpart of function application: applies a pure function to a monad *)
(* aka liftM in gibbons2011icfp, notation ($) in mu2017 *)
Definition fmap A B (f : A -> B) (m : M _) := m >>= (Ret \o f).
Local Notation "f ($) m" := (fmap f m).
Arguments fmap : simpl never.

Lemma fmap_id : Map_laws.id fmap.
Proof.
move=> A; apply functional_extensionality => m; by rewrite /fmap bindmret.
Qed.

Lemma fmap_o : Map_laws.comp fmap.
Proof.
move=> A B C g h; apply functional_extensionality => m.
by rewrite /fmap /= bindA; rewrite_ bindretf.
Qed.

Lemma fmap_ret A B (f : A -> B) a : f ($) Ret a = (Ret \o f) a.
Proof. by rewrite /fmap bindretf. Qed.

Lemma bind_fmap A B C (f : A -> B) (m : M A) (g : B -> M C) :
  f ($) m >>= g = m >>= (g \o f).
Proof. by rewrite bindA; rewrite_ bindretf. Qed.

Lemma fmap_if A B (f : A -> B) b (m : M A) a :
  fmap f (if b then m else Ret a) = if b then fmap f m else Ret (f a).
Proof. case: ifPn => Hb //; by rewrite /fmap /= bindretf. Qed.

(* monadic counterpart of function composition:
   composes a pure function after a monadic function *)
Definition fcomp A B C (f : A -> B) (g : C -> M A) := fmap f \o g.
Arguments fcomp : simpl never.
Local Notation "f (o) g" := (fcomp f g).

Lemma fcomp_ext A B C (f : A -> B) (g : C -> M A) c :
  (f (o) g) c = f ($) g c.
Proof. by []. Qed.

Lemma fmap_comp A B C (f : A -> B) (g : C -> A) (m : M C) :
  (f \o g) ($) m = f ($) (g ($) m).
Proof. by rewrite /fmap /fmap bindA; rewrite_ bindretf. Qed.

Lemma fcomp_comp A B C D (f : A -> B) (g : C -> A) (m : D -> M C) :
  (f \o g) (o) m = f (o) (g (o) m).
Proof. by rewrite /fcomp /= compA fmap_o. Qed.

Lemma fmap_bind A B C (f : A -> B) m (g : C -> M A) :
  f ($) (m >>= g) = m >>= (f (o) g).
Proof. by rewrite /fmap /= bindA. Qed.

Lemma skip_fmap A B (f : A -> B) (mb : M B) ma :
  mb >> (f ($) ma) = f ($) (mb >> ma).
Proof. by rewrite fmap_bind. Qed.

Definition join A (pp : M (M A)) := pp >>= id.
Arguments join {A} : simpl never.

Lemma join_fmap A B (f : A -> M B) m : join (fmap f m) = m >>= f.
Proof. by rewrite /join /fmap bindA; rewrite_ bindretf. Qed.

Lemma join_ret A : join \o Ret = @id (M A). (* left unit *)
Proof. apply functional_extensionality => ? /=; by rewrite /join bindretf. Qed.

Lemma join_fmap_ret A : join \o fmap Ret = @id (M A). (* right unit *)
Proof.
apply functional_extensionality => mx /=; by rewrite join_fmap bindmret.
Qed.

(* associativity *)
Lemma join_fmap_join A : join \o fmap join = join \o join :> (M (M (M A)) -> M A).
Proof.
apply functional_extensionality => mx /=; by rewrite join_fmap /join bindA.
Qed.

(* joint commutes with fmap *)
Lemma join_naturality A B (f : A -> B) :
  fmap f \o join = join \o fmap (fmap f) :> (M (M A) -> M B).
Proof.
apply functional_extensionality => mma /=; by rewrite join_fmap /fmap -bindA.
Qed.

Definition kleisli A B C (m : B -> M C) (n : A -> M B) : A -> M C :=
  join \o fmap m \o n.
Local Notation "m >=> n" := (kleisli m n).

Lemma fcomp_kleisli A B C D (f : A -> B) (g : C -> M A) (h : D -> M C) :
  f (o) (g >=> h) = (f (o) g) >=> h.
Proof. by rewrite /kleisli /fcomp /= 2!compA join_naturality fmap_o compA. Qed.

Lemma kleisli_fcomp A B C (f : A -> M B) (g : B -> A) (h : C -> M B) :
  ((f \o g) >=> h) = f >=> (g (o) h).
Proof. by rewrite /kleisli /fcomp fmap_o 2!compA. Qed.
Local Notation "m >=> n" := (kleisli m n).

Lemma bind_kleisli A B C m (f : B -> M C) (g : A -> M B) :
  m >>= (f >=> g) = (m >>= g) >>= f.
Proof. by rewrite bindA; bind_ext => a; rewrite /kleisli /= join_fmap. Qed.

Definition rbind A B (f : A -> M B) (m : M A) : M B := m >>= f.
Local Notation "f =<< m" := (rbind f m).

Definition rkleisli A B C (f : A -> M B) (g : B -> M C) : A -> M C := g >=> f.
Local Notation "n <=< m" := (rkleisli n m).

End fmap_and_join.
Notation "f ($) m" := (fmap f m) : mu_scope.
Arguments fmap : simpl never.
Notation "f (o) g" := (fcomp f g) : mu_scope.
Arguments fcomp : simpl never.
Arguments join {M} {A} : simpl never.
Notation "m >=> n" := (kleisli m n).
Notation "f =<< m" := (rbind f m) : mu_scope.
Notation "n <=< m" := (rkleisli n m) : mu_scope.

Definition pair {M : monad} {A} (xy : (M A * M A)%type) : M (A * A)%type :=
  let (mx, my) := xy in
  mx >>= (fun x => my >>= fun y => Ret (x, y)).

Lemma naturality_pair (M : monad) A B (f : A -> B) (g : A -> M A):
  fmap (f`^2) \o (pair \o g`^2) = pair \o (fmap f \o g)`^2.
Proof.
apply functional_extensionality => -[a0 a1] /=.
rewrite fmap_bind bind_fmap; bind_ext => a2 /=.
rewrite fcomp_ext fmap_bind bind_fmap; bind_ext => a3 /=.
by rewrite fcomp_ext fmap_ret.
Qed.

Section rep.

Variable M : monad.

Fixpoint rep (n : nat) (mx : M unit) : M unit :=
  if n is n.+1 then mx >> rep n mx else skip.

Lemma repS mx n : rep n.+1 mx = rep n mx >> mx.
Proof.
elim: n => /= [|n IH]; first by rewrite bindmskip bindskipf.
by rewrite bindA IH.
Qed.

Lemma rep1 mx : rep 1 mx = mx. Proof. by rewrite repS /= bindskipf. Qed.

Lemma rep_addn m n mx : rep (m + n) mx = rep m mx >> rep n mx.
Proof.
elim: m n => [|m IH /=] n; by
  [rewrite bindskipf add0n | rewrite -addnE IH bindA].
Qed.

End rep.

Section MonadCount.

Variable M : monad.
Variable tick : M unit.

Fixpoint hanoi n : M unit :=
  if n is n.+1 then hanoi n >> tick >> hanoi n else skip.

Lemma hanoi_rep n : hanoi n = rep (2 ^ n).-1 tick.
Proof.
elim: n => // n IH /=.
rewrite IH -repS prednK ?expn_gt0 // -rep_addn.
by rewrite -subn1 addnBA ?expn_gt0 // addnn -muln2 -expnSr subn1.
Qed.

End MonadCount.

Module MonadFail.
Record mixin_of (M : monad) : Type := Mixin {
  op_fail : forall A, M A ;
  (* exceptions are left-zeros of sequential composition *)
  _ : Laws.left_zero (@Bind M) op_fail (* fail A >>= f = fail B *)
}.
Record class_of (m : Type -> Type) := Class {
  base : Monad.class_of m ; mixin : mixin_of (Monad.Pack base) }.
Structure t := Pack { m : Type -> Type ; class : class_of m }.
Definition fail (M : t) : forall A, m M A :=
  let: Pack _ (Class _ (Mixin x _)) := M return forall A, m M A in x.
Arguments fail {M} {A} : simpl never.
Definition baseType (M : t) := Monad.Pack (base (class M)).
Module Exports.
Notation Fail := fail.
Notation failMonad := t.
Coercion baseType : failMonad >-> monad.
Canonical baseType.
End Exports.
End MonadFail.
Export MonadFail.Exports.

Section fail_lemmas.
Variable (M : failMonad).
Lemma bindfailf : Laws.left_zero (@Bind M) (@Fail _).
Proof. by case : M => m [? []]. Qed.
End fail_lemmas.

Lemma fmap_fail {A B} (M : failMonad) (f : A -> B) : fmap f Fail = Fail :> M _.
Proof. by rewrite /fmap bindfailf. Qed.

Section guard_assert.

Variable M : failMonad.

Definition guard (b : bool) : M unit := if b then skip else Fail.

(* guard distributes over conjunction *)
Lemma guard_and a b : guard (a && b) = guard a >> guard b.
Proof. move: a b => -[b|b] /=; by [rewrite bindskipf| rewrite bindfailf]. Qed.

Definition assert {A} (p : pred A) (a : A) : M A :=
  guard (p a) >> Ret a.

Definition bassert {A} (p : pred A) (m : M A) : M A := m >>= assert p.

(* follows from guards commuting with anything *)
Lemma commutativity_of_assertions A q :
  join \o fmap (bassert q) = bassert q \o join :> (_ -> M A).
Proof.
apply functional_extensionality => x.
by rewrite [fmap]lock [join]lock /= -!lock join_fmap /join /bassert bindA.
Qed.

(* guards commute with anything *)
Lemma guardsC (HM : Laws.right_zero (@Bind M) (@Fail _)) b B (m : M B) :
  (guard b >> m) = (m >>= fun x => guard b >> Ret x).
Proof.
rewrite /guard; case: ifPn => Hb.
  rewrite bindskipf.
  rewrite_ bindskipf.
  by rewrite bindmret.
rewrite_ bindfailf.
by rewrite bindfailf HM.
Qed.

End guard_assert.
Arguments assert {M} {A}.
Arguments guard {M}.

Lemma well_founded_size A : well_founded (fun x y : seq A => size x < size y).
Proof. by apply: (@Wf_nat.well_founded_lt_compat _ size) => ? ? /ltP. Qed.

Definition bassert_hylo {M : failMonad} A B
  (f : B -> M (A * B)%type) (p : pred B) (r : forall p f, B -> B -> bool) :=
  forall b, f b = bassert (fun z => r p f z.2 b) (f b).

Definition bassert_size {M : failMonad} A B
  (f : seq B -> M (A * seq B)%type) :=
  @bassert_hylo M _ _ f predT (fun _ _ x y => size x < size y).

(* from section 4.3 of mu2017: terminating unfold *)
Section unfoldM.

Local Open Scope mu_scope.

Section unfoldM_monad.
Variables (M : monad) (A B : Type).
Variable (r : B -> B -> bool).
Hypothesis wfr : well_founded r.
Variables (p : pred B) (f : B -> M (A * B)%type).

Definition unfoldM' (y : B) (g : forall y' : B, r y' y -> M (seq A)) : M (seq A) :=
  if p y then Ret [::] else f y >>=
    (fun xz => match Bool.bool_dec (r xz.2 y) true with
            | left H => cons xz.1 ($) g xz.2 H
            | right H => Ret [::]
            end).
(* superfluous match to define the "recursive" call,
   to be removed by unfoldME under hypo. *)

Definition unfoldM := Fix wfr (fun _ => _ _) unfoldM'.

End unfoldM_monad.

Section unfoldM_failMonad.
Variables (M : failMonad) (A B' : Type).
Let B := seq B'.
Notation unfoldM := (@unfoldM M A _ _ (@well_founded_size B')).
Variables (p : pred B) (f : B -> M (A * B)%type).

Hypothesis decr_size : bassert_size f.

Lemma unfoldME y : unfoldM p f y =
  if p y then Ret [::]
  else f y >>= (fun xz => cons xz.1 ($) unfoldM p f xz.2).
Proof.
rewrite /unfoldM Fix_eq; last first.
  move => b g g' H; rewrite /unfoldM'; case: ifPn => // pb.
  bind_ext => -[a' b'] /=.
  destruct Bool.bool_dec => //; by rewrite H.
rewrite /unfoldM'; case: ifPn => // py.
rewrite decr_size /bassert 2!bindA; bind_ext => -[a' b'].
rewrite /assert /guard /=; case: ifPn => b'y; last by rewrite !bindfailf.
by rewrite bindskipf 2!bindretf /= b'y.
Qed.

End unfoldM_failMonad.

End unfoldM.
Arguments unfoldM : simpl never.

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

Module MonadAlt.
Record mixin_of (M : monad) : Type := Mixin {
  op_alt : forall A, M A -> M A -> M A ;
  _ : forall A, associative (@op_alt A) ;
  (* composition distributes leftwards over choice *)
  _ : Laws.bind_left_distributive (@Bind M) op_alt
  (* in general, composition does not distribute rightwards over choice *)
  (* NB: no bindDr to accommodate both angelic and demonic interpretations of nondeterminism *)
}.
Record class_of (m : Type -> Type) : Type := Class {
  base : Monad.class_of m ; mixin : mixin_of (Monad.Pack base) }.
Structure t := Pack { m : Type -> Type ; class : class_of m }.
Definition alt M : forall A, m M A -> m M A -> m M A :=
  let: Pack _ (Class _ (Mixin x _ _)) := M
  return forall A, m M A -> m M A -> m M A in x.
Arguments alt {M A} : simpl never.
Definition baseType (M : t) := Monad.Pack (base (class M)).
Module Exports.
Notation Alt := alt.
Notation "'[~p]'" := (@Alt _). (* postfix notation *)
Notation "x '[~i]' y" := (Alt x y). (* infix notation *)
Notation altMonad := t.
Coercion baseType : altMonad >-> monad.
Canonical baseType.
End Exports.
End MonadAlt.
Export MonadAlt.Exports.

Section monadalt_lemmas.
Variable (M : altMonad).
Lemma alt_bindDl : Laws.bind_left_distributive (@Bind M) [~p].
Proof. by case: M => m [? []]. Qed.
Lemma altA : forall A, associative (@Alt M A).
Proof. by case: M => m [? []]. Qed.

(* TODO: name ok? *)
Lemma naturality_nondeter A B (f : A -> B) p q :
  fmap f (p [~i] q) = fmap f p [~i] fmap f q :> M _.
Proof. by rewrite /fmap alt_bindDl. Qed.

Local Open Scope mu_scope.

Lemma alt_fmapDl A B (f : A -> B) (m1 m2 : M A) :
  f ($) (m1 [~i] m2) = f ($) m1 [~i] f ($) m2.
Proof. by rewrite /fmap alt_bindDl. Qed.

End monadalt_lemmas.

Section arbitrary.

Variables (M : altMonad) (A : Type) (def : A).

Definition arbitrary : seq A -> M A :=
  foldr1 (Ret def) (fun x y => x [~i] y) \o map Ret.

End arbitrary.
Arguments arbitrary {M} {A}.

(* gibbonsUTP2012 *)
Section subsequences_of_a_list.

Variables (M : altMonad) (A : Type).

Fixpoint subs (s : seq A) : M (seq A) :=
  if s isn't h :: t then Ret [::] else
  let t' := subs t in
  fmap (cons h) t' [~i] t'.

Fixpoint SUBS (s : seq A) : Monad.m (MonadAlt.baseType M) _ :=
  if s isn't h :: t then @Monad.ret (MonadAlt.baseType M) _ [::] else
  let t' : Monad.m (MonadAlt.baseType M) _ := SUBS t in
  MonadAlt.alt (@fmap (MonadAlt.baseType M) _ _ (cons h) t') t'.

Goal subs = SUBS. by []. Abort.

Lemma subs_cons x (xs : seq A) :
  subs (x :: xs) = let t' := subs xs in fmap (cons x) t' [~i] t'.
Proof. by []. Qed.

Lemma subs_cat (xs ys : seq A) :
  subs (xs ++ ys) = do us <- subs xs; do vs <- subs ys; Ret (us ++ vs).
Proof.
elim: xs ys => [ys |x xs IH ys].
  by rewrite /= bindretf bindmret.
rewrite [in RHS]subs_cons.
cbv zeta.
rewrite alt_bindDl.
rewrite bindA.
rewrite [in RHS]/=.
Open (X in subs xs >>= X).
  rewrite bindretf.
  rewrite_ cat_cons.
  reflexivity.
rewrite [X in _ = X [~i] _](_ : _ = fmap (cons x) (do x0 <- subs xs; do x1 <- subs ys; Ret (x0 ++ x1))); last first.
  rewrite /fmap.
  rewrite bindA.
  bind_ext => x0.
  rewrite bindA.
  by rewrite_ bindretf.
rewrite -IH.
rewrite cat_cons.
by rewrite subs_cons.
Qed.

End subsequences_of_a_list.

(* mu2017, Sect. 3.1 *)
Section permutation_and_insertion.

Variable M : altMonad.

Local Open Scope mu_scope.

Fixpoint insert {A} (a : A) (s : seq A) : M (seq A) :=
  if s isn't h :: t then Ret [:: a] else
  Ret (a :: h :: t) [~i] (cons h ($) insert a t).
Arguments insert : simpl never.

Lemma insertE A (a : A) s :
  insert a s = if s isn't h :: t then Ret [:: a] else
  Ret (a :: h :: t) [~i] (cons h ($) insert a t).
Proof. by case: s. Qed.

Fixpoint perm {A} (s : seq A) : M (seq A) :=
  if s isn't h :: t then Ret [::] else perm t >>= insert h.


Lemma insert_map A B (f : A -> B) (a : A) :
  insert (f a) \o map f = map f (o) insert a :> (_ -> M _).
Proof.
apply functional_extensionality; elim => [|y xs IH].
  by rewrite [in LHS]/= fcomp_ext 2!insertE fmap_ret.
apply/esym.
rewrite fcomp_ext insertE alt_fmapDl.
(* first branch *)
rewrite fmap_ret [ in X in X [~i] _ ]/=.
(* second branch *)
rewrite -fmap_comp.
rewrite (_ : map f \o cons y = cons (f y) \o map f) //.
rewrite fmap_comp.
rewrite -(fcomp_ext (map f)).
rewrite -IH.
rewrite [RHS]/=.
by rewrite insertE.
Qed.

Lemma perm_map A B (f : A -> B) :
  perm \o map f = map f (o) perm :> (seq A -> M (seq B)).
Proof.
apply functional_extensionality; elim => [/=|x xs IH].
  by rewrite fcomp_ext /= fmap_ret.
rewrite fcomp_ext.
rewrite [in RHS]/=.
rewrite fmap_bind.
rewrite -insert_map.
rewrite -bind_fmap.
rewrite /=.
rewrite -fcomp_ext.
by rewrite -IH.
Qed.

End permutation_and_insertion.
Arguments insert {M} {A} : simpl never.
Arguments perm {M} {A}.

Module MonadAltCI.
Record mixin_of (M : Type -> Type) (op : forall A, M A -> M A -> M A) : Type := Mixin {
  _ : forall A, idempotent (op A) ;
  _ : forall A, commutative (op A)
}.
Record class_of (m : Type -> Type) : Type := Class {
  base : MonadAlt.class_of m ;
  mixin : mixin_of (@MonadAlt.alt (MonadAlt.Pack base)) }.
Structure t := Pack { m : Type -> Type ; class : class_of m }.
Definition baseType (M : t) := MonadAlt.Pack (base (class M)).
Module Exports.
Notation altCIMonad := t.
Coercion baseType : altCIMonad >-> altMonad.
Canonical baseType.
End Exports.
End MonadAltCI.
Export MonadAltCI.Exports.

Section altci_lemmas.
Variable (M : altCIMonad).
Lemma altmm : forall A, idempotent (@Alt _ A : M A -> M A -> M A).
Proof. by case: M => m [? []]. Qed.
Lemma altC : forall A, commutative (@Alt _ A : M A -> M A -> M A).
Proof. by case: M => m [? []]. Qed.
Lemma altCA A : @left_commutative (M A) (M A) (fun x y => x [~i] y).
Proof. move=> x y z. by rewrite altA altC altA altC (altC z). Qed.
Lemma altAC A : @right_commutative (M A) (M A) (fun x y => x [~i] y).
Proof. move=> x y z; by rewrite altC altA (altC x). Qed.
Lemma altACA A : @interchange (M A) (fun x y => x [~i] y) (fun x y => x [~i] y).
Proof. move=> x y z t; rewrite !altA; congr (_ [~i] _); by rewrite altAC. Qed.
End altci_lemmas.

(* mu2017, Sect. 3.2 *)
Section spark_aggregation.
Local Open Scope mu_scope.

Let Partition A := seq A.
Let RDD A := seq (Partition A).

Variable M : altCIMonad.

Lemma insert_rcons A (x : A) y xs :
  insert x (rcons xs y) = Ret (xs ++ [:: y; x]) [~i] (rcons^~ y ($) insert x xs) :> M _.
Proof.
elim: xs x y => [/= x y|xs1 xs2 IH x y].
  by rewrite !insertE !fmap_ret /= altC.
rewrite /= insertE /= IH /=.
rewrite naturality_nondeter fmap_ret.
rewrite naturality_nondeter fmap_ret.
rewrite -!fmap_comp /=.
by rewrite altCA.
Qed.

Section foldl_perm_deterministic.
Variables (A B : Type) (op : B -> A -> B).
Local Notation "x (.) y" := (op x y) (at level 11).
Hypothesis opP : forall (x y : A) (w : B), (w (.) x) (.) y = (w (.) y) (.) x.

Lemma lemma_35 x (b : B) : foldl op b (o) insert x = Ret \o foldl op b \o (rcons^~ x) :> (_ -> M _).
Proof.
apply functional_extensionality => xs; move: xs b; elim/last_ind => [/=|xs y IH] b.
  by rewrite fcomp_ext insertE fmap_ret.
rewrite fcomp_ext.
rewrite insert_rcons.
rewrite naturality_nondeter fmap_ret.
rewrite -fmap_comp.
have H : forall w, foldl op b \o rcons^~ w = op^~ w \o foldl op b.
  by move=> w; apply functional_extensionality => ws /=; rewrite -cats1 foldl_cat.
rewrite (H y).
rewrite fmap_comp.
move: (IH b) => {IH}IH.
rewrite fcomp_ext in IH.
rewrite IH.
rewrite -[in X in _ [~i] X]bindretf.
rewrite bindretf.
rewrite -{1}compA.
rewrite fmap_ret.
rewrite (H x).
rewrite [in X in _ [~i] X]/=.
rewrite opP.
rewrite /= -!cats1 -catA /=.
rewrite foldl_cat /=.
by rewrite altmm.
Qed.

(* TODO(rei): clean *)
Lemma lemma_34 b : foldl op b (o) perm = Ret \o foldl op b :> (_ -> M _).
Proof.
apply functional_extensionality => xs; move: xs b; elim=> [/=|x xs IH] b.
  by rewrite /= fcomp_ext /= fmap_ret.
rewrite fcomp_ext [in LHS]/= fmap_bind.
rewrite_ lemma_35.
transitivity ((Ret \o foldl op (b (.) x)) xs : M _); last by [].
rewrite -IH.
rewrite [in RHS]fcomp_ext.
rewrite /fmap.
bind_ext => ys.
rewrite /= -cats1 foldl_cat /=.
congr (Ret _ : M _).
elim: ys b => // y ys ih /= b.
by rewrite ih /= opP.
Qed.

End foldl_perm_deterministic.

Definition aggregate A B (b : B) (mul : B -> A -> B) (add : B -> B -> B) : RDD A -> M B :=
  foldl add b (o) (perm \o map (foldl mul b)).

Definition deterministic A B (f : A -> M B) :=
  exists g : A -> B, f = Ret \o g.

Lemma aggregateP A B (b : B) (mul : B -> A -> B) (add : B -> B -> B) :
  associative add -> commutative add -> left_id b add -> right_id b add ->
  deterministic (aggregate b mul add).
Proof.
move=> addA addC add0b addb0.
rewrite /deterministic; exists (foldl add b \o map (foldl mul b)).
(* NB(rei): mu2017 is using perm_map (lemma 3.1) and (7) but that does not seem useful*)
rewrite compA -[in RHS]lemma_34; last by move=> x ??; rewrite -addA (addC x) addA.
by [].
Qed.

End spark_aggregation.

Module MonadNondet.
Record mixin_of (M : failMonad) (a : forall A, M A -> M A -> M A) : Type :=
  Mixin { _ : Laws.left_id (@Fail M) a ;
          _ : Laws.right_id (@Fail M) a
}.
Record class_of (m : Type -> Type) : Type := Class {
  base : MonadFail.class_of m ;
  base2 : MonadAlt.mixin_of (Monad.Pack (MonadFail.base base)) ;
  mixin : @mixin_of (MonadFail.Pack base) (MonadAlt.op_alt base2)
}.
Structure t : Type := Pack { m : Type -> Type ; class : class_of m }.
Definition baseType (M : t) := MonadFail.Pack (base (class M)).
Module Exports.
Notation nondetMonad := t.
Coercion baseType : nondetMonad >-> failMonad.
Canonical baseType.
Definition alt_of_nondet (M : nondetMonad) : altMonad :=
  MonadAlt.Pack (MonadAlt.Class (base2 (class M))).
Canonical alt_of_nondet.
End Exports.
End MonadNondet.
Export MonadNondet.Exports.

Section nondet_lemmas.
Variable (M : nondetMonad).
Lemma altmfail : Laws.right_id (@Fail M) [~p].
Proof. by case: M => m [[? ?] [? ? ?] [? ?]]. Qed.
Lemma altfailm : Laws.left_id (@Fail M) [~p]. (* NB: not used? *)
Proof. by case: M => m [[? ?] [? ? ?] [? ?]]. Qed.
End nondet_lemmas.

Lemma test_canonical (M : nondetMonad) A (a : M A) (b : A -> M A) :
  a [~i] (Fail >>= b) = a [~i] Fail.
Proof.
Set Printing All.
Unset Printing All.
by rewrite bindfailf.
Abort.

Section nondet_big.
Variables (M : nondetMonad) (A : Type).
Canonical alt_monoid :=
  Monoid.Law (@altA (alt_of_nondet M) A) (@altfailm _ _) (@altmfail _ _).

Lemma test_bigop n : \big[Alt/Fail]_(i < n) (Fail : M A) = Fail.
Proof.
elim: n => [|n IH]; first by rewrite big_ord0.
by rewrite big_ord_recr /= IH altmfail.
Qed.

End nondet_big.

(* gibbons2011icfp Sect. 4.4 *)

Section select.
Variables (M : nondetMonad) (A : Type).
Implicit Types s : seq A.

Fixpoint select s : M (A * seq A)%type :=
  if s isn't h :: t then Fail else
  (Ret (h, t) [~i] do x <- select t; Ret (x.1, h :: x.2)).

Local Obligation Tactic := idtac.
(* variant of select that keeps track of the length, useful to write perms *)
Program Fixpoint tselect s : M (A * (size s).-1.-tuple A)%type :=
  if s isn't h :: t then Fail else
  (Ret (h, @Tuple (size t) A t _) [~i]
  do x <- tselect t; Ret (x.1, @Tuple (size t) A _ _ (* h :: x.2 *))).
Next Obligation. by []. Defined.
Next Obligation.
move=> s h [|h' t] hts [x1 x2]; [exact: [::] | exact: (h :: x2)].
Defined.
Next Obligation.
move=> s h [|h' t] hts [x1 x2] //=; by rewrite size_tuple.
Defined.
Next Obligation. by []. Defined.

Lemma tselect_nil : tselect [::] = Fail. Proof. by []. Qed.

Lemma tselect1 a : tselect [:: a] = Ret (a, [tuple]).
Proof.
rewrite /= bindfailf altmfail /tselect_obligation_1 /= tupleE /nil_tuple.
do 3 f_equal; exact: proof_irrelevance.
Qed.

Program Definition tselect_cons_statement a t (_ : t <> nil) :=
  tselect (a :: t) = Ret (a, @Tuple _ _ t _) [~i]
                    do x <- tselect t; Ret (x.1, @Tuple _ _ (a :: x.2) _).
Next Obligation. by []. Defined.
Next Obligation.
move=> a t t0 [x1 x2].
rewrite /= size_tuple prednK //; by destruct t.
Defined.

Program Lemma tselect_cons a t (Ht : t <> nil) : tselect_cons_statement a Ht.
Proof.
rewrite /tselect_cons_statement [in LHS]/=; congr (_ [~i] _).
bind_ext; case=> x1 x2 /=.
do 2 f_equal; apply val_inj => /=; by destruct t.
Qed.

Local Open Scope mu_scope.

Lemma selectE s : select s =
  (fun xy => (xy.1, tval xy.2)) ($) tselect s :> M (A * seq A)%type.
Proof.
elim: s => [|h [|h' t] IH].
- by rewrite /fmap bindfailf.
- by rewrite tselect1 fmap_ret /= bindfailf altmfail.
- rewrite [h' :: t]lock /= -lock IH [in RHS]alt_fmapDl fmap_ret; congr (_ [~i] _).
  rewrite bind_fmap fmap_bind; bind_ext => -[x1 x2].
  by rewrite fcomp_ext fmap_ret.
Qed.

Lemma decr_size_select : bassert_size select.
Proof.
case => [|h t]; first by rewrite !selectE /= fmap_fail /bassert bindfailf.
rewrite /bassert selectE bind_fmap /fmap; bind_ext => -[x y] /=.
by rewrite /assert /guard /= size_tuple ltnS leqnn bindskipf.
Qed.

End select.
Arguments select {M} {A}.
Arguments tselect {M} {A}.

Section permutations.
Variables (M : nondetMonad) (A : Type).
Implicit Types s : seq A.

Local Obligation Tactic := idtac.
Program Definition perms' s
  (f : forall s', size s' < size s -> M (seq A)) : M (seq A) :=
  if s isn't h :: t then Ret [::] else
    do x <- tselect (h :: t); do y <- f x.2 _; Ret (x.1 :: y).
Next Obligation.
move=> s H h t hts [y ys]; by rewrite size_tuple -hts /= ltnS leqnn.
Qed.
Next Obligation. by []. Qed.

Definition perms : seq A -> M (seq A) :=
  Fix (@well_founded_size _) (fun _ => M _) perms'.

Lemma tpermsE s : perms s = if s isn't h :: t then Ret [::] else
  do x <- tselect (h :: t); do y <- perms x.2; Ret (x.1 :: y).
Proof.
rewrite {1}/perms Fix_eq //; [by case: s|move=> s' f g H].
by rewrite /perms'; destruct s' => //=; bind_ext=> x; rewrite H.
Qed.

Lemma permsE s : perms s = if s isn't h :: t then Ret [::] else
  do x <- select (h :: t); do y <- perms x.2; Ret (x.1 :: y).
Proof.
rewrite tpermsE; case: s => // h t.
by rewrite selectE bind_fmap.
Qed.

End permutations.
Arguments perms {M} {A}.

(* from section 4.3 of mu2017, definition of perms using unfoldM *)
Section mu_perm.
Variables (A : Type) (M : nondetMonad).

Definition mu_perm : seq A -> M (seq A) :=
  unfoldM (@well_founded_size _) (@nilp _) select.

Lemma mu_permE s : mu_perm s = if s isn't h :: t then Ret [::]
  else do a <- select (h :: t) ; do b <- mu_perm a.2; Ret (a.1 :: b).
Proof. rewrite /mu_perm unfoldME; [by case: s | exact: decr_size_select]. Qed.

Lemma perms_mu_perm s : perms s = mu_perm s.
Proof.
move Hn : (size s) => n.
elim: n s Hn => [|n IH [//|h t] /= [tn]].
  case => //; by rewrite permsE mu_permE.
rewrite tpermsE mu_permE selectE bind_fmap; bind_ext => -[a b].
by rewrite /= IH // size_tuple.
Qed.

End mu_perm.
Arguments mu_perm {A} {M}.

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

Module Exports.
Notation nondetSyntax := t.
Notation ndAlt := alt.
Notation ndRet := ret.
Notation ndBind := bind.
Notation ndFail := fail.
Notation ndDenote := denote.
End Exports.
End SyntaxNondet.
Export SyntaxNondet.Exports.

Module MonadExcept.
Record mixin_of (M : failMonad) : Type := Mixin {
  op_catch : forall A, M A -> M A -> M A ;
  (* monoid *)
  _ : forall A, right_id Fail (@op_catch A) ;
  _ : forall A, left_id Fail (@op_catch A) ;
  _ : forall A, associative (@op_catch A) ;
  (* unexceptional bodies need no handler *)
  _ : forall A x, left_zero (Ret x) (@op_catch A)
  (* NB: left-zero of sequential composition inherited from failMonad *)
}.
Record class_of (m : Type -> Type) := Class {
  base : MonadFail.class_of m ;
  mixin : mixin_of (MonadFail.Pack base) }.
Record t : Type := Pack { m : Type -> Type ; class : class_of m }.
Definition catch (M : t) : forall A, m M A -> m M A -> m M A :=
  let: Pack _ (Class _ (Mixin x _ _ _ _)) := M
  return forall A, m M A -> m M A -> m M A in x.
Arguments catch {M A} : simpl never.
Definition baseType M := MonadFail.Pack (base (class M)).
Definition monadType M := Monad.Pack (MonadFail.base (base (class M))).
Module Exports.
Notation Catch := catch.
Notation exceptMonad := t.
Coercion baseType : exceptMonad >-> failMonad.
Canonical baseType.
Canonical monadType.
End Exports.
End MonadExcept.
Export MonadExcept.Exports.

Section except_lemmas.
Variables (M : exceptMonad).
Lemma catchfailm : forall A, left_id Fail (@Catch M A).
Proof. by case: M => m [? []]. Qed.
Lemma catchmfail : forall A, right_id Fail (@Catch M A). (* NB: not used? *)
Proof. by case: M => m [? []]. Qed.
Lemma catchret : forall A x, left_zero (Ret x) (@Catch M A).
Proof. by case: M => m [? []]. Qed.
Lemma catchA : forall A, associative (@Catch M A). (* NB: not used? *)
Proof. by case: M => m [? []]. Qed.
End except_lemmas.

Section fastproduct.

Definition product (s : seq nat) := foldr muln 1 s.

Lemma product0 s : O \in s -> product s = O.
Proof.
elim: s => //= h t ih; rewrite inE => /orP[/eqP <-|/ih ->];
  by rewrite ?muln0 ?mul0n.
Qed.

Section work.

Variable M : failMonad.

Definition work s : M nat :=
  if O \in s then Fail else Ret (product s).

(* work refined to eliminate multiple traversals *)
Lemma workE :
  let next := fun n mx => if n == 0 then Fail else fmap (muln n) mx in
  work = foldr next (Ret 1).
Proof.
apply foldr_universal => // h t; case: ifPn => [/eqP -> //| h0].
by rewrite /work inE eq_sym (negbTE h0) [_ || _]/= fmap_if fmap_fail.
Qed.

End work.
Arguments work {M}.

Variable M : exceptMonad.

Definition fastprod s : M _ := Catch (work s) (Ret O).

(* fastprod is pure, never throwing an unhandled exception *)
Lemma fastprodE s : fastprod s = Ret (product s).
Proof.
rewrite /fastprod /work lift_if if_ext catchfailm.
by rewrite catchret; case: ifPn => // /product0 <-.
Qed.

End fastproduct.
