From mathcomp Require Import all_ssreflect.
From mathcomp Require boolp.
Require Import monae_lib hierarchy monad_lib fail_lib.
From infotheo Require Import ssr_ext.

(******************************************************************************)
(*                            Quicksort example                               *)
(*                                                                            *)
(* wip!                                                                       *)
(******************************************************************************)

(* TODO: shouldn't prePlusMonad be plusMonad (like list monad) and
   plusMonad be plusCIMonad (like set monad) *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope order_scope.
Import Order.TTheory.
Local Open Scope monae_scope.
Local Open Scope tuple_ext_scope.

(* TODO: move *)
Lemma kleisliE (M : monad) (A B C : UU0) (g : B -> M C) (f : A -> M B) (a : A) :
  (f >=> g) a = (f a) >>= g.
Proof. by rewrite /kleisli /= join_fmap. Qed.

Fixpoint splits {M : plusMonad} A (s : seq A) : M (seq A * seq A)%type :=
  if s isn't x :: xs then Ret ([::], [::])  else
    splits xs >>= (fun '(ys, zs) => Ret (x :: ys, zs) [~]
                                     Ret (ys, x :: zs)).

Program Fixpoint tsplits {M : plusMonad} A (s : seq A) : M ((size s).-bseq A * (size s).-bseq A)%type :=
  if s isn't x :: xs then Ret (bseq0 _  _, bseq0 _ _) (*TODO: try to use [bseq of [::]]*) else
    tsplits xs >>= (fun '(ys, zs) => Ret (@Bseq _ _ (x :: ys) _ , @Bseq _ _ zs _) [~]
                                     Ret (@Bseq _ _  ys _, @Bseq _ _ (x :: zs) _)).
Next Obligation. by rewrite (leq_ltn_trans (size_bseq b)). Qed.
Next Obligation. by rewrite (leq_trans (size_bseq b0)). Qed.
Next Obligation. by rewrite (leq_trans (size_bseq b)). Qed.
Next Obligation. by rewrite (leq_ltn_trans (size_bseq b0)). Qed.

(*Goal forall M, @splits M _ [:: O; 1]%nat = Ret ([::], [::]).
move=> M.
rewrite /= bindretf alt_bindDl !bindretf.
Abort.*)

Local Open Scope mprog.
Lemma splitsE {M : plusMonad} A (s : seq A) :
  splits s = fmap (fun xy => (bseqval xy.1, bseqval xy.2)) (tsplits s) :> M _.
Proof.
elim: s => /= [|h t ih]; first by rewrite fmapE bindretf.
rewrite {}ih /= !fmapE 2!bindA; bind_ext => -[a b] /=.
by rewrite bindretf alt_bindDl 2!bindretf.
Qed.
Local Close Scope mprog.

Section qperm.
Variables (M : plusMonad) (A : Type).

Local Obligation Tactic := idtac.
Program Definition qperm' (s : seq A)
    (f : forall s', size s' < size s -> M (seq A)) : M (seq A) :=
  if s isn't x :: xs then Ret [::] else
    tsplits xs >>= (fun a => let: (ys, zs) := a in liftM2 (fun a b => a ++ [:: x] ++ b) (f ys _) (f zs _)).
Next Obligation.
move=> [|h t] // ht x xs [xh xst] [a b ys zs] [-> zsb].
by apply: (leq_ltn_trans (size_bseq a)); rewrite xst.
Qed.
Next Obligation.
move=> [|h t] // ht x xs [xh xst] [a b ys zs] [ysa ->].
by apply: (leq_ltn_trans (size_bseq b)); rewrite xst.
Qed.
Next Obligation. by move=> /= s _ x xs. Qed.

Definition qperm : seq A -> M (seq A) :=
  Fix (@well_founded_size _) (fun _ => M _) qperm'.

Lemma qperm'_Fix (s : seq A) (f g : forall y, (size y < size s)%N -> M (seq A)) :
  (forall y (p : (size y < size s)%N), f y p = g y p) -> qperm' f = qperm' g.
Proof.
move=> H; rewrite /qperm'; case: s f g H => // h t f g H.
bind_ext => -[a b] /=; rewrite /liftM2 H (_ : f = g) //.
apply fun_ext_dep => s.
by rewrite boolp.funeqE=> p; exact: H.
Qed.

Lemma qperm_nil : qperm [::] = Ret [::].
Proof. by rewrite /qperm (Fix_eq _ _ _ qperm'_Fix). Qed.

Lemma qperm_cons x xs :
  qperm (x :: xs) = splits xs >>= (fun a => let: (ys, zs) := a in
                    liftM2 (fun a b => a ++ [:: x] ++ b) (qperm ys) (qperm zs)).
Proof.
rewrite {1}/qperm {1}(Fix_eq _ _ _ qperm'_Fix) /=.
rewrite splitsE /= fmapE bindA; bind_ext => -[s1 s2] /=.
by rewrite bindretf.
Qed.

End qperm.
Arguments qperm {M} {A}.

Definition refin {M : plusMonad} A (m1 m2 : M A) : Prop := m1 [~] m2 = m2.

Reserved Notation "A `<=` B" (at level 70, no associativity).
Reserved Notation "A `>=` B" (at level 70, no associativity).
Notation "m1 `<=` m2" := (refin m1 m2) : monae_scope.
Notation "m1 `>=` m2" := (refin m2 m1) : monae_scope.

Reserved Notation "A `<.=` B" (at level 70, no associativity).
Definition lrefin {M : plusMonad} A B (f g : A -> M B) : Prop :=
  forall x, f x `<=`g x.
Notation "f `<.=` g" := (lrefin f g) : monae_scope.

Lemma bind_monotonic_refin (M : plusMonad) A B (m1 m2 : M A) (f : A -> M B) :
  (m1 `<=` m2) -> (m1 >>= f `<=` m2 >>= f).
Proof. by move=> m12; rewrite /refin -alt_bindDl m12. Qed.

Lemma bind_monotonic_lrefin (M : plusMonad) A B (m : M A) (f1 f2 : A -> M B) :
  (f1 `<.=` f2) -> (m >>= f1 `<=` m >>= f2).
Proof.
move=> f12.
rewrite /refin.
rewrite -alt_bindDr.
by bind_ext => a; apply f12.
Qed.

Lemma guard_neg (M : plusMonad) A (p q : bool) (m1 m2 : M A) :
  (if p then m1 else m2) `<=` (guard p >> m1) [~] (guard (~~ p) >> m2).
Proof.
rewrite /refin; case: ifPn => /= [pT|pF]; rewrite !(guardT,guardF).
by rewrite bindskipf bindfailf altA altmm.
by rewrite bindfailf bindskipf altCA altmm.
Qed.

Section slowsort.
Variable M : plusMonad.
Variables (d : unit) (T : porderType d).

Let leT := (fun x y : T => x <= y)%O.
Let sorted := sorted leT.

Lemma sorted_cat' (a b : seq T) : sorted (a ++ b) -> sorted a && sorted b.
Proof.
elim: a b => //= h t ih b; rewrite cat_path => /andP[-> /=].
exact: path_sorted.
Qed.

(* equation 5 *)
Lemma sorted_cat_cons (s s' : seq T) (p : T) :
  sorted (s ++ p :: s') = [&& sorted s, sorted s', all (<= p) s & all (>= p) s'].
Proof.
apply/idP/idP => [|].
  rewrite -cat1s => H; apply/and4P; split.
  by move: H => /sorted_cat'/andP[].
  by move: H; rewrite catA => /sorted_cat'/andP[].
  move: H; rewrite catA => /sorted_cat'/andP[].
  by rewrite {1}/sorted -rev_sorted rev_cat /= (path_sortedE ge_trans) all_rev => /andP[].
  move/sorted_cat' : H => /andP[_].
  by rewrite {1}/sorted /= (path_sortedE le_trans) // => /andP[].
case/and4P=> ss ss' ps ps'; apply sorted_cat => //=.
  by rewrite (path_sortedE le_trans) ps'.
move=> t ts t' t'ps'; apply: (@le_trans _ _ p); first by move/allP : ps; apply.
by move: t'ps'; rewrite inE => /orP[/eqP ->//|]; move/allP : ps'; apply.
Qed.

Definition slowsort : seq T -> M (seq T) :=
  (qperm >=> assert sorted)%monae.

(*Definition invariant_by_qperm (p : pred (seq T)) :=
  forall s, p s -> qperm s >>= (fun x => guard (p x)) = Ret true.*)

Lemma guard_qperm_eq (B : Type) (p : T) (a : seq T) (f : seq T -> M B) :
 guard (all (<= p) a) >> (qperm a >>= f) = qperm a >>= (fun x => guard (all (<= p) x) >> f x).
Proof.
elim: a p f => /= => [p f|x xs ih p f].
  by rewrite guardT bindskipf qperm_nil 2!bindretf /= guardT bindskipf.
Admitted.

Lemma guard_qperm_eq2 (B : Type) (p : T) (a : seq T) (f : seq T -> M B) :
 guard (all (>= p) a) >> (qperm a >>= f) = qperm a >>= (fun x => (guard (all (>= p) x) >> f x)).
Admitted.

Lemma guard_qperm_neq (B : Type) (p : T) (b a : seq T) (f : seq T -> M B) :
 guard (all (>= p) b) >> (qperm a >>= f) = qperm a >>= (fun x => (guard (all (>= p) b) >> f x)).
Admitted.

Lemma guard_qperm_neq2 (B : Type) (p : T) (b a : seq T) (f : seq T -> M B) :
 guard (all (<= p) b) >> (qperm a >>= f) = qperm a >>= (fun x => (guard (all (<= p) b) >> f x)).
Admitted.

Lemma refin_slowsort_inductive_case (p : T) (xs : seq T) :
  slowsort (p :: xs) =
  splits xs >>= (fun '(ys, zs) => guard (all (<= p) ys && all (>= p) zs) >>
    (qperm ys >>= assert sorted) >>= (fun ys' =>
    (qperm zs >>= assert sorted) >>= (fun zs' =>
    Ret (ys' ++ [:: p] ++ zs')))).
Proof.
transitivity (splits xs >>= (fun '(ys, zs) =>
    qperm ys >>= (fun ys' => qperm zs >>= (fun zs' =>
    assert sorted (ys' ++ [:: p] ++ zs')))) : M _).
  rewrite /slowsort /= kleisliE qperm_cons /= !bindA.
  bind_ext => -[a b] /=.
  rewrite /liftM2 bindA; bind_ext => s.
  by rewrite bindA; bind_ext => s'; rewrite bindretf.
transitivity (splits xs >>= (fun '(ys, zs) =>
    qperm ys >>= (fun ys' => qperm zs >>= (fun zs' =>
    guard ([&& sorted ys', sorted zs', all (<= p) ys' & all (>= p) zs']) >>
    Ret (ys' ++ [:: p] ++ zs')))) : M _).
  bind_ext => -[a b]; bind_ext => s; bind_ext => s'; rewrite assertE /=.
  by rewrite -sorted_cat_cons.
bind_ext=> {xs} -[a b].
rewrite guard_and 2!bindA (bindA (qperm a)).
rewrite guard_qperm_neq.
rewrite guard_qperm_eq.
bind_ext => s.
do 3 rewrite_ guard_and.
transitivity (qperm b >>=
  (fun x =>
   guard (all (>= p) x) >> (guard (all (<= p) s) >> (guard (sorted x) >> ((guard (sorted s)) >> Ret (s ++ [:: p] ++ x)))) : M _)).
  bind_ext => s'.
  rewrite -!bindA -!guard_and.
  rewrite andbC.
  rewrite (andbC _ (all (<= p) s)).
  rewrite (andbC (sorted s)).
  by rewrite !andbA.
rewrite -guard_qperm_eq2.
rewrite -[in RHS]bindA.
rewrite -[in RHS]guard_and [in RHS]andbC [in RHS]guard_and.
rewrite [in RHS]bindA.
congr (_ >> _).
rewrite boolp.funeqE => s'.
rewrite -guard_qperm_neq2.
congr (_ >> _).
rewrite boolp.funeqE => s2.
rewrite_ bindA.
rewrite assertE bindA bindretf.
rewrite guardsC; last exact: (@bindmfail M).
rewrite bindA.
bind_ext => s3.
by rewrite assertE !bindA 2!bindretf assertE.
Qed.

Fixpoint partition p (s : seq T) : seq T * seq T :=
  if s isn't x :: xs then ([::], [::]) else
  let: (ys, zs) := partition p xs in
  if x <= p then (x :: ys, zs) else (ys, x :: zs).

Lemma size_partition p (s : seq T) :
  size (partition p s).1 + size (partition p s).2 = size s.
Proof.
elim: s p => //= x xs ih p; have {ih} := ih p.
move H : (partition p xs) => h; case: h H => a b ab /= abxs.
by case: ifPn => xp /=; rewrite ?(addSn,addnS) abxs.
Qed.

Lemma refin_partition (p : T) (xs : seq T) :
  (Ret (partition p xs) : M (seq T * seq T)%type (*TODO: :> notation for `<=`?*))
  `<=`
  splits xs >>= assert (fun '(ys, zs) => (all (<= p) ys && all (>= p) zs)).
Proof.
elim: xs p => [p /=|x xs ih p].
  by rewrite bindretf /refin /= !assertE !all_nil /= guardT bindskipf altmm.
rewrite /=.
move pxs : (partition p xs) => s; case: s pxs => ys zs pxs.
case: ifPn => xp.
rewrite (_ : (fun '(_, _) => _) = (fun i => Ret (x :: i.1, i.2) [~] Ret (i.1, x :: i.2))); last first.
  by rewrite boolp.funeqE => -[a b]. (* TODO: awkward  *)
  rewrite alt_bindDr.
  rewrite alt_bindDl.
Admitted.

Lemma refin_slowsort (p : T) (xs : seq T) :
  slowsort (p :: xs) `>=`
  Ret (partition p xs) >>= (fun '(ys, zs) =>
    slowsort ys >>= (fun ys' => slowsort zs >>= (fun zs' => Ret (ys' ++ [:: p] ++ zs')))).
Proof.
rewrite [X in X `>=` _]refin_slowsort_inductive_case.
rewrite [X in X `>=` _](_ : _ = splits xs >>=
  (fun a => guard (let '(ys, zs) := a in all (<= p) ys && all (>= p) zs) >> Ret a) >>=
  fun '(ys, zs) => (qperm ys >>= assert sorted) >>=
   (fun ys' => (qperm zs >>= assert sorted) >>= (fun zs'=> Ret (ys' ++ [:: p] ++ zs')))); last first.
  rewrite bindA; bind_ext => -[s1 s2];rewrite !bindA; congr (_ >> _).
  by rewrite boolp.funeqE => -[]; rewrite bindretf bindA.
apply: bind_monotonic_refin.
have := refin_partition p xs.
by rewrite /assert; unlock.
Qed.

Program Fixpoint qsort' (s : seq T)
    (f : forall s', (size s' < size s)%N -> seq T) : seq T :=
  if s isn't p :: xs then [::] else
  let: (ys, zs) := partition p xs in
  f ys _ ++ [:: p] ++ f zs _.
Next Obligation.
have := size_partition p xs.
by rewrite -Heq_anonymous /= => <-; rewrite ltnS leq_addr.
Qed.
Next Obligation.
have := size_partition p xs.
by rewrite -Heq_anonymous /= => <-; rewrite ltnS leq_addl.
Qed.

Definition qsort : seq T -> seq T :=
  Fix (@well_founded_size _) (fun _ => _) qsort'.

Lemma qsort'_Fix (x : seq T)
  (f g : forall y : seq T, (size y < size x)%N -> seq T) :
  (forall (y : seq T) (p : (size y < size x)%N), f y p = g y p) ->
  qsort' f = qsort' g.
Proof.
by move=> ?; congr qsort'; apply fun_ext_dep => ?; rewrite boolp.funeqE.
Qed.

Lemma qsort_nil : qsort [::] = [::].
Proof. by rewrite /qsort Fix_eq //; exact: qsort'_Fix. Qed.

Lemma qsort_cons p (xs : seq T) :
  qsort (p :: xs) = let: (ys, zs) := partition p xs in
                    qsort ys ++ [:: p] ++ qsort zs.
Proof.
rewrite [in LHS]/qsort Fix_eq /=; last exact: qsort'_Fix.
by move s12 : (partition p xs) => h; case: h s12.
Qed.

Definition qsortE := (qsort_nil, qsort_cons).

(* TODO: Ret \o qsort `<.=` slowsort by induction on the length of the input list *)

End slowsort.

Goal let s := [:: 3; 42; 230; 1; 67; 2]%N in qsort s = sort ltn s.
move=> s; rewrite /s sortE /=.
by repeat rewrite qsortE /=.
Abort.

Definition size_preserving (M : monad) (A : UU0) (f : seq A -> M (seq A)) :=
  forall xs, f xs >>= (fun ys => Ret (ys, size ys)) = f xs >>= (fun ys => Ret (ys, size xs)).

Lemma size_preserving_qperm (M : plusMonad) (A : UU0) :
  size_preserving (@qperm M A).
Proof.
move=> s; move sn : (size s) => n.
elim/ltn_ind: n s sn => n ih [/= <-{ih n}| h t].
  by rewrite qperm_nil 2!bindretf.
case: n ih => // n ih [tn].
rewrite qperm_cons.
rewrite splitsE /=.
Abort.
