(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2020 monae authors, license: LGPL-2.1-or-later               *)
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
  if s isn't x :: xs then Ret ([::], [::]) else
    splits xs >>= (fun '(ys, zs) => Ret (x :: ys, zs) [~] Ret (ys, x :: zs)).

Program Fixpoint tsplits {M : plusMonad} A (s : seq A) : M ((size s).-bseq A * (size s).-bseq A)%type :=
  if s isn't x :: xs then Ret (bseq0 _  _, bseq0 _ _) (*TODO: try to use [bseq of [::]]*) else
    tsplits xs >>= (fun '(ys, zs) => Ret (@Bseq _ _ (x :: ys) _ , @Bseq _ _ zs _) [~]
                                     Ret (@Bseq _ _  ys _, @Bseq _ _ (x :: zs) _)).
Next Obligation. by rewrite (leq_ltn_trans (size_bseq b)). Qed.
Next Obligation. by rewrite (leq_trans (size_bseq b0)). Qed.
Next Obligation. by rewrite (leq_trans (size_bseq b)). Qed.
Next Obligation. by rewrite (leq_ltn_trans (size_bseq b0)). Qed.

Goal forall M, @splits M nat [::] = Ret ([::], [::]). by []. Qed.

(* Goal forall M, @splits M _ [:: O; 1]%nat = Ret ([::], [::]).
move=> M.
rewrite /= bindretf alt_bindDl !bindretf.
Abort. *)

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

Lemma qperm_consE x xs :
  qperm (x :: xs) = splits xs >>= (fun z =>
    liftM2 (fun a b => a ++ [:: x] ++ b) (qperm z.1) (qperm z.2)).
Proof. by rewrite qperm_cons; bind_ext => -[]. Qed.

Definition qpermE := (qperm_nil, qperm_cons).

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
rewrite /refin -alt_bindDr.
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

Lemma slowsort_nil : slowsort [::] = Ret [::].
Proof.
by rewrite /slowsort kleisliE qpermE bindretf /assert /= guardT bindskipf; unlock.
Qed.

(*Definition invariant_by_qperm (p : pred (seq T)) :=
  forall s, p s -> qperm s >>= (fun x => guard (p x)) = Ret true.*)

Lemma sub (x p : T) (xs : seq T) : (x <= p) && all (<= p) xs -> all (<= p) (x :: xs).
Proof.
  (* by []. *)
  elim: xs => [ // | a l h1 h2 ]. simpl in *.
  by rewrite h2; simpl.
Qed.

Lemma sub_inv (x p : T) (xs : seq T) : (x <= p) && all (<= p) xs <-> all (<= p) (x :: xs).
Proof.
  by [].
Qed.

Lemma guard_sub_inv (x p : T) (xs : seq T) (B : Type) (f : seq T -> M B) : 
  guard ((x <= p) && all (<= p) xs) >> (do x <- qperm (x :: xs); f x)%Do 
  = guard (all (<= p) (x :: xs)) >> (do x <- qperm (x :: xs); f x)%Do.
Proof.
  by [].
Qed.

Lemma Pxs (s : T) (ss : seq T) (p : seq T -> Prop) :
  (forall xs : seq T, p xs) -> p (s :: ss).
Proof.
  by [].
Qed.

Lemma tseqt (s : T) (ss : seq T) (p : seq T -> bool) :
  (forall xs : seq T, p xs) -> p [:: s].
Proof. by []. Qed.

Lemma app_nil_r (xs : seq T) : xs ++ [::] = xs.
Proof.
  (* induction xs.
  done. *)
  elim: xs => [//| a l ih ]. simpl. rewrite ih. done.
Qed.

Lemma guard_splits (p : T) (t : seq T) (C : Type) (f : seq T * seq T -> M C) :
  guard (all (<= p) t) >> (splits t >>= f)
  =
  splits t >>= (fun x => guard (all (<= p) x.1) >>
                      guard (all (<= p) x.2) >> f x).
Proof.
Admitted.

Lemma all_cons (r : rel T) (x p : T) (xs : seq T) :
  all (r p) (x :: xs) -> r p x.
Proof.
  rewrite /all => /andP[] ? _ //.
Qed.
  
Lemma in_all_r (r : rel T) {r_trans : transitive r} (x p : T) (t : seq T) :
  mem t x -> all (r p) t -> r p x.
Proof.
  elim: t => /= //.
  move=> a l ih /=.
  rewrite in_cons => /orP[/eqP|] h /andP[] h1 h2.
  by subst.
  move: h h2 => //.
Qed.

(* Lemma subseq_all p (a b t : seq T) (C : Type) (f : seq T * seq T -> M C) :
  subseq a t && subseq b t -> 
  all (<= p) t -> all (<= p) a && all (<= p) b.
Proof.
  intros.
  induction a.
  induction b. 
  rewrite //.
  move: H => /andP[] h1 h2.
  apply /andP; split => //.
  rewrite /all /=.
  exact: H0. *)

Lemma splits_guard (t : seq T) (C : Type) (f : seq T * seq T -> M C) :
  splits t >>= f =
  splits t >>= (fun x => (guard (subseq x.1 t) >> guard (subseq x.2 t)) >> f x).
Proof.
  (* rewrite 
  (do x <- splits t; (guard (subseqmodulo perm x.1 t) >> guard (subseq x.2 t)) >> f x)%Do. *)
Admitted.

Lemma guard_qperm_eq (B : Type) (p : T) (a : seq T) (f : seq T -> M B) :
  guard (all (<= p) a) >>= (fun _ => qperm a >>= f) =
  qperm a >>= (fun x => guard (all (<= p) x) >> f x).
Proof.
move: p.
move szn : (size a) => n.
elim: n f a szn => [f a /eqP|n ih f].
  rewrite size_eq0 => /eqP ->{a} p.
  by rewrite qperm_nil 2!bindretf.
move=> -[//|h t [tn] p].
rewrite qperm_consE.
rewrite {1}/liftM2.
rewrite !bindA.
rewrite /=.
rewrite guard_and.
rewrite [in LHS]bindA.
(* rewrite [in LHS]bindA. *)
(* 1. guard and split commute *)
transitivity (
  guard (h <= p) >>
  (do x0 <- splits t;
    guard (all (<= p) t) >>
    do x <- do x1 <- qperm x0.1; do x2 <- qperm x0.2; Ret (x1 ++ h :: x2);
    f x)%Do
).
  bind_ext => -[].
  rewrite guard_splits.
  rewrite [in LHS]splits_guard.
  rewrite [in RHS]splits_guard.
  bind_ext => -[a b].
  rewrite -guard_and /=.
  move c1 : (subseq a t && subseq b t) => bl.
  move: c1.
  case: bl => ?.
  rewrite guardT !bindskipf.

  admit.
rewrite ![in RHS]bindA.
transitivity (
  (do x0 <- splits t;
  guard (h <= p) >>
   guard (all (<= p) t) >>
   (do x <-
    do x1 <- qperm x0.1; do x2 <- qperm x0.2; Ret (x1 ++ h :: x2);
    f x))%Do
).
admit.
(* bind_ext => -[a b].
rewrite /=.
rewrite /liftM2. *)
(* use ih after generalization *)
Admitted.

(*
  rewrite guardsC; last exact: (@bindmfail M).
  rewrite bindA.  
  bind_ext => x.
  rewrite guardsC; last exact: (@bindmfail M).
  
  (* rewrite [in LHS]bindA. *)
  case: (x == a) => //.
  bind_ext => x1.*)

  (* elim: x => [|a0 l].
  elim: a => [//|a l].
  rewrite /=.
  rewrite /assert /guard; unlock.
  rewrite bindskipf.
  elim: a => //= => [| x xs ih ].
  by rewrite guardT bindskipf qperm_nil 2!bindretf /= guardT bindskipf.
  rewrite guard_and.
  rewrite bindA.
  rewrite qperm_cons.
  case: (x <= p) => [|].
  rewrite guardT bindskipf.
  rewrite //.
  bind_ext => -[a b].
  rewrite !bindA.
  rewrite guardsC. *)

  (* rewrite joinE.
  rewrite ih.
  elim: a p f => /= => [p f|x xs ih p f].
  rewrite guard_sub_inv.
  subst.
  elim/ltn_ind: a => [].
  move: a. *)
  (* have {ih}.
  rewrite {}ih.
  (* (tl  (hd :: tl)). *)
  unfold guard.
  rewrite qperm_cons.

  rewrite ih.
  case tl.

  rewrite /=.
  apply tseqt.
  by [].
  rewrite guard_and; simpl.

  rewrite <- IHa; auto. move: a0.
  induction a0.
  rewrite IHa.
  move: a; induction a.
  case.
  rewrite qperm_cons.
  destruct IHa.
  move: ih.
  move: tl.


  rewrite guardT.
  elim tl => [ /= |]; simpl in *.
  rewrite qperm_nil.
  rewrite bindskipf.
  rewrite /=.
  rewrite <- ih. *)
  (* rewrite guardT.
  rewrite bindskipf.
  rewrite qperm_nil.
  rewrite bindretf.
  rewrite bindretf. *)

  (* rewrite sub_inv.
  elim: (x :: xs).

  simpl.

  rewrite guardsC.
  rewrite qperm_cons.
  rewrite ih. *)

Lemma guard_qperm_eq2 (B : Type) (p : T) (a : seq T) (f : seq T -> M B) :
 guard (all (>= p) a) >> (qperm a >>= f) = qperm a >>= (fun x => (guard (all (>= p) x) >> f x)).
Admitted.

Lemma guard_qperm_neq (B : Type) (b a : seq T) (r : pred T) (f : seq T -> M B) :
  guard (all r b) >> (qperm a >>= f) =
    qperm a >>= (fun x => (guard (all r b) >> f x)).
Proof.
rewrite guardsC; last exact: (@bindmfail M).
rewrite bindA.
bind_ext => x.
by rewrite guardsC; last exact: (@bindmfail M).
Qed.

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
do 3 under eq_bind do rewrite guard_and.
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
rewrite -guard_qperm_neq.
congr (_ >> _).
rewrite boolp.funeqE => s2.
under [RHS]eq_bind do rewrite bindA.
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
(*apply: bind_monotonic_refin.
have := refin_partition p xs.
by rewrite /assert; unlock.
Qed.*) (*TODO: broken since HB *) Admitted.

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

Lemma lrefin_refl A B (a : A -> M B) :
 a `<.=` a.
Proof. rewrite /lrefin /refin => x. by rewrite altmm. Qed.

Lemma lrefin_trans A B (b a c : A -> M B) :
 a `<.=` b -> b `<.=` c -> a `<.=` c.
Proof.
  rewrite /lrefin /refin => h1 h2 x.
  by rewrite -h2 altA h1.
Qed.

Lemma refin_refl A (a : M A) :
 a `<=` a.
Proof. by rewrite /refin altmm. Qed.

Lemma refin_trans A (b a c : M A) :
 a `<=` b -> b `<=` c -> a `<=` c.
Proof. 
  rewrite /refin => h1 h2.
  by rewrite -h2 altA h1.
Qed.

Lemma quicksort_on_lists : Ret \o qsort `<.=` slowsort.
Proof.
move=> s.
  have [n sn] := ubnP (size s); elim: n => // n ih in s sn *.
  case: s => [|h t] in sn *.
    rewrite /= qsort_nil slowsort_nil. exact: refin_refl.
  rewrite /= qsort_cons.
  move pht : (partition h t) => ht.
  case: ht => ys zs in pht *.
  apply: (refin_trans _ (refin_slowsort h t)).
  rewrite bindretf pht.
  rewrite -(ih ys).
  rewrite -(ih zs).
  repeat rewrite alt_bindDl bindretf.
  rewrite /refin !altA altmm //.
Abort.

(* TODO: Ret \o qsort `<.=` slowsort by induction on the length of the input list *)

End slowsort.

Goal qsort [:: 3; 42; 230; 1; 67; 2]%N = [:: 1; 2; 3; 42; 67; 230]%N.
by repeat rewrite qsortE /=. Abort.

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

Section Test.
Variable M : plusMonad.
Lemma eq1 A B (f : A -> M B) : fail >>= f = fail.
Proof. by apply: bindfailf. Qed.
Lemma eq2 A (m : M A) : m >> fail = (@fail M A).
Proof. by apply: (@bindmfail M). Qed.
  (* move: (@bindmfail M). rewrite /BindLaws.right_zero. //. Qed. *)
Lemma eq3 A B (m1 m2 : M A) (f : A -> M B) : 
  (m1 [~] m2) >>= f = (m1 >>= f) [~] (m2 >>= f).
Proof. by apply: alt_bindDl. Qed.
Lemma eq4 A B (m : M A) (f1 f2 : A -> M B) :
  m >>= (fun x => f1 x [~] f2 x) = (m >>= f1) [~] (m >>= f2).
Proof. by apply: alt_bindDr. Qed.

Variables (d : unit) (T : porderType d).
(* Variables (r : rel T) (r_trans : transitive r). *)
Let leT : rel T := (fun x y : T => x <= y)%O.
Let geT := (fun x y : T => y <= x)%O.

Lemma sorted_cons {r : rel T} {r_trans : transitive r} (x : T) (xs : seq T) :
  sorted r (x :: xs) = sorted r xs && all (r x) xs.
Proof.
  apply/idP/idP => [ /= xxs |/andP[ _ /path_min_sorted /= ->//]].
  rewrite (order_path_min r_trans xxs) ?andbT//.
  exact: path_sorted xxs.
Qed.

Lemma rev_transitivity {r : rel T} {r_trans : transitive r}:
  (transitive (fun x y : T => r^~ x y)).
Proof.
  move=> y x z h1 h2. move: h2 h1.
  by apply r_trans.
Qed.

Lemma sorted_rcons {r : rel T} {r_trans : transitive r} (x : T) (xs : seq T) :
  sorted r (rcons xs x) = sorted r xs && all (r^~ x) xs.
Proof.
  rewrite -rev_sorted rev_rcons sorted_cons.
  rewrite rev_sorted all_rev //.
  apply (@rev_transitivity _ r_trans).
Qed.

Local Notation sorted := (sorted leT).

Lemma sorted_cons' (x : T) (xs : seq T) :
  sorted (x :: xs) = sorted xs && all (leT x) xs.
Proof. by rewrite sorted_cons //; apply le_trans. Qed.

Lemma sorted_rcons' (x : T) (xs : seq T) :
 sorted (rcons xs x) = sorted xs && all (geT x) xs.
Proof. by rewrite sorted_rcons //; apply le_trans. Qed.
(* Proof. by rewrite -rev_sorted rev_rcons (@sorted_cons _ ge_trans) rev_sorted all_rev. Qed. *)

Lemma sorted_cat_cons' (x : T) (ys zs : seq T) : 
  sorted (ys ++ x :: zs) = [&& sorted ys, sorted zs, all (<= x) ys & all (>= x) zs].
Proof.
  apply/idP/idP => H.
  (* -> *)
  have Hr : sorted (ys) && sorted (x :: zs) by apply sorted_cat'.
  rewrite -cat1s catA cats1 in H.
  have Hl : sorted (rcons ys x) && sorted (zs) by apply sorted_cat'.
  move: Hl Hr. rewrite sorted_cons' sorted_rcons' andbC => /and3P[] ? ? ? /and3P[] _ _ ?.
  apply /and4P; split => //.
  (* <- *)
  move: H => /and4P[] p1 p2 allYs allZs.
  rewrite sorted_cat //.
  by rewrite sorted_cons'; apply/andP; split.
  move => a ha b hb.
  apply /(@le_trans _ _ x).
  by move/allP : allYs; apply.
  move: hb; rewrite inE => /orP[/eqP -> //|].
  by move/allP : allZs; apply.
Qed.

Lemma lemma1_l A B (m1 m2 : M A) (f : A -> M B) :
  m1 `<=` m2 -> (m1 >>= f `<=` m2 >>= f).
Proof.
  by move=> m12; rewrite /refin -alt_bindDl m12.
Qed.

Lemma lemma1_r A B (m : M A) (f1 f2 : A -> M B) :
  f1 `<.=` f2 -> (m >>= f1) `<=` (m >>= f2).
Proof.
  move=> f12. 
  (* rewrite /refin -eq4.  *)
  rewrite /refin -alt_bindDr. 
  by bind_ext => a; rewrite f12.
Qed.

Lemma eq7 A (p q : bool) (m1 m2 : M A) :
  (if p then m1 else m2) `<=` (guard p >> m1) [~] (guard (~~ p) >> m2).
Proof.
  rewrite /refin; case: ifPn => /= [pT|pF]; rewrite !(guardT,guardF).
  by rewrite bindskipf bindfailf altA altmm.
  by rewrite bindfailf bindskipf altCA altmm.
Qed.

Definition nondetState_sub S (M : nondetStateMonad S) A (n : M A) :=
  {m | ndDenote m = n}.

Definition commute {M : monad} A B (m : M A) (n : M B) C (f : A -> B -> M C) : Prop :=
  m >>= (fun x => n >>= (fun y => f x y)) = n >>= (fun y => m >>= (fun x => f x y)) :> M _.

Lemma div1 (p : T) (xs : seq T) : 
  slowsort M (p :: xs) = 
  splits xs >>= (fun '(ys, zs) =>
  qperm ys >>= (fun ys' => qperm zs >>= (fun zs' =>
  assert sorted (ys' ++ [:: p] ++ zs')))).
Proof.
  (* expanding definitions, monad laws *)
  rewrite /slowsort.
  rewrite /= kleisliE.
  rewrite qperm_cons /=.
  rewrite bindA.
  bind_ext => -[? ?].
  rewrite /liftM2.
  rewrite bindA; bind_ext => ?.
  rewrite bindA; bind_ext => ?.
  rewrite bindretf.
  done.
Qed.

Lemma div2 (p : T) (xs : seq T) :
  (@splits M _ xs) >>= (fun '(ys, zs) =>
    qperm ys >>= (fun ys' => qperm zs >>= (fun zs' =>
    assert sorted (ys' ++ [:: p] ++ zs')))) =
  splits xs >>= (fun '(ys, zs) =>
      qperm ys >>= (fun ys' => qperm zs >>= (fun zs' =>
      guard ([&& sorted ys', sorted zs', all (<= p) ys' & all (>= p) zs']) >>
      Ret (ys' ++ [:: p] ++ zs')))).
Proof.
  bind_ext => -[? ?]; bind_ext => ?; bind_ext => ?; rewrite assertE /=.
  by rewrite -sorted_cat_cons'. (* by (5) *)
Qed.

Lemma div3 (p : T) (xs : seq T) :
  (@splits M _ xs) >>= (fun '(ys, zs) =>
  qperm ys >>= (fun ys' => 
  qperm zs >>= (fun zs' =>
  guard ([&& sorted ys', sorted zs', all (<= p) ys' & all (>= p) zs']) >>
  Ret (ys' ++ [:: p] ++ zs')))) =
  (@splits M _ xs) >>= (fun '(ys, zs) =>
  qperm ys >>= (fun ys' => 
  qperm zs >>= (fun zs' =>
  guard (sorted ys') >>= (fun _ => 
  guard (sorted zs') >>= (fun _ =>
  guard (all (<= p) ys') >>= (fun _ =>
  guard (all (>= p) zs') >>= (fun _ =>
  Ret (ys' ++ [:: p] ++ zs')))))))).
Proof.
  bind_ext => -[? ?].
  bind_ext => ?.
  bind_ext => ?.
  by rewrite !guard_and !bindA. (* by (6) *)
Qed.

Lemma rev_rev : forall (xs : seq T), rev (rev xs) = xs.
Proof. by induction xs => //; rewrite rev_cons rev_rcons IHxs. Qed.

(* 
Lemma sorted_rev (x y : T) (xs : seq T) :
  sorted (rev (y :: xs)) -> y <= x -> all (<= x) xs -> sorted (rev ([:: x] ++ y :: xs)).
Proof.
  move => h1 h2 h3.
  rewrite rev_cat.
  apply sorted_cat.
  done.
  done.
  move => a ha b hb.
  have h23 : all (<= x) (y :: xs).
  apply sub. apply /andP. done.
  rewrite rev_cons in ha.
  apply: (@le_trans _ _ x).
  move/allP : h3; apply.
  move/allP : ha; apply.
  unfold all. by apply/andP; split.
  auto. *)
End Test.

Section specificationDemo.
Variable M : plusMonad.

(* perm *)
Example perm1 : (@qperm M nat [::]) = Ret [::].
by rewrite qpermE. Qed.
Example perm2 : (@qperm M nat [:: 1]%N) = Ret [:: 1]%N.
by rewrite /= qperm_cons /= bindretf /liftM2 /= qperm_nil 2!bindretf. Qed.
Example perm3 : (@qperm M nat [:: 2; 1]%N) = Ret [:: 1; 2]%N [~] Ret [:: 2; 1]%N.
rewrite qpermE !bindA bindretf alt_bindDl bindretf /liftM2.
by repeat rewrite !qpermE !bindA bindretf !bindretf /=. Qed.
Example perm4 : (@qperm M nat [:: 3; 2; 1]%N) = Ret [:: 1; 2; 3]%N [~] Ret [:: 1; 3; 2]%N [~]
                                                Ret [:: 2; 1; 3]%N [~] Ret [:: 2; 3; 1]%N [~]
                                                Ret [:: 3; 1; 2]%N [~] Ret [:: 3; 2; 1]%N.
rewrite qpermE !bindA.
repeat rewrite bindretf alt_bindDl.
rewrite bindretf /liftM2.
repeat rewrite !qpermE /= !bindA !bindretf !alt_bindDl !bindretf /= !/liftM2.
repeat rewrite !qpermE !bindA bindretf !bindretf /=.
rewrite -altA altACA !altA //. Qed.

(* split *)
Example split1 : (@splits M nat [::]) = Ret ([::], [::]).
by []. Qed.
Example split2 : (@splits M nat [:: 1; 2]%N) =
  Ret ([:: 1; 2]%N, [::]%N) [~] Ret ([:: 2]%N, [:: 1]%N) [~]
  Ret ([:: 1]%N, [:: 2]%N) [~] Ret ([::]%N, [:: 1; 2]%N).
Proof.
rewrite /splits bindA.
repeat rewrite bindretf alt_bindDl !bindretf.
by rewrite altA. 
Qed.

(* sorted *)
Example sorted1 : (@sorted nat (<=%O) [::]%N) = true.
by []. Qed.
Example sorted2 : (@sorted nat (<=%O) [:: 1; 2; 3; 4]%N) = true.
Proof.
rewrite /sorted.
rewrite /path.
rewrite /= //. Qed.
Example sorted3 : (@sorted nat (<=%O) [:: 1; 2; 4; 3]%N) = false.
Proof.
rewrite /sorted /path.
rewrite /= //. Qed.

(* filt *)
Example filt1 : (@assert M _ (sorted <=%O)) [:: 1; 2; 3]%N = Ret ([:: 1; 2; 3]%N).
rewrite /assert /guard /sorted /path /=; unlock.
by rewrite bindskipf. Qed.

Example filt2 : (@assert M _ (sorted <=%O)) [:: 2; 1; 3]%N = fail.
rewrite /sorted /assert /guard /path /=.
unlock.

rewrite bindfailf //. Qed.

Variables (d : unit) (T : porderType d).
(* slowsort *)
Definition bindskipE := (bindskipf, bindmskip).
(* Definition bindfailE := (bindfailf, bindmfail). *)
(* Definition altfailE := (altfailm, altmfail). *)

Ltac sub := repeat rewrite !alt_bindDl !bindretf; rewrite bindA; repeat rewrite !qpermE !bindA !bindretf /=.
Ltac bindSF := rewrite !bindskipf !bindfailf.
Ltac slowsort_process := 
  rewrite /slowsort kleisliE; 
  rewrite !qpermE /bindA /= !bindretf; 
  repeat sub;
  rewrite /sorted /assert /guard /path /=; unlock;
(*  repeat rewrite bindfailE;*)
  repeat rewrite bindskipE(*;
  repeat rewrite altfailE*).

Example slowsort0 : (@slowsort M _ T [::]) = Ret [::].
by slowsort_process.
Qed.

Example slowsort1 : (@slowsort M _ _ [:: 1; 2]%N) = Ret [:: 1; 2]%N.
(*  by slowsort_process.
Qed.*) Abort.

Example slowsort2 : (@slowsort M _ _ [:: 2; 1]%N) = Ret [:: 1; 2]%N.
(*  by slowsort_process.
(* rewrite /slowsort kleisliE.
rewrite !qpermE /bindA /= !bindretf.
repeat sub.
rewrite /sorted /assert /guard /path /=; unlock.
bindSF.
by rewrite altmfail. *)
Qed.*) Abort.

(* Goal (@slowsort M _ _ [:: 2; 1; 3; 4]%N) = Ret [:: 1; 2; 3; 4]%N.
rewrite /slowsort kleisliE.
rewrite !qpermE !bindA /= !bindretf.
repeat sl.
rewrite /assert /sorted /guard /path /=.
unlock.
bindSF.
by rewrite !altfailm !altmfail.
Qed. *)
  
Lemma refin_antisym A (m1 m2 : M A) : (m1 `<=` m2) /\ (m2 `<=` m1) -> m1 = m2.
Proof. 
move => -[h1 h2]. rewrite /refin in h1 h2. rewrite -h2 in h1.
move: h1. rewrite altAC altmm h2 //.
Qed.

Example refin1 : (@qperm M nat [:: 1]%N) `>=` fail -> true.
rewrite /refin.
rewrite qpermE bindretf /liftM2.
repeat rewrite !qpermE bindretf !bindretf /=.
by rewrite altfailm.
Qed.

Example refin2 : (@qperm M nat [:: 1]%N) `>=` Ret [:: 1]%N -> true.
rewrite /refin.
rewrite qpermE bindretf /liftM2.
repeat rewrite !qpermE bindretf !bindretf /=.
by rewrite altmm.
Qed.

Example refin3 : (@qperm M nat [:: 2; 1]%N) `>=` Ret [:: 1; 2]%N -> true.
rewrite /refin.
rewrite qpermE !bindA bindretf alt_bindDl bindretf /liftM2.
repeat rewrite !qpermE !bindA bindretf !bindretf /=.
by rewrite altA altmm altC.
Qed.
    
    (* Definition eq8_sub (p : T) (xs : seq T) : Ret (partition p xs) `<=` ((@splits M T xs) >>= assert (fun '(ys, zs) => all (<= p) ys && all (>= p) zs)). *)
Variables (p : nat).
(* partition *)
Example part1 : partition 1%N [::] = ([::], [::]).
Proof. by []. Qed.
Example part2 : partition 1%N [:: 1; 2]%N = ([:: 1]%N, [:: 2]%N).
Proof. by []. Qed.
(* Example spfilt : (@splits M nat [:: 1; 2]%N) >>= assert (fun '(ys, zs) => all (<= 1%N) ys && all (>= 1%N) zs) = Ret ([:: 1]%N, [:: 2]%N) [~] Ret ([::], [:: 1; 2]%N). *)

    End specificationDemo.