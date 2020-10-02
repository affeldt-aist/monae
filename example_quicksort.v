From mathcomp Require Import all_ssreflect.
From mathcomp Require boolp.
Require Import monae_lib hierarchy monad_lib fail_lib.
From infotheo Require Import ssr_ext.

(******************************************************************************)
(*                            Quicksort example                               *)
(* wip                                                                        *)
(******************************************************************************)

(* TODO: shouldn't preplusmonad be plusmonad (like list monad) and plusmonad be plusCIMonad (like set monad) *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope order_scope.
Import Order.TTheory.
Local Open Scope monae_scope.
Local Open Scope tuple_ext_scope.

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

Lemma qperm_cons x xs :
  qperm (x :: xs) = tsplits xs >>= (fun a => let: (ys, zs) := a in
                    liftM2 (fun a b => a ++ [:: x] ++ b) (qperm ys) (qperm zs)).
Proof.
rewrite {1}/qperm Fix_eq; first by rewrite /=; bind_ext => -[].
move=> s f g H; rewrite /qperm'; case: s f g H => // h t f g H.
bind_ext => -[a b] /=; rewrite /liftM2 H (_ : f = g) //.
apply fun_ext_dep => s.
by rewrite boolp.funeqE=> p; exact: H.
Qed.

End qperm.
Arguments qperm {M} {A}.

Reserved Notation "A `<=` B" (at level 70, no associativity).
Definition refin {M : plusMonad} A (m1 m2 : M A) : Prop := m1 [~] m2 = m2.
Notation "m1 `<=` m2" := (refin m1 m2) : monae_scope.

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

Lemma kleisliE (M : monad) (A B C : UU0) (g : B -> M C) (f : A -> M B) (a : A) :
  (f >=> g) a = (f a) >>= g.
Proof. by rewrite /kleisli /= join_fmap. Qed.

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
  rewrite splitsE /= fmapE bindA; bind_ext => -[a b] /=.
  rewrite bindretf /liftM2 bindA; bind_ext => s.
  by rewrite bindA; bind_ext => s'; rewrite bindretf.
transitivity (splits xs >>= (fun '(ys, zs) =>
    qperm ys >>= (fun ys' => qperm zs >>= (fun zs' =>
    guard ([&& sorted ys', sorted zs', all (<= p) ys' & all (>= p) zs']) >>
    Ret (ys' ++ [:: p] ++ zs')))) : M _).
  bind_ext => -[a b]; bind_ext => s; bind_ext => s'; rewrite assertE /=.
  by rewrite -sorted_cat_cons.
bind_ext=> -[a b].
rewrite guardsC; last exact: (@bindmfail M). (*TODO: put guardsC at the level of failR0Monad *)
rewrite 2!bindA; bind_ext => s.
rewrite assertE bindA guardsC; last exact: (@bindmfail M).
rewrite bindA bindretf assertE 2!bindA guardsC; last exact: (@bindmfail M).
rewrite bindretf 3!bindA; bind_ext => s'.
rewrite assertE bindA 2!bindretf assertE bindA bindretf.
rewrite 2!guard_and assertE 2!bindA.
Admitted.

Fixpoint partition (p : T) (s : seq T) :=
  if s isn't x :: xs then ([::], [::]) else
  let: (ys, zs) := partition p xs in
  if x <= p then (x :: ys, zs) else (ys, x :: zs).

Lemma refin_slowsort (p : T) (xs : seq T) :
  Ret (partition p xs) >>= (fun '(ys, zs) =>
    slowsort ys >>= (fun ys' => slowsort zs >>= (fun zs' => Ret (ys' ++ [:: p] ++ zs'))))
  `<=`
  slowsort (p :: xs).
Proof.
apply/esym.
Abort.

Fail Fixpoint qsort (s : seq T) :=
  if s isn't p :: xs then [::] else
  let: (ys, zs) := partition p xs in
  qsort ys ++ [:: p] ++ qsort zs.

(* TODO: Ret \o qsort `<.=` slowsort by induction on the length of the input list *)

End slowsort.
