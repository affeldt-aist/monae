(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2020 monae authors, license: LGPL-2.1-or-later               *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require boolp.
Require Import monae_lib.
(* From HB Require Import structures. *)
Require Import hierarchy monad_lib fail_lib state_lib.
From infotheo Require Import ssr_ext.

(******************************************************************************)
(*                            Quicksort example                               *)
(*                                                                            *)
(* This file provides a formalization of quicksort on lists as proved in      *)
(* [1, Sect. 4]. The main lemmas is quicksort_slowsort.                       *)
(*                                                                            *)
(*        m1 `<=` m2 == m1 refines m2, i.e., every result of m1 is a possible *)
(*                   result of m2                                             *)
(*         f `<.=` g == refinement relation lifted to functions, i.e.,        *)
(*                      forall x, f x `<=` g x                                *)
(*          splits s == split a list nondeterministically                     *)
(*                      type: seq A -> M (seq A * seq A) with M : plusMonad   *)
(*         tsplits s == same as split with an enriched return type            *)
(*                      M ((size s).-bseq A * (size s).-bseq A))              *)
(*           qperm s == permute the list s                                    *)
(*                      type: seq A -> M (seq A) with M : plusMonad           *)
(* is_partition p (s, t) == elements of s are smaller or equal to p, and      *)
(*                          elements of t are greater of equal to p           *)
(*     partition p s == partitions s into a partition w.r.t. p                *)
(*                      type: T -> seq T -> seq T * seq T                     *)
(*        slowsort s == choose a sorted list among all permutations of s      *)
(*           qsort s == sort s by quicksort                                   *)
(*                      type: seq T -> seq T                                  *)
(* functional_qsort.fqsort == same as qsort but defined with Function         *)
(*                                                                            *)
(* Reference:                                                                 *)
(* - [1] Shin-Cheng Mu, Tsung-Ju Chiang, Declarative Pearl: Deriving Monadic  *)
(*       Quicksort, FLOPS 2020                                                *)
(******************************************************************************)

(* TODO: shouldn't prePlusMonad be plusMonad (like list monad) and
    plusMonad be plusCIMonad (like set monad)? *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory.
Local Open Scope order_scope.

Section sorted.
Variables (d : unit) (T : porderType d).

Lemma sorted_cons (r : rel T) (r_trans : transitive r) x (xs : seq T) :
  sorted r (x :: xs) = sorted r xs && all (r x) xs.
Proof.
apply/idP/idP => [ /= xxs |/andP[ _ /path_min_sorted /= ->//]].
rewrite (order_path_min r_trans xxs) ?andbT//.
exact: path_sorted xxs.
Qed.

Lemma sorted_rcons (r : rel T) (r_trans : transitive r) x (xs : seq T) :
  sorted r (rcons xs x) = sorted r xs && all (r^~ x) xs.
Proof.
rewrite -rev_sorted rev_rcons sorted_cons.
  by rewrite rev_sorted all_rev.
by apply /rev_trans /r_trans.
Qed.

Local Notation sorted := (sorted <=%O).

Lemma sorted_cons' x (xs : seq T) :
  sorted (x :: xs) = sorted xs && all (<=%O x) xs.
Proof. by rewrite sorted_cons //; exact le_trans. Qed.

Lemma sorted_rcons' x (xs : seq T) :
  sorted (rcons xs x) = sorted xs && all (>=%O x) xs.
Proof. by rewrite sorted_rcons //; apply le_trans. Qed.

Lemma sorted_cat' (a b : seq T) : sorted (a ++ b) -> sorted a && sorted b.
Proof.
elim: a b => //= h t ih b; rewrite cat_path => /andP[-> /=].
exact: path_sorted.
Qed.

Lemma sorted_cat_cons' (x : T) (ys zs : seq T) :
  sorted (ys ++ x :: zs) = [&& sorted ys, sorted zs, all (<= x) ys & all (>= x) zs].
Proof.
apply/idP/idP => [|].
  rewrite -cat1s => H; apply/and4P; split; move: H.
  - by move/sorted_cat' => /andP[].
  - by move/sorted_cat'; rewrite sorted_cons' => /and3P[].
  - by rewrite -cat_rcons => /sorted_cat'/andP[]; rewrite sorted_rcons' => /andP[].
  - by move/sorted_cat' => /andP[_]; rewrite sorted_cons' => /andP[].
case/and4P => ss ss' ps ps'; apply sorted_cat => //.
  by rewrite sorted_cons' ss' ps'.
move => a ain b bin; apply (@le_trans _ _ x).
- by move: ps => /allP; apply.
- by move: bin ps'; rewrite inE => /orP[/eqP ->//|] => /allP; apply.
Qed.

End sorted.

Local Open Scope monae_scope.

(* TODO: move *)
Lemma bind_if (M : monad) A B {b : bool} {m : M A} {f g : A -> M B} :
  m >>= (fun x => if b then f x else g x)
  = (if b then (m >>= (fun x => f x))
          else (m >>= (fun x => g x))).
Proof. by case: ifPn. Qed.

Reserved Notation "m1 `<=` m2" (at level 70, no associativity).
Reserved Notation "m2 `>=` m1" (at level 70, no associativity).
Reserved Notation "f `<.=` g" (at level 70, no associativity).

Local Open Scope tuple_ext_scope.
Local Open Scope mprog.
(*Local Notation "m >>= f" := (monae.hierarchy.bind m f).
Local Notation ret x := (monae.hierarchy.ret x).*)

Definition refin (M : altMonad) A (m1 m2 : M A) : Prop := m1 [~] m2 = m2.

Notation "m1 `<=` m2" := (refin m1 m2) : monae_scope.
Notation "m1 `>=` m2" := (refin m2 m1) : monae_scope.

Section refin_lemmas.
Variable M : altCIMonad.

Lemma refin_refl A (a : M A) : a `<=` a.
Proof. by rewrite /refin altmm. Qed.

Lemma refin_trans A (b a c : M A) : a `<=` b -> b `<=` c -> a `<=` c.
Proof. by rewrite /refin => h1 <-; rewrite altA h1. Qed.

Lemma refin_antisym A (a b : M A) : a `<=` b -> b `<=` a -> a = b.
Proof. by rewrite /refin => h1 <-; rewrite altC. Qed.

Lemma refin_alt A (m1 m1' m2 m2' : M A) :
  m1 `<=` m1' -> m2 `<=` m2' -> m1 [~] m2 `<=` m1' [~] m2'.
Proof. by move=> h1 h2; rewrite /refin altACA h1 h2. Qed.

End refin_lemmas.

Lemma refin_guard_le (M : plusMonad) (d : unit) (T : porderType d) (x y : T) :
  total (<=%O : rel T) -> guard (x <= y) `>=` (guard (~~ (y <= x)) : M _).
Proof.
case: guardPn => [nyx|_ _].
  rewrite /total => /(_ x y).
  by rewrite (negbTE nyx) orbF => ->; rewrite guardT; exact: refin_refl.
by rewrite /refin altfailm.
Qed.

Definition lrefin {M : altMonad} A B (f g : A -> M B) := forall x, f x `<=`g x.

Notation "f `<.=` g" := (lrefin f g) : monae_scope.

Section lrefin_lemmas.
Variable M : altCIMonad.

Lemma lrefin_refl A B (a : A -> M B) : a `<.=` a.
Proof. by move => ?; exact: refin_refl. Qed.

Lemma lrefin_trans A B (b a c : A -> M B) : a `<.=` b -> b `<.=` c -> a `<.=` c.
Proof. by move => ? ? ?; exact: refin_trans. Qed.

Lemma lrefin_antisym A B (a b : A -> M B) : a `<.=` b -> b `<.=` a -> a = b.
Proof. move => ? ?; rewrite boolp.funeqE => ?; exact: refin_antisym. Qed.

End lrefin_lemmas.

Lemma refin_bindr (M : altMonad) A B (m1 m2 : M A) (f : A -> M B) :
  (m1 `<=` m2) -> (m1 >>= f `<=` m2 >>= f).
Proof. by move=> m12; rewrite /refin -alt_bindDl m12. Qed.

Lemma refin_bindl (M : prePlusMonad) A B (m : M A) (f g : A -> M B) :
  (f `<.=` g) -> (m >>= f `<=` m >>= g).
Proof. by move=> fg; rewrite /refin -alt_bindDr; bind_ext => a; exact: fg. Qed.

Lemma refin_bind (M : plusMonad) A B {m n : M A} {f g : A -> M B} :
  m `<=` n -> f `<.=` g -> (m >>= f) `<=` (n >>= g).
Proof.
by move=> mn /refin_bindl ?; exact: (refin_trans _ (refin_bindr _ mn)).
Qed.

Lemma refin_liftM2 (M : plusMonad) A B C {f : A -> B -> C} {m1 n1 : M A} {m2 n2 : M B} :
  m1 `<=` n1 -> m2 `<=` n2 -> liftM2 f m1 m2 `<=` liftM2 f n1 n2.
Proof.
move=> mn1 mn2; rewrite /liftM2.
by apply: (refin_bind mn1 _) => a; exact: refin_bindr.
Qed.

Lemma guard_neg (M : plusMonad) A (p : bool) (m1 m2 : M A) :
  (if p then m1 else m2) `<=` (guard p >> m1) [~] (guard (~~ p) >> m2).
Proof.
rewrite /refin; case: ifPn => /= [pT|pF]; rewrite !(guardT,guardF).
by rewrite bindskipf bindfailf altA altmm.
by rewrite bindfailf bindskipf altCA altmm.
Qed.

Section splits.
Variable M : plusMonad.
Variables (d : unit) (T : porderType d).

Fixpoint splits {M : plusMonad} A (s : seq A) : M (seq A * seq A)%type :=
  if s isn't x :: xs then Ret ([::], [::]) else
    splits xs >>= (fun yz => Ret (x :: yz.1, yz.2) [~] Ret (yz.1, x :: yz.2)).

Lemma leq_bseq_size A (xs : seq A) (b0 : (size xs).-bseq A) :
  (size b0 <= (size xs).+1)%N.
Proof. by rewrite (leq_trans (size_bseq b0)). Qed.

Fixpoint tsplits {M : plusMonad} A (s : seq A)
    : M ((size s).-bseq A * (size s).-bseq A)%type :=
  if s isn't x :: xs then Ret ([bseq of [::]], [bseq of [::]])
  else tsplits xs >>= (fun '(ys, zs) =>
    Ret ([bseq of x :: ys], widen_bseq (leqnSn _) zs) [~]
    Ret (widen_bseq (leqnSn _) ys, [bseq of x :: zs])).

Local Lemma splits_nat_nil : @splits M nat [::] = Ret ([::], [::]).
Proof. by []. Abort.

Local Lemma splits_nat_01 : @splits M _ [:: O; 1]%nat = Ret ([::], [::]).
Proof. rewrite /= bindretf alt_bindDl !bindretf /=. Abort.

Local Open Scope mprog.
Lemma splitsE A (s : seq A) :
  splits s =
  fmap (fun '(ys, zs) => (bseqval ys, bseqval zs)) (tsplits s) :> M _.
Proof.
elim: s => /= [|h t ih]; first by rewrite fmapE bindretf.
rewrite {}ih /= !fmapE 2!bindA; bind_ext => -[a b] /=.
by rewrite bindretf alt_bindDl 2!bindretf.
Qed.
Local Close Scope mprog.

End splits.

Section qperm.
Variables (M : plusMonad) (A : UU0).
Variables (d : unit) (T : porderType d).

Require Import Recdef.
Fail Function qperm (s : seq A) {measure size s} : M (seq A) :=
  if s isn't x :: xs then Ret [::] else
    splits xs >>= (fun '(ys, zs) => liftM2 (fun a b => a ++ x :: b) (qperm ys) (qperm zs)).

Local Obligation Tactic := idtac.
Program Definition qperm' (s : seq A)
    (f : forall s', size s' < size s -> M (seq A)) : M (seq A) :=
  if s isn't x :: xs then Ret [::] else
    tsplits xs >>= (fun '(ys, zs) => liftM2 (fun a b => a ++ x :: b) (f ys _) (f zs _)).
Next Obligation.
move=> [|h t] // ht x xs [xh xst] [a b] ys _ _ .
by apply: (leq_ltn_trans (size_bseq ys)); rewrite xst.
Qed.
Next Obligation.
move=> [|h t] // ht x xs [xh xst] [a b] _ zs _.
by apply: (leq_ltn_trans (size_bseq zs)); rewrite xst.
Qed.
Next Obligation. by []. Qed.

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
  qperm (x :: xs) = splits xs >>= (fun '(ys, zs) =>
                    liftM2 (fun a b => a ++ x :: b) (qperm ys) (qperm zs)).
Proof.
rewrite {1}/qperm {1}(Fix_eq _ _ _ qperm'_Fix) /=.
rewrite splitsE /= fmapE bindA; bind_ext => -[s1 s2] /=.
by rewrite bindretf.
Qed.

Definition qpermE := (qperm_nil, qperm_cons).

End qperm.
Arguments qperm {M} {A}.

Section guard_commute.
Variable M : plusMonad.
Variables (d : unit) (T : porderType d).

(* NB: on the model of nondetState_sub in state_lib.v *)
Definition nondetPlus_sub (M : plusMonad) A (n : M A) :=
  {m | ndDenote m = n}.

Lemma commute_plus
  A (m : M A) B (n : M B) C (f : A -> B -> M C) :
  nondetPlus_sub m -> commute m n f.
Proof.
case => x.
elim: x m n f => [{}A a m n f <-| B0 {}A n0 H0 n1 H1 m n2 f <- |
  A0 m n f <- | A0 n0 H0 n1 H1 m n2 f <-].
- rewrite /commute bindretf.
  by under [RHS] eq_bind do rewrite bindretf.
- rewrite /commute /= !bindA.
  transitivity (do x <- ndDenote n0; do y <- n2; ndDenote (n1 x) >>= f^~ y)%Do.
    bind_ext => s.
    by rewrite (H1 s).
  rewrite H0 //.
  bind_ext => b.
  by rewrite bindA.
- rewrite /commute /= bindfailf.
  transitivity (n >> fail : M C).
    by rewrite (@bindmfail M).
  bind_ext => b.
  by rewrite (@bindfailf M).
- rewrite /commute /= alt_bindDl.
  transitivity (do y <- n2; ndDenote n0 >>= f^~ y [~]
                          ndDenote n1 >>= f^~ y)%Do; last first.
    bind_ext => a.
    by rewrite alt_bindDl.
  by rewrite alt_bindDr H0 // H1.
Qed.

Lemma commute_guard_n (b : bool) B (n : M B) C (f : unit -> B -> M C) :
  commute (guard b) n f.
Proof.
apply commute_plus; exists (if b then ndRet tt else @ndFail _).
by case: ifP; rewrite (guardT, guardF).
Qed.

Lemma guard_splits A (p : pred T) (t : seq T) (f : seq T * seq T -> M A) :
  guard (all p t) >> (splits t >>= f) =
  splits t >>= (fun x => guard (all p x.1) >> guard (all p x.2) >> f x).
Proof.
elim: t p A f => [p A f|h t ih p A f].
  by rewrite /= 2!bindretf /= guardT bindmskip.
rewrite /= guard_and !bindA ih -bindA.
rewrite [in RHS]bindA -[in LHS]bindA. (* TODO : not robust *)
rewrite (@guardsC M (@bindmfail M) _).
rewrite bindA.
bind_ext => -[a b] /=.
rewrite assertE bindA bindretf bindA /=.
rewrite [in RHS]alt_bindDl /=.
do 2 rewrite bindretf /= guard_and !bindA.
rewrite -!bindA.
rewrite [in RHS](@guardsC M (@bindmfail M) (all p a)).
rewrite !bindA -alt_bindDr.
bind_ext; case; rewrite assertE bindmskip -[in RHS]alt_bindDr.
by bind_ext; case; rewrite alt_bindDl /= 2!bindretf -alt_bindDr.
Qed.

Lemma guard_splits' A (p : pred T) (t : seq T) (f : seq T * seq T -> M A) :
  splits t >>= (fun x => guard (all p t) >> f x) =
  splits t >>= (fun x => (guard (all p x.1) >> guard (all p x.2)) >> f x).
Proof.
rewrite -guard_splits (@guardsC M (@bindmfail M) _) bindA.
by bind_ext => -[a b]; rewrite guardsC; last exact : (@bindmfail M).
Abort.

Lemma guard_splits_cons A h (p : pred T) (t : seq T) (f : seq T * seq T -> M A) :
  guard (all p (h :: t)) >> (splits t >>= f)
  =
  splits t >>= (fun x => guard (all p x.1) >>
                         guard (all p x.2) >>
                         guard (p h) >> f x).
Proof.
rewrite /= guard_and bindA guard_splits commute_guard_n.
bind_ext => -[a b] /=.
by rewrite -bindA -!guard_and andbC.
Qed.

Lemma guard_qperm_eq B (p : pred T) (a : seq T) (f : seq T -> M B) :
  guard (all p a) >>= (fun _ => qperm a >>= f) =
  qperm a >>= (fun x => guard (all p x) >> f x).
Proof.
move: p.
have [n leMn] := ubnP (size a); elim: n => // n ih in a f leMn *.
case: a leMn => [|h t].
  by move=> _ p; rewrite /= qperm_nil 2!bindretf.
rewrite ltnS => tn p.
rewrite qperm_cons {1}/liftM2 !bindA /= guard_and [in LHS]bindA.
rewrite -bindA -guard_and.
rewrite guard_splits_cons /liftM2.
rewrite splitsE /= fmapE !bindA /=.
bind_ext => -[a b] /=.
rewrite 2!bindretf /=.
(* transitivity (
  ((guard (all p b) >> guard (p h)) >> guard (all p a) >>
  (do x <- do x1 <- qperm a; do x2 <- qperm b; Ret (x1 ++ h :: x2); f x)%Do)
  ). *)
rewrite -2!guard_and andbC andbA andbC andbA 2!guard_and !bindA.
rewrite ih; last by rewrite (leq_trans _ tn) //= ltnS size_bseq.
(* transitivity (
  (do x0 <- qperm a; ((guard (p h) >> guard (all p x0)) >> guard (all p b))
  >> (do x1 <- do x2 <- qperm b; Ret (x0 ++ h :: x2); f x1)%Do)%Do
). *)
rewrite -bindA -guard_and commute_guard_n.
bind_ext => ?.
rewrite -bindA -guard_and andbC andbA andbC andbA 2!guard_and !bindA.
rewrite ih; last by rewrite (leq_trans _ tn) //= ltnS size_bseq.
(* transitivity (
  (do x2 <- qperm b; ((guard (p h) >> guard (all p x0)) >> guard (all p x2)) >>
  (do x3 <- Ret (x0 ++ h :: x2); f x3)%Do)%Do
). *)
rewrite -bindA -guard_and commute_guard_n.
bind_ext => ?.
by rewrite -bindA -!guard_and 2!bindretf -all_rcons -cat_rcons all_cat.
Qed.

Lemma guard_qperm_neq B (b a : seq T) (r : pred T) (f : seq T -> M B) :
  guard (all r b) >> (qperm a >>= f) =
  qperm a >>= (fun x => (guard (all r b) >> f x)).
Proof. by rewrite commute_guard_n. Qed.

End guard_commute.

Section partition.
Variable M : plusMonad.
Variables (d : unit) (T : porderType d).

Definition is_partition p (yz : seq T * seq T) :=
  all (<= p) yz.1 && all (>= p) yz.2.

Lemma is_partition_consL p x (ys zs : seq T) :
  is_partition p (x :: ys, zs) = (x <= p) && is_partition p (ys, zs).
Proof. by rewrite /is_partition /= andbA. Qed.

Lemma is_partition_consR p x (ys zs : seq T) :
  is_partition p (ys, x :: zs) = (x >= p) && is_partition p (ys, zs).
Proof. by rewrite /is_partition /= andbCA. Qed.

Definition is_partition_consE := (is_partition_consL, is_partition_consR).

Fixpoint partition p (s : seq T) : seq T * seq T :=
  if s isn't x :: xs then ([::], [::]) else
  let: yz := partition p xs in
  if x <= p then (x :: yz.1, yz.2) else (yz.1, x :: yz.2).

Lemma size_partition p (s : seq T) :
  size (partition p s).1 + size (partition p s).2 = size s.
Proof.
elim: s p => //= x xs ih p; have {ih} := ih p.
move H : (partition p xs) => h; case: h H => a b ab /= abxs.
by case: ifPn => xp /=; rewrite ?(addSn,addnS) abxs.
Qed.

Lemma refin_partition (p : T) (xs : seq T) :
  total (<=%O : rel T) ->
  (Ret (partition p xs) : M (seq T * seq T)%type (*TODO: :> notation for `<=`?*))
  `<=`
  splits xs >>= assert (is_partition p).
Proof.
move => t.
elim: xs p => [p /=|x xs ih p].
  by rewrite /is_partition bindretf /refin /= !assertE !all_nil /= guardT bindskipf altmm.
rewrite /=.
rewrite bindA.
under eq_bind do rewrite alt_bindDl 2!bindretf 2!assertE.
under eq_bind do rewrite 2!is_partition_consE 2!guard_and 2!bindA.
apply: (@refin_trans _ _ _); last first.
  apply: refin_bindl => x0.
  apply: (refin_alt (refin_refl _)).
  apply: refin_bindr.
  exact: (refin_guard_le _ _ _ t).
apply: (@refin_trans _ _ _); last first.
  apply: refin_bindl => x1.
  exact: guard_neg.
under eq_bind do rewrite -bind_if.
apply: (@refin_trans _ _ (
  (do a <- splits xs;
  guard (is_partition p a) >> (Ret a >>= (fun a =>
  (if x <= p then Ret (x :: a.1, a.2) else Ret (a.1, x :: a.2)))))%Do)); last first.
  rewrite /refin -alt_bindDr.
  bind_ext => -[? ?] /=.
  by rewrite bindretf /= (altmm (_ : M _)).
under eq_bind do rewrite -bindA -assertE.
rewrite -bindA.
apply: (@refin_trans _ _ _); last exact/refin_bindr/ih.
rewrite bindretf.
by case: ifPn => xp; exact: refin_refl.
Qed.

End partition.

Section slowsort.
Variable M : plusMonad.
Variables (d : unit) (T : porderType d).

Local Notation sorted := (sorted <=%O).

Definition slowsort : seq T -> M (seq T) := (qperm >=> assert sorted).

Lemma slowsort_nil : slowsort [::] = Ret [::].
Proof.
rewrite /slowsort.
by rewrite kleisliE qpermE bindretf assertE guardT bindskipf.
Qed.

Lemma refin_slowsort_inductive_case (p : T) (xs : seq T) :
  slowsort (p :: xs) =
  splits xs >>= (fun yz => guard (is_partition p yz) >>
    (qperm yz.1 >>= assert sorted) >>= (fun ys' =>
    (qperm yz.2 >>= assert sorted) >>= (fun zs' =>
    Ret (ys' ++ p :: zs')))).
Proof.
transitivity (
  splits xs >>= (fun '(ys, zs) =>
  qperm ys >>= (fun ys' => qperm zs >>= (fun zs' =>
  assert sorted (ys' ++ p :: zs')))) : M _).
  rewrite /slowsort kleisliE qperm_cons !bindA.
  bind_ext => -[a b] /=.
  rewrite /liftM2 bindA; bind_ext => s.
  by rewrite bindA; bind_ext => s'; rewrite bindretf.
transitivity (
  splits xs >>= (fun '(ys, zs) =>
  qperm ys >>= (fun ys' => qperm zs >>= (fun zs' =>
  guard ([&& sorted ys', sorted zs', all (<= p) ys' & all (>= p) zs']) >>
  Ret (ys' ++ p :: zs')))) : M _).
  bind_ext => -[a b]; bind_ext => s; bind_ext => s'; rewrite assertE /=.
  by rewrite -sorted_cat_cons'.
bind_ext=> {xs} -[a b].
rewrite guard_and 2!bindA (bindA (qperm a)).
rewrite guard_qperm_neq.
rewrite guard_qperm_eq.
bind_ext => s.
under [LHS]eq_bind do rewrite 3!guard_and.
transitivity (
  qperm b >>= (fun x =>
  guard (all (>= p) x) >> (guard (all (<= p) s) >>
  (guard (sorted x) >> ((guard (sorted s)) >> Ret (s ++ p :: x)))) : M _)).
  bind_ext => s'.
  rewrite -!bindA -!guard_and.
  by rewrite andbC (andbC _ (all (<= p) s)) (andbC (sorted s)) !andbA.
rewrite -guard_qperm_eq.
rewrite -[in RHS]bindA -guard_and andbC guard_and bindA.
congr (_ >> _).
rewrite boolp.funeqE => ?.
rewrite -guard_qperm_neq.
bind_ext; case.
under [RHS]eq_bind do rewrite bindA.
rewrite assertE bindA bindretf (@guardsC M (@bindmfail M)) bindA.
bind_ext => ?.
by rewrite assertE !bindA 2!bindretf assertE.
Qed.

Lemma refin_slowsort (p : T) (xs : seq T) :
  (total (<=%O : rel T)) ->
  slowsort (p :: xs) `>=`
  Ret (partition p xs) >>= (fun '(ys, zs) =>
    slowsort ys >>= (fun ys' => slowsort zs >>= (fun zs' => Ret (ys' ++ p :: zs'))) : M _).
Proof.
move => hyp.
rewrite [X in X `>=` _]refin_slowsort_inductive_case.
rewrite [X in X `>=` _](_ : _ = splits xs >>=
    (fun yz => assert (is_partition p) yz) >>=
    fun '(ys, zs) => (slowsort ys) >>=
    (fun ys' => (slowsort zs) >>= (fun zs'=> Ret (ys' ++ p :: zs')))); last first.
  rewrite bindA; bind_ext => -[s1 s2];rewrite !bindA assertE bindA; congr (_ >> _).
  by rewrite boolp.funeqE => -[] /=; rewrite bindretf /slowsort 2!kleisliE bindA.
exact/refin_bindr/(refin_partition M p xs hyp).
Qed.

End slowsort.
Arguments slowsort {M} {_} {_}.

Section qsort.
Variable M : plusMonad.
Variables (d : unit) (T : porderType d).

Program Fixpoint qsort' (s : seq T)
    (f : forall s', (size s' < size s)%N -> seq T) : seq T :=
  if s isn't p :: xs then [::] else
  let: (ys, zs) := partition p xs in
  f ys _ ++ p :: f zs _.
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
                    qsort ys ++ p :: qsort zs.
Proof.
rewrite [in LHS]/qsort Fix_eq /=; last exact: qsort'_Fix.
by move s12 : (partition p xs) => h; case: h s12.
Qed.

Definition qsortE := (qsort_nil, qsort_cons).

Lemma quicksort_slowsort : total (<=%O : rel T) ->
  Ret \o qsort `<.=` (slowsort : _ -> M _).
Proof.
move=> hyp s.
have [n sn] := ubnP (size s); elim: n => // n ih in s sn *.
case: s => [|h t] in sn *.
  by rewrite /= qsort_nil slowsort_nil; exact: refin_refl.
rewrite ltnS /= in sn.
rewrite /= qsort_cons.
move pht : (partition h t) => ht; case: ht pht => ys zs pht.
apply: (refin_trans _ (refin_slowsort M h t hyp)).
rewrite bindretf pht.
rewrite -(ih ys); last first.
  by rewrite (leq_trans _ sn)// ltnS -(size_partition h t) pht leq_addr.
rewrite -(ih zs); last first.
  by rewrite (leq_trans _ sn)// ltnS -(size_partition h t) pht leq_addl.
do 2 rewrite alt_bindDl bindretf.
by rewrite /refin !altA altmm. (* TODO: needs lemma *)
Qed.

End qsort.

Example qsort_nat :
  qsort [:: 3; 42; 230; 1; 67; 2]%N = [:: 1; 2; 3; 42; 67; 230]%N.
Proof. by repeat rewrite qsortE //=. Abort.

Example qsort_sort :
  let s := [:: 3; 42; 230; 1; 67; 2]%N in qsort s = sort ltn s.
Proof.
move=> s; rewrite /s sortE /=.
by repeat rewrite qsortE /=.
Abort.

(* NB: experiment with a version of qsort written with Function *)
Module functional_qsort.
Require Import Recdef.
From mathcomp Require Import ssrnat.
Section qsort_def.
Variables (M : plusMonad).
Variables (d : unit) (T : porderType d).
Function fqsort (s : seq T) {measure size s} : seq T :=
  (* if s isn't h :: t then [::]
  else let: (ys, zs) := partition h t in
       fqsort ys ++ h :: fqsort zs. *)
  (* NB: not using match causes problems when applying fqsort_ind
     which is automatically generated *)
  match s with
  | [::] => [::]
  | h :: t => let: (ys, zs) := partition h t in
              fqsort ys ++ h :: fqsort zs
  end.
Proof.
move=> s h t sht ys zs H.
have := size_partition h t.
by rewrite H /= => <-; apply/ltP; rewrite ltnS leq_addl.
move=> s h t sht ys zs H.
have := size_partition h t.
by rewrite H /= => <-; apply/ltP; rewrite ltnS leq_addr.
Defined.

Definition partition_slowsort (xs : seq T) : M (seq T) :=
  if xs isn't h :: t then Ret [::] else
  let: (ys, zs) := partition h t in
  liftM2 (fun a b => a ++ h :: b) (slowsort ys) (slowsort zs).

Lemma refin_partition_slowsort : total (<=%O : rel T) ->
  partition_slowsort `<.=` slowsort.
Proof.
move => hyp [|p xs]; first by rewrite slowsort_nil; exact: refin_refl.
rewrite [X in X `>=` _]refin_slowsort_inductive_case.
rewrite [X in X `>=` _](_ : _ = splits xs >>=
    (fun yz => assert (is_partition p) yz) >>=
    fun '(ys, zs) => slowsort ys >>=
    (fun ys' => slowsort zs >>= (fun zs'=> Ret (ys' ++ p :: zs')))); last first.
  rewrite bindA; bind_ext => -[s1 s2];rewrite !bindA assertE bindA.
  bind_ext => -[] /=.
  by rewrite bindretf /slowsort 2!kleisliE bindA.
rewrite /=.
apply: refin_trans; last exact/refin_bindr/refin_partition.
by rewrite bindretf; exact: refin_refl.
Qed.

Lemma refin_fqsort : (total (<=%O : rel T)) ->
  Ret \o fqsort `<.=` (slowsort : seq T -> M _).
Proof.
move=> hyp s => /=.
apply fqsort_ind => [s0 _|s0 h t sht ys zs pht ihys ihzs].
(* apply fqsort_ind => [s0 h t sht ys zs pht ihys ihzs|s0 x sx H]; last first. *)
  by rewrite slowsort_nil; exact: refin_refl.
apply: (refin_trans _ (refin_partition_slowsort hyp _)).
rewrite /= pht.
apply: refin_trans; last exact: (refin_liftM2 ihys ihzs).
rewrite /liftM2 2!bindretf. (*TODO: lemma*)
exact: refin_refl.
Qed.

End qsort_def.

Example qsort_nat :
  fqsort [:: 3; 42; 230; 1; 67; 2]%N = [:: 1; 2; 3; 42; 67; 230]%N.
Proof.
do 4 rewrite fqsort_equation /=.
reflexivity.
Qed.

Eval compute in qsort [:: 3; 42; 230; 1; 67; 2]%N.
Eval compute in fqsort [:: 3; 42; 230; 1; 67; 2]%N.

End functional_qsort.
