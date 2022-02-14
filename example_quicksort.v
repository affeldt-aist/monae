(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2020 monae authors, license: LGPL-2.1-or-later               *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require boolp.
Require Import monae_lib.
Require Import hierarchy monad_lib fail_lib state_lib.
From infotheo Require Import ssr_ext.
Require Import Recdef.

(******************************************************************************)
(*                            Quicksort example                               *)
(*                                                                            *)
(* This file provides a formalization of quicksort on lists as proved in      *)
(* [1, Sect. 4]. The main lemmas is quicksort_slowsort.                       *)
(*                                                                            *)
(* is_partition p (s, t) == elements of s are smaller or equal to p, and      *)
(*                          elements of t are greater of equal to p           *)
(*         partition p s == partitions s into a partition w.r.t. p            *)
(*                          type: T -> seq T -> seq T * seq T                 *)
(*            slowsort s == choose a sorted list among all permutations of s  *)
(*               qsort s == sort s by quicksort                               *)
(*                          type: seq T -> seq T                              *)
(*                                                                            *)
(* Reference:                                                                 *)
(* - [1] Shin-Cheng Mu, Tsung-Ju Chiang, Declarative Pearl: Deriving Monadic  *)
(*       Quicksort, FLOPS 2020                                                *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory.
Local Open Scope order_scope.

From mathcomp Require Import ssrnat.

Section sorted.
Variables (d : unit) (T : orderType d).

Local Notation sorted := (sorted <=%O).

Lemma sorted_cat_cons (x : T) (ys zs : seq T) :
  sorted (ys ++ x :: zs) = [&& sorted ys, sorted zs, all (<= x) ys & all (>= x) zs].
Proof.
apply/idP/idP => [|].
elim: ys => /= [|h t ih]; first by rewrite le_path_sortedE andbC.
rewrite !le_path_sortedE all_cat.
by move=> /andP[/andP[-> /= /andP[-> _]] hs]; move: (ih hs) => ->.
case/and4P => ss ss' ps ps'; apply (@sorted_cat _) => // /=.
by rewrite le_path_sortedE ss' ps'.
move => a ain b bin; apply: le_trans.
- by move: ps => /allP; apply.
- by move: bin ps'; rewrite inE => /orP[/eqP ->//|] => /allP; apply.
Qed.

End sorted.

Local Open Scope monae_scope.
Local Open Scope tuple_ext_scope.
Local Open Scope mprog.

(* TODO: move *)
Section guard_qperm.
Variable M : plusMonad.
Variables (d : unit) (T : orderType d).

Lemma guard_splits A (p : pred T) (t : seq T) (f : seq T * seq T -> M A) :
  splits t >>= (fun x => guard (all p t) >> f x) =
  splits t >>= (fun x => guard (all p x.1) >> guard (all p x.2) >> f x).
Proof.
rewrite -commute_plus_guard.
elim: t => [|h t ih] in p A f *; first by rewrite 2!bindretf guardT bindmskip.
rewrite [LHS]/= guard_and 2!bindA ih /= commute_plus_guard bindA.
bind_ext => -[a b] /=.
rewrite !alt_bindDl !bindretf /= !guard_and !bindA !alt_bindDr.
by congr (_ [~] _); rewrite commute_plus_guard.
Qed.

(* NB: corresponds to perm-preserves-all? *)
Lemma guard_all_qperm B (p : pred T) s (f : seq T -> M B) :
  qperm s >>= (fun x => guard (all p s) >> f x) =
  qperm s >>= (fun x => guard (all p x) >> f x).
Proof.
rewrite -commute_plus_guard.
have [n leMn] := ubnP (size s); elim: n => // n ih in s f leMn *.
case: s leMn => [|h t]; first by move=> _; rewrite qperm_nil !bindretf.
rewrite ltnS => tn.
rewrite qperm_cons !bindA /= guard_and bindA (commute_plus_guard (all p t)).
rewrite guard_splits splitsE fmapE 2!bindA commute_plus_guard.
bind_ext => -[a b]; rewrite 2!bindretf !bindA /=.
rewrite (commute_plus_guard (all p b)).
rewrite ih; last by rewrite (leq_trans _ tn) //= ltnS size_bseq.
rewrite (commute_plus_guard (p h)).
bind_ext => a'; rewrite !bindA (commute_plus_guard (p h)).
rewrite ih; last by rewrite (leq_trans _ tn) //= ltnS size_bseq.
rewrite (commute_plus_guard (p h)) commute_plus_guard.
bind_ext => b'; rewrite !bindretf all_cat /= andbA andbAC !guard_and !bindA.
by under eq_bind do rewrite commute_plus_guard.
Qed.

End guard_qperm.

Section partition.
Variables (M : plusMonad) (d : unit) (T : orderType d).

Definition is_partition p (yz : seq T * seq T) :=
  all (<= p) yz.1 && all (>= p) yz.2.

Lemma is_partition_consL p x (ys zs : seq T) :
  is_partition p (x :: ys, zs) = (x <= p) && is_partition p (ys, zs).
Proof. by rewrite /is_partition andbA. Qed.

Lemma is_partition_consR p x (ys zs : seq T) :
  is_partition p (ys, x :: zs) = (x >= p) && is_partition p (ys, zs).
Proof. by rewrite /is_partition andbCA. Qed.

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
by case: ifPn => xp; rewrite ?(addSn,addnS) abxs.
Qed.

Lemma partition_spec (p : T) (xs : seq T) :
  ((@ret M _) \o partition p) xs `<=` splits xs >>= assert (is_partition p).
Proof.
elim: xs p => [/=|x xs ih] p.
  rewrite bindretf !assertE /is_partition guardT bindskipf; exact: refin_refl.
rewrite /= bindA.
under eq_bind do rewrite alt_bindDl 2!bindretf 2!assertE.
under eq_bind do rewrite 2!is_partition_consE 2!guard_and 2!bindA.
apply: (refin_trans _ (refin_bindl _ _)); last first => [yz|].
  exact/(refin_alt (refin_refl _))/refin_bindr/refin_guard_le.
apply: (refin_trans _ (refin_bindl _ _)); last first => [yz|].
  exact: refin_if_guard.
under eq_bind do rewrite -bind_if.
apply: (@refin_trans _ _ (splits xs >>=
  fun a => guard (is_partition p a) >> (Ret a >>=
  fun a => (if x <= p then Ret (x :: a.1, a.2)
    else Ret (a.1, x :: a.2))))); last first.
  apply: refin_bindl => ?; apply: refin_bindl => ?.
  rewrite bindretf; exact: refin_refl.
under eq_bind do rewrite -bindA -assertE.
rewrite -bindA; apply: (refin_trans _ (refin_bindr _ (ih _))).
rewrite bindretf; case: ifPn => ?; exact: refin_refl.
Qed.

End partition.

Section slowsort.
Variables (M : plusMonad) (d : unit) (T : orderType d).

Local Notation sorted := (sorted <=%O).

Definition slowsort : seq T -> M (seq T) := (qperm >=> assert sorted).

Lemma slowsort_nil : slowsort [::] = Ret [::].
Proof.
by rewrite /slowsort kleisliE qpermE bindretf assertE guardT bindskipf.
Qed.

Lemma slowsort_cons p xs : slowsort (p :: xs) =
  splits xs >>= (fun '(ys, zs) => qperm ys >>=
    (fun ys' => qperm zs >>= (fun zs' => assert sorted (ys' ++ p :: zs')))).
Proof.
rewrite /slowsort kleisliE qperm_cons bindA.
by bind_ext => -[a b]; rewrite liftM2E.
Qed.

Lemma slowsort_splits p s : slowsort (p :: s) =
  splits s >>= (fun x => guard (is_partition p x) >>
  slowsort x.1 >>= (fun a => slowsort x.2 >>= (fun b => Ret (a ++ p :: b)))).
Proof.
rewrite slowsort_cons; bind_ext=> {s} -[a b].
rewrite /is_partition /slowsort !kleisliE.
rewrite guard_and !bindA (commute_plus_guard (all (>= p) b)) commute_plus_guard.
rewrite guard_all_qperm.
bind_ext=> a'; rewrite commute_plus_guard assertE bindA bindretf bindA.
rewrite (commute_plus_guard (sorted a')).
rewrite (commute_plus_guard (all (<= p) a')) commute_plus_guard guard_all_qperm.
bind_ext=> b'; rewrite commute_plus_guard !assertE bindA bindretf.
by rewrite sorted_cat_cons andbC -!andbA andbC !guard_and !bindA.
Qed.

Lemma refin_partition_slowsort p s :
  Ret (partition p s) >>= (fun '(a, b) =>
  slowsort a >>= (fun a' => slowsort b >>= (fun b' => Ret (a' ++ p :: b'))))
  `<=`
  (slowsort (p :: s) : M _).
Proof.
rewrite slowsort_splits.
apply: refin_trans; first exact/refin_bindr/(partition_spec M p s).
rewrite bindA; apply: refin_bindl => -[a b].
rewrite assertE (bindA _ (fun _ => Ret (a, b))) bindretf /= bindA.
exact: refin_refl.
Qed.

Lemma nondetPlus_sub_slowsort s : nondetPlus_sub (slowsort s : M _).
Proof.
rewrite /slowsort kleisliE.
have [syn syn_qperm] := @nondetPlus_sub_qperm M _ s.
exists (ndBind syn (fun a => ndBind
  (if sorted a then ndRet tt else ndFail unit)
  (fun _ : unit => ndRet a))).
rewrite /= syn_qperm; bind_ext => s'.
case: ifPn => sorteds'.
  by rewrite /= bindretf assertE sorteds' guardT bindskipf.
by rewrite /= assertE (negbTE sorteds') guardF bindfailf.
Qed.

Lemma qperm_slowsort : (qperm >=> slowsort) = slowsort :> (seq T -> M (seq T)).
Proof. by rewrite /slowsort -kleisliA qperm_idempotent. Qed.

End slowsort.
Arguments slowsort {M} {_} {_}.

Section slowsort_example.
Variable M : plusMonad.

Let bindskipE := (bindskipf, bindmskip).

Ltac sub := repeat rewrite !alt_bindDl !bindretf;
            rewrite bindA;
            repeat rewrite !qpermE !bindA !bindretf /=.
Ltac bindSF := rewrite !bindskipf !bindfailf.

Variables (d : unit) (T : orderType d).

Example slowsort2 : @slowsort M _ _ [:: 2; 1]%N = Ret [:: 1; 2]%N.
Proof.
rewrite /slowsort kleisliE.
rewrite !qpermE /bindA /= !bindretf.
repeat sub.
rewrite /sorted /assert /guard /path /=; unlock.
bindSF.
by rewrite altmfail.
Qed.

End slowsort_example.

Section slowsort_preserves.
Context (M : plusMonad) {d : unit} {E : orderType d}.

Let slowsort_preserves_size : preserves (@slowsort M _ E) size.
Proof.
move=> s; have [n ns] := ubnP (size s); elim: n s ns => // n ih s ns.
move: s ns => [ns|p s]; first by rewrite /= slowsort_nil 2!bindretf.
rewrite /= ltnS => ns; rewrite /slowsort kleisliE !bindA.
rewrite (qperm_preserves_size2 _
  (fun a b => assert (sorted <=%O) a >>= (fun x' => Ret (x', b)))).
bind_ext => ht; rewrite assertE 2!bindA; apply: bind_ext_guard => _.
by rewrite 2!bindretf.
Qed.

Lemma slowsort_preserves_size2 (x : seq E) B (f : seq E -> nat -> M B) :
  (slowsort x >>= fun x' => f x' (size x)) =
  (slowsort x >>= fun x' => f x' (size x')) :> M _.
Proof.
transitivity (slowsort x >>= (fun y => Ret (y, size y)) >>= (fun z => f z.1 z.2)).
  by rewrite slowsort_preserves_size bindA; bind_ext => s; rewrite bindretf.
by rewrite bindA; bind_ext => s; rewrite bindretf.
Qed.

Lemma bind_slowsort_guard (s : seq E) B (f : seq E -> M B) :
  (slowsort s >>= f) = slowsort s >>= (fun x => guard (size s == size x) >> f x).
Proof.
rewrite -(slowsort_preserves_size2 s (fun a b => guard (size s == b) >> f a)).
by rewrite eqxx guardT; under [in RHS]eq_bind do rewrite bindskipf.
Qed.

End slowsort_preserves.

Section qsort.
Variables (M : plusMonad).
Variables (d : unit) (T : orderType d).
Function qsort (s : seq T) {measure size s} : seq T :=
  (* if s is h :: t
  then let '(ys, zs) := partition h t in
       qsort ys ++ h :: qsort zs
  else [::]. *)
  (* NB: not using match causes problems when applying fqsort_ind
     which is automatically generated *)
  match s with
  | [::] => [::]
  | h :: t => let: (ys, zs) := partition h t in
              qsort ys ++ h :: qsort zs
  end.
Proof.
move=> s h t _ ys zs pht_yz; have := size_partition h t.
by rewrite pht_yz /= => <-; apply/ltP; rewrite ltnS leq_addl.
move=> s h t _ ys zs pht_yz; have := size_partition h t.
by rewrite pht_yz /= => <-; apply/ltP; rewrite ltnS leq_addr.
Defined.

Definition partition_slowsort (xs : seq T) : M (seq T) :=
  if xs isn't h :: t then Ret [::] else
  let: (ys, zs) := partition h t in
  liftM2 (fun a b => a ++ h :: b) (slowsort ys) (slowsort zs).

(* NB: slowsort'-spec in Nondet.agda *)
Lemma partition_slowsort_spec : partition_slowsort `<.=` slowsort.
Proof.
move; elim => [/=|h t ih].
rewrite slowsort_nil; exact: refin_refl.
rewrite slowsort_splits.
apply: (@refin_trans _ _ (splits t >>= fun yz =>
    assert (is_partition h) yz >>=
    fun '(ys, zs) => slowsort ys >>=
    fun ys' : seq T => slowsort zs >>=
    fun zs' => Ret (ys' ++ h :: zs'))); last first.
apply: refin_bindl => -[? ?].
rewrite assertE !bindA bindretf; exact: refin_refl.
rewrite -bindA; apply: refin_trans; last exact/refin_bindr/partition_spec.
rewrite bindretf /partition_slowsort; exact: refin_refl.
Qed.

Lemma qsort_spec : Ret \o qsort `<.=` (@slowsort M _ _).
Proof.
move=> s /=.
apply qsort_ind => [{}s _|{}s h t _ ys zs pht ihys ihzs]. (* qsort_ind *)
  rewrite slowsort_nil; exact: refin_refl.
apply: (refin_trans _ (partition_slowsort_spec _)); rewrite /= pht.
apply: (refin_trans _ (refin_liftM2 ihys ihzs)).
rewrite liftM2_ret; exact: refin_refl.
Qed.

End qsort.
