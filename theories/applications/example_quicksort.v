(* monae: Monadic equational reasoning in Rocq                                *)
(* Copyright (C) 2025 monae authors, license: LGPL-2.1-or-later               *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require boolp.
Require Import preamble.
Require Import hierarchy monad_lib alt_lib fail_lib state_lib.
From infotheo Require Import ssr_ext.
Require Import Recdef.
From Equations Require Import Equations.

(**md**************************************************************************)
(* # Quicksort example                                                        *)
(*                                                                            *)
(* This file provides a formalization of quicksort on lists as proved in      *)
(* [1, Sect. 4]. The main lemmas is quicksort_slowsort.                       *)
(*                                                                            *)
(* ```                                                                        *)
(* is_partition p (s, t) == elements of s are smaller or equal to p, and      *)
(*                          elements of t are greater of equal to p           *)
(*         partition p s == partitions s into a partition w.r.t. p            *)
(*                          type: T -> seq T -> seq T * seq T                 *)
(*            slowsort s == choose a sorted list among all permutations of s  *)
(*               qsort s == sort s by quicksort                               *)
(*                          type: seq T -> seq T                              *)
(* ```                                                                        *)
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
Context d (T : orderType d).

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

Section partition.
Context (M : plusMonad) d (T : orderType d).

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
by case: ifPn => xp; rewrite !(addSn,addnS) abxs.
(* ! was ? :conflict with Equations TODO bug report *)
Qed.

Lemma partition_spec (p : T) (xs : seq T) :
  ((@ret M _) \o partition p) xs `<=` splits xs >>= assert (is_partition p).
Proof.
elim: xs p => [/=|x xs ih] p.
  rewrite bindretf !assertE /is_partition guardT bindskipf; exact: refin_refl.
rewrite /= bindA.
apply: (refin_trans _ (refin_bindl _ _)); last first => [yz|].
rewrite alt_bindDl 2!bindretf 2!assertE.
rewrite 2!is_partition_consE 2!guard_and 2!bindA.
exact/(refin_alt (refin_refl _))/refin_bindr/refin_guard_le.
(* under eq_bind do rewrite alt_bindDl 2!bindretf 2!assertE.
under eq_bind do rewrite 2!is_partition_consE 2!guard_and 2!bindA. *)
(* apply: (refin_trans _ (refin_bindl _ _)); last first => [yz|]. *)
  (* apply (refin_alt). *)
  (* exact/(refin_alt (refin_refl _))/refin_bindr/refin_guard_le. *)
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
Context (M : plusMonad) d (T : orderType d).

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
rewrite guard_and !bindA/= (plus_commute (guard (all (>= p) b)))//=.
rewrite (plus_commute (guard (all (<= p) a)))// guard_all_qperm.
bind_ext=> a'.
rewrite plus_commute// assertE bindA bindretf bindA.
rewrite (plus_commute (guard (sorted a')))//.
rewrite (plus_commute (guard (all (<= p) a')))// plus_commute// guard_all_qperm.
bind_ext=> b'.
rewrite (plus_commute (guard (all (>= p) b')))// !assertE bindA bindretf.
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

Lemma slowsort_isNondet s : plus_isNondet (slowsort s : M _).
Proof.
rewrite /slowsort kleisliE.
have [syn syn_qperm] := @qperm_isNondet M _ s.
exists (ndBind syn (fun a => ndBind
  (if sorted a then ndRet tt else ndFail unit)
  (fun _ : unit => ndRet a))).
rewrite /= syn_qperm; bind_ext => s' /=.
case: ifPn => sorteds'.
  by rewrite /= bindretf assertE sorteds' guardT bindskipf.
by rewrite /= assertE (negbTE sorteds') guardF bindfailf.
Qed.

Lemma qperm_slowsort : (qperm >=> slowsort) = slowsort :> (seq T -> M (seq T)).
Proof. by rewrite /slowsort -kleisliA qperm_idempotent. Qed.

End slowsort.
Arguments slowsort {M} {_} {_}.

#[global] Hint Extern 0 (plus_isNondet (slowsort _)) =>
  solve[exact: slowsort_isNondet] : core.

Section slowsort_example.
Variable M : plusMonad.

Let bindskipE := (bindskipf, bindmskip).

Ltac sub := repeat rewrite !alt_bindDl !bindretf;
            rewrite bindA;
            repeat rewrite !qpermE !bindA !bindretf /=.
Ltac bindSF := rewrite !bindskipf !bindfailf.

Context d (T : orderType d).

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
Context (M : plusMonad) d {E : orderType d}.

Let slowsort_preserves_size : preserves (@slowsort M _ E) size.
Proof.
move=> s; have [n ns] := ubnP (size s); elim: n s ns => // n ih s ns.
move: s ns => [ns|p s]; first by rewrite /= slowsort_nil 2!bindretf.
rewrite /= ltnS => ns. rewrite /slowsort kleisliE bindA [RHS]bindA.
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
Context d (T : orderType d).

(* let *)
Equations? qsort (s : seq T) : seq T by wf (size s) lt :=
| [::] => [::]
| h :: t => qsort (partition h t).1 ++ h :: qsort (partition h t).2.
(* let: (ys, zs) := partition h t in
qsort ys ++ h :: qsort zs. *)
Proof.
have := size_partition h t.
by move=> <-; apply /ltP; rewrite ltnS leq_addr.
have := size_partition h t.
by move=> <-; apply /ltP; rewrite ltnS leq_addl.
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
apply qsort_elim => [|h t ihys ihzs].
  rewrite slowsort_nil; exact: refin_refl.
apply: (refin_trans _ (partition_slowsort_spec _)).
rewrite /=.
move H : (partition h t) => ht.
move: ht H => [ys zs] /= pht.
rewrite pht in ihys ihzs.
apply: (refin_trans _ (refin_liftM2 ihys ihzs)).
rewrite liftM2_ret; exact: refin_refl.
Qed.

End qsort.

Module qsort_function.
Section qsort_function.
Context (M : plusMonad) d (T : orderType d).

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

End qsort_function.
End qsort_function.
