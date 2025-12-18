(* monae: Monadic equational reasoning in Rocq                                *)
(* Copyright (C) 2025 monae authors, license: LGPL-2.1-or-later               *)
Require Import Lia.
From mathcomp Require Import all_ssreflect.
From mathcomp Require boolp.
Require Import hierarchy.

(**md**************************************************************************)
(* # Applications of the Elgot monad                                          *)
(*                                                                            *)
(* ## Applications of the Elgot monad                                         *)
(*                                                                            *)
(* The examples in this file are also documented in the following paper:      *)
(* [1] Ryuji Kawakami, Jacques Garrigue, Takafumi Saikawa, Reynald Affeldt.   *)
(*     Monadic equational reasoning for while loops. Computer Software, 2026  *)
(*                                                                            *)
(* ```                                                                        *)
(*         fact_elgot == factorial                                            *)
(*            collatz == Collatz sequence                                     *)
(*                       (was collatzm in [1])                                *)
(*         minus{1,2} == TODO                                                 *)
(*            fastexp == fast exponential                                     *)
(*               mc91 == McCarthy's 91 function                               *)
(* ```                                                                        *)
(*                                                                            *)
(* ## Applications of the Elgot-assert monad                                  *)
(*                                                                            *)
(* Proved proves partial correctness of the Bubble Sort algorithm not         *)
(* changing the list length. The main theorem is bubblesort_size.             *)
(*                                                                            *)
(* ```                                                                        *)
(*              sortl == for all elements, swap them if their order is        *)
(*                       reversed compared to adjacent elements               *)
(*         bubblesort == Bubble Sort algorithm using while                    *)
(*             sizelE == a predicate to check not changing the list length    *)
(* ```                                                                        *)
(*                                                                            *)
(* ## Applications of the Elgot-exception monad                               *)
(*                                                                            *)
(* ```                                                                        *)
(*       prodover10 l == (monadic) product of elements of l that are > 10     *)
(*  prodover10_pure l == product of elements of l that are > 10               *)
(* ```                                                                        *)
(*                                                                            *)
(* ## Applications of the Elgot-state monad                                   *)
(*                                                                            *)
(* ```                                                                        *)
(*         fact_elgot_state == factorial                                      *)
(*                             (was factds in [1]                             *)
(*       collatz_state{1,2} == Collatz sequence using the Elgot state monad   *)
(* ```                                                                        *)
(*                                                                            *)
(* ## Application of the Elgot-typedstore monad                               *)
(*                                                                            *)
(* ```                                                                        *)
(*   fact_elgot_typed_store == was factdts_nat in [1]                         *)
(*   fact_elgot_typed_store_unit == was factdts_unit in [1]                   *)
(* ```                                                                        *)
(******************************************************************************)

Local Open Scope monae_scope.

Section factorial.
Variable M : elgotMonad.

Let fact_body a : M (nat + nat * nat)%type :=
  if a.1 is m.+1 then Ret (inr (m, a.2 * m.+1)) else Ret (inl a.2).

Definition fact_elgot := fun nm => while fact_body nm.

Lemma fact_elgot_fact n m : fact_elgot (n, m) ≈ Ret (m * n`!).
Proof.
rewrite /fact_elgot.
elim: n m => [m | n IH m]; rewrite fixpointwB bindretf/=.
  by rewrite muln1.
by rewrite mulnA.
Qed.

Let divide5_body (f : nat -> M nat) nm : M (nat + nat * nat)%type :=
    if nm.2 %% 5 == 0 then Ret (inl nm.2)
    else f nm.1 >>= (fun x => Ret (inr (nm.1.+1, x))).

Let divide_fact1 n := while (divide5_body (fun n => fact_elgot (n, 1))) (n, 1).

Let divide_fact2 n := while (divide5_body (fun n => Ret n`!)) (n, 1).

Lemma divide_fact1wB n : divide_fact1 n ≈ divide_fact2 n.
Proof.
rewrite /divide_fact1 /divide_fact2 /divide5_body.
apply: whilewB => -[k l].
case: ifPn => //= _.
by rewrite fact_elgot_fact !bindretf mul1n.
Qed.

End factorial.

Section collatz.
Variable M : elgotMonad.

(* was collatzm_body in [1] *)
Let collatz_body (T : Type) m n : M (T + nat)%type :=
  if n == 1 then Ret (inl m)
  else if n %% 2 == 0 then Ret (inr n./2)
       else Ret (inr (3 * n).+1).

(* was collatzm in [1] *)
Definition collatz (T : Type) (m : T) := while (collatz_body T m).

(* was collatzmwB in [1] *)
Lemma collatzwB (T U : Type) (f : T -> U) m n :
  collatz T m n >>= (Ret \o f) ≈ collatz U (f m) n.
Proof.
rewrite /collatz naturalitywB/=.
apply: whilewB => q.
have [->|q1] := eqVneq q 1.
  by rewrite bindretf/= fmapE bindretf.
rewrite /collatz_body (negbTE q1).
by case: ifPn; rewrite bindretf/= fmapE bindretf.
Qed.

End collatz.

Section minus.
Variable M : elgotMonad.

Let minus1_body nm : M ((nat + nat * nat) + nat * nat)%type :=
  if nm.1 is n'.+1 then Ret (inr (n', nm.2))
                   else if nm.2 is m'.+1 then Ret (inl (inr (m', m')))
                                         else Ret (inl (inl 0)).

Definition minus1 := fun nm => while (while minus1_body) nm.

Let minus2_body nm : M (nat + nat * nat)%type :=
  if nm.1 is n'.+1 then Ret (inr (n', nm.2))
                   else if nm.2 is m'.+1 then Ret (inr (m', m'))
                                         else Ret (inl 0).

Definition minus2 := fun nm => while minus2_body nm.

Lemma eq_minus nm : minus1 nm ≈ minus2 nm.
Proof.
rewrite /minus1 /minus2 -codiagonalwB.
apply: whilewB => -[n m].
case: n => [|n /=].
  by case: m => //= [|n]; rewrite fmapE bindretf.
by rewrite fmapE bindretf.
Qed.

End minus.

Section fastexp.
Variable M : elgotMonad.

Let fastexp_body nmk : M (nat + nat * nat * nat)%type :=
  match nmk with (n, m, k) =>
    if n == 0 then Ret (inl m)
    else (if odd n then Ret (inr (n.-1, m * k, k))
          else Ret (inr (n./2, m, k * k) ))
  end.

Let fastexp n m k := while fastexp_body (n, m, k).

Lemma fastexpwB n : forall m k, fastexp n m k ≈ Ret (m * expn k n).
Proof.
rewrite /fastexp /fastexp_body.
elim: n {-2}n (leqnn n) => n.
  rewrite leqn0 => /eqP -> m k.
  by rewrite fixpointwB/= bindretf/= muln1.
move=> IH [_|m' Hmn] m k; first by rewrite fixpointwB/= bindretf/= muln1.
have [/= Hm'|/= Hm'] := boolP (odd m'); last first.
  by rewrite fixpointwB/= Hm' bindretf/= IH//= expnSr mulnAC -mulnA.
rewrite fixpointwB/= Hm' bindretf/= IH.
  by rewrite uphalfE mulnn -expnM mul2n (@even_halfK m'.+1)//= negbK.
rewrite leq_uphalf_double.
move: Hmn; rewrite ltnS => /leq_trans; apply.
by rewrite -addnn leq_addr.
Qed.

End fastexp.

Section mc91.
Variable M : elgotMonad.

Let mc91_body nm : M (nat + nat * nat)%type :=
  if nm.1 == 0 then Ret (inl nm.2)
  else if nm.2 > 100 then Ret (inr (nm.1.-1, nm.2 - 10))
       else Ret (inr (nm.1.+1, nm.2 + 11)).

Definition mc91 n m := while mc91_body (n.+1, m).

(* was wBisim_mc91S in [1] *)
Lemma mc91wBS n m : 90 <= m < 101 -> mc91 n m ≈ mc91 n m.+1.
Proof.
move=> /andP[m89].
rewrite /mc91 /mc91_body fixpointwB/= ltnNge => m100.
rewrite -/mc91_body.
rewrite (negbTE m100) bindretf/= fixpointwB/=.
rewrite /mc91_body/= -[100]/(89 + 11) ltn_add2r m89.
rewrite -/mc91_body.
rewrite bindretf fixpointwB /= fixpointwB.
rewrite (_ : m + 11 - 10 = m.+1)//.
by rewrite -addnBA// addn1.
Qed.

Lemma mc91wB101 m n : 90 <= m <= 101 -> mc91 n m ≈ mc91 n 101.
Proof.
move=> /andP[m89 m101].
have [/ltnW /subnKC|m100] := ltnP m 101; last first.
  by rewrite (_ : m = 101)//; apply/anti_leq; rewrite m101.
set k := 101 - m.
clearbody k.
move: m m89 m101.
elim: k => [m m89 m101|l IH m m89].
  by rewrite addn0 => ->.
rewrite leq_eqVlt => /predU1P[->//| Hm].
rewrite -addn1 (addnC l 1) addnA mc91wBS ?m89// addn1.
by apply: IH => //; exact: leq_trans.
Qed.

Lemma mc91wB91 n : mc91 n 101 ≈ Ret 91.
Proof.
elim: n => [|n IH]; rewrite /mc91 /mc91_body fixpointwB bindretf/=.
  by rewrite fixpointwB bindretf.
by rewrite -/mc91_body // -/(mc91 n 91) mc91wB101 // IH.
Qed.

Lemma mc91wB n m : m <= 101 -> mc91 n m ≈ Ret 91.
Proof.
move=> m101.
have [m89|] := leqP 90 m.
  move: (conj m89 m101) => /andP Hm.
  by rewrite mc91wB101// mc91wB91.
move=> /ltnW /subnKC.
set k := 90 - m.
clearbody k.
elim: k {-2}k (leqnn k) n m {m101} => k.
  rewrite leqn0 => /eqP -> n m.
  rewrite addn0 => ->.
  by rewrite mc91wB101// mc91wB91.
move=> IH k' Hk n m Hm.
have -> : m = 90 - k' by rewrite -Hm addnK.
rewrite /mc91 /mc91_body fixpointwB //=.
rewrite ltn_subRL addnC/=.
rewrite bindretf/= -/mc91_body -/(mc91 _ _).
have [k'11|k'11] := leqP k' 11.
  by rewrite mc91wB101 ?mc91wB91//; lia.
by rewrite (IH (k' - 11))//; lia.
Qed.

End mc91.

Section select.
Variable M : elgotExceptMonad.

Definition select l := let max := \max_(i <- l) i in (max, rem max l).

Definition prodover10_body ln : M (nat + (seq nat) * nat)%type :=
  match ln with
    (l, n) => if l is h::tl then
                let (m, res) := select l in
                catch (if m <= 10 then
                         fail
                       else Ret (inr (res, m * n))) (Ret (inl n))
              else
                Ret (inl n)
  end.

Definition prodover10 := while prodover10_body.

Definition prodover10_pure l :=
  foldr (fun x acc => if 10 < x then x * acc else acc) 1 l.

Lemma all_under10 l : (forall i, i \in l -> i <= 10) -> prodover10_pure l = 1.
Proof.
elim: l => //= n l' Hl H.
have [n10|_] := ltnP 10 n.
  contradict n10.
  by apply/negP; by rewrite -leqNgt H// mem_head.
rewrite Hl// => m Hl'.
by rewrite H// inE Hl' orbT.
Qed.

Lemma prodover10_pure_rem (l : seq nat) (k : nat) : 10 < k -> k \in l ->
  k * prodover10_pure (rem k l) = prodover10_pure l.
Proof.
move=> Hk Hink.
rewrite /prodover10_pure.
elim: l => //= n l' IH in Hink *.
have [nk|nk] := eqVneq n k.
  have [|?] := ltnP 10 n; first by rewrite nk.
  contradict Hk.
  rewrite -nk.
  by apply/negP; rewrite -ltnNge.
have Hkl': k \in l'.
  by move: Hink; rewrite in_cons eq_sym (negbTE nk).
have [Hn|HnN] := ltnP 10 n.
  by rewrite -(IH Hkl')/= Hn mulnA (mulnC k n) -mulnA.
by rewrite -(IH Hkl')/= ltnNge HnN/=.
Qed.

Lemma prodover10wB (l : seq nat) n :
  prodover10 (l, n) ≈ Ret (n * prodover10_pure l).
Proof.
move Hlen: (size l) => len.
move: n.
elim: len l Hlen.
  move => l /eqP/nilP Hl n.
  rewrite /prodover10_pure /prodover10 /prodover10_body Hl /=.
  by rewrite fixpointwB /= bindretf /= mulnS muln0 addn0.
move=> m IH l' Hs n.
rewrite /prodover10 /prodover10_body fixpointwB /=.
elim: l' Hs => //= [h l''] _ []Hs.
have [/bigmax_leqP_seq Hm10|Hm10] := leqP (\max_(i <- h :: l'') i) 10.
  rewrite catchfailm bindretf /=.
  rewrite ifF; last first.
    apply/negP/negP; rewrite -leqNgt.
    by rewrite Hm10//= mem_head.
  rewrite all_under10.
    by rewrite muln1.
  move=> i Hini.
  by rewrite Hm10//= in_cons Hini orbT.
rewrite catchret bindretf /=.
rewrite -/prodover10_body -/prodover10.
have [Ht|Hf] := eqVneq h (\max_(i <- h :: l'') i).
  by rewrite {2}Ht (ifT _ _ Hm10) (IH l'' Hs) -Ht (mulnC h n) mulnA.
move: Hm10.
set k := \max_(i <- h :: l'') i => k10.
have Hmaxin : k \in (h :: l'') by rewrite preamble.maxinseq.
rewrite IH/=.
  rewrite /= (mulnC k n) -mulnA fun_if.
  rewrite (mulnA k h _) (mulnC k h) -mulnA (prodover10_pure_rem _ _ k10) //.
  by move: Hmaxin; rewrite in_cons eq_sym (negPf Hf).
subst k.
rewrite size_rem.
  case: l'' Hs Hf k10 Hmaxin => [? contr|h' l'''  Hs ? ?].
    contradict contr.
    by rewrite big_cons big_nil maxn0 eq_refl.
  by rewrite prednK.
move: Hmaxin.
by rewrite in_cons eq_sym (negPf Hf).
Qed.

End select.

Section bubblesort.
Variable M : elgotAssertMonad.

Fixpoint sortl (l : seq nat) :=
  if l is n :: tl then
    (if tl is m :: tl' then
       (if m < n then
          m :: n :: sortl tl'
        else n :: sortl tl)
     else l)
  else nil.

Lemma sortl_length l : size l = size (sortl l).
Proof.
move Hlen: (size l) => n.
elim: n {-2}n (leqnn n) l Hlen => n.
  rewrite leqn0 => /eqP -> l.
  by move/size0nil => ->.
move=> IH m Hmn.
move=> [|h] //=.
move=> [|k tl] // Hs.
have [hk|kh] := leqP h k.
  rewrite [k :: tl]lock/= -lock -Hs.
  congr S.
  rewrite -(IH (size (k :: tl))) //.
  by rewrite -(leq_add2r 1 _ _) !addn1 Hs.
rewrite -Hs [k :: tl]lock/= -lock -(IH (size tl)) //.
by move: Hmn; rewrite -Hs/= ltnS; exact: ltnW.
Qed.

Definition bubblesort_body (l : seq nat) : M (seq nat + seq nat)%type :=
  if l == sortl l then Ret (inl l) else Ret (inr (sortl l)).

Definition bubblesort l := while bubblesort_body l.

Definition sizelE (l : seq nat) : pred (seq nat + seq nat) :=
  fun ll => match ll with
            | inr l' => size l == size l'
            | inl l' => size l == size l'
            end.

Lemma bubblesort_size l :
  bassert (sizelE l) (bubblesort l >>= (Ret \o inl)) ≈ bubblesort l >>= (Ret \o inl).
Proof.
apply: pcorrect.
  by rewrite/sizelE.
move=> l' /= Inv.
rewrite /bubblesort_body.
case: ifP => /eqP H.
  by rewrite bindretf/= bindretf/= assertE/= Inv guardT bindretf.
move: Inv.
rewrite !bindretf/= !/sizelE (sortl_length l') /assert /guard.
case: ifP => //=.
by rewrite !bindskipf.
Qed.

End bubblesort.

Section factorial.
Variable M : elgotStateMonad nat.

Local Open Scope do_notation.

Definition fact_elgot_state_body m : M (unit + nat)%type :=
  do s <- get;
  match m with
  | O => do _ <- put s; Ret (inl tt)
  | m'.+1 => do _<- put (m * s); Ret (inr m')
  end.

Definition fact_elgot_state := while fact_elgot_state_body.

Lemma fact_elgot_statewB n :
  fact_elgot_state n ≈ do s <- get; do _ <- put (n`! * s); Ret tt.
Proof.
rewrite /fact_elgot_state /fact_elgot_state_body.
elim: n => /= [|n' IH].
rewrite fixpointwB/= !bindA.
apply: bindfwB => a.
by rewrite bindA bindretf/= mul1n.
rewrite /fact_elgot_state /fact_elgot_state_body fixpointwB/= bindA.
under eq_bind do rewrite bindA bindretf/=.
setoid_rewrite IH.
by under eq_bind do rewrite -!bindA putget !bindA bindretf -bindA
                            putput mulnA (mulnC n'`! _).
Qed.

End factorial.

Section collatz_state.
Variable M : elgotStateMonad (seq nat).

Local Open Scope do_notation.

Definition collatz_state1_body nml
    : M ((nat * nat + nat * nat * nat) + nat * nat * nat)%type :=
  match nml with (n, m, l) =>
    do s' <- get;
    do _ <- put (n :: s');
    if n == 1 then if (l %% 4 == 1)
            then Ret (inl (inl (m, l)))
                 else do _ <- put [::]; Ret (inl (inr (m.+1, m.+1, 0)))
    else if (n %% 2 == 0) then Ret (inr (n./2, m, l.+1))
         else Ret (inr ((3 * n).+1, m, l.+1))
  end.

Definition collatz_state1 n := while (while collatz_state1_body) (n, n, 0).

Definition collatz_state2_body nml : M ((nat * nat + nat * nat * nat))%type :=
  match nml with (n, m, l) =>
    do s' <- get;
    do _ <- put (n :: s');
    if (l %% 4 == 1) && (n == 1) then Ret (inl (m, l))
    else if (n == 1) then do _ <- put [::]; Ret (inr (m.+1, m.+1, 0))
         else if (n %% 2) == 0 then Ret (inr (n./2, m, l.+1))
              else Ret (inr ((3 * n).+1, m, l.+1))
  end.

Definition collatz_state2 n := while collatz_state2_body (n, n, 0).

Lemma collatz_state1wB n : collatz_state1 n ≈ collatz_state2 n.
Proof.
rewrite /collatz_state1 /collatz_state2 -codiagonalwB.
apply: whilewB => -[[n' m] l].
rewrite /collatz_state1_body /collatz_state2_body.
have [Hl|?] := eqVneq (l %% 4) 1 => /=.
  have [?|] := eqVneq n' 1 => /=.
    rewrite Hl fmapE bindA.
    by under eq_bind do rewrite bindA bindretf.
  have [|] := eqVneq (n' %% 2) 0 => /=;
  rewrite fmapE/= bindA bindfwB//= => a;
  by rewrite bindA bindretf.
have [Hn'|_] := eqVneq n' 1 => /=.
  rewrite Hn' ifN //= fmapE bindA.
  by under eq_bind do rewrite bindA bindA bindretf.
have [|] := eqVneq (n' %% 2) 0 => /=;
  rewrite fmapE/= bindA;
  by under eq_bind do rewrite bindA bindretf.
Qed.

End collatz_state.

Require Import typed_store_universe typed_store_lib.

Module CoqTypeNat.
Import MLTypes CoqTypeNat.

Definition elgotTypedStoreMonad (N : monad) :=
  elgotTypedStoreMonad ml_type N nat.

Section factorial.
Variables (N : monad) (M : elgotTypedStoreMonad N).

Local Notation coq_type := hierarchy.coq_type.
Local Open Scope do_notation.

Definition fact_elgot_typed_store_unit_body
    (r l : loc ml_int) n (_ : unit) : M(unit + unit)%type :=
  do i <- cget l;
        if i <= n
        then do v <- cget r;
             do _ <- cput r (i * v);
             do _ <- cput l (i.+1);
             Ret (inr tt)
        else Ret (inl tt).

Definition fact_elgot_typed_store_unit n :=
  do r <- cnew ml_int 1;
  do l <- cnew ml_int 1;
  do _ <-
  while (fact_elgot_typed_store_unit_body r l n) tt;
  do v <- cget r; Ret v.

(* was factdts_nat_body in [1] *)
Let fact_elgot_typed_store_body (r : loc ml_int) n : M (unit + nat)%type :=
  do v <- cget r;
  if n is m.+1 then do _ <- cput r (n * v); Ret (inr m)
               else Ret (inl tt).

(* was while_factdts_natE in [1] *)
Let while_fact_elgot_typed_storewB n r :
  while (fact_elgot_typed_store_body r) n ≈ do s <- cget r; cput r (n`! * s).
Proof.
elim: n => /= [|m IH].
  rewrite fixpointwB/= !bindA.
  under [x in _ ≈ x]eq_bind => s do rewrite fact0 mul1n.
  rewrite cgetputskip.
  by under eq_bind do rewrite bindretf.
rewrite fixpointwB/= bindA.
under eq_bind => s do rewrite bindA bindretf/=.
setoid_rewrite IH.
by under eq_bind do rewrite cputget cputput mulnA (mulnC m`! _).
Qed.

(* was factdts_nat in [1] *)
Definition fact_elgot_typed_store n :=
  do r <- cnew ml_int 1;
  do _ <- while (fact_elgot_typed_store_body r) n ;
  cget r.

(* was factn in [1] *)
Lemma fact_elgot_typed_storewB n :
  fact_elgot_typed_store n ≈ cnew ml_int n`! >> Ret n`!.
Proof.
rewrite /fact_elgot_typed_store.
setoid_rewrite while_fact_elgot_typed_storewB.
under eq_bind do rewrite bindA.
by rewrite cnewget cnewput muln1 cnewgetret.
Qed.

End factorial.

End CoqTypeNat.
