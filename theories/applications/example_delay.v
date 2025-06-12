(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2025 monae authors, license: LGPL-2.1-or-later               *)
Require Import Lia.
From mathcomp Require Import all_ssreflect.
From mathcomp Require boolp.
Require Import hierarchy.

(**md**************************************************************************)
(* # Applications of the Delay monad                                          *)
(*                                                                            *)
(* ```                                                                        *)
(*   factdelay == factorial                                                   *)
(*    collatzm == Collatz sequence                                            *)
(*     fastexp == fast exponential                                            *)
(*        mc91 == McCarthy's 91 function                                      *)
(* ```                                                                        *)
(******************************************************************************)

Local Open Scope monae_scope.

Section factorial.
Variable M : delayMonad.

Let fact_body a : M (nat + nat * nat)%type :=
  if a.1 is m.+1 then Ret (inr (m, a.2 * m.+1)) else Ret (inl a.2).

Definition factdelay := fun nm => while fact_body nm.

Lemma factdelay_fact n m : factdelay (n, m) ≈ Ret (m * n`!).
Proof.
rewrite /factdelay.
elim: n m => [m | n IH m]; rewrite fixpointwB bindretf/=.
  by rewrite muln1.
by rewrite mulnA.
Qed.

Let divide5_body (f : nat -> M nat) nm : M (nat + nat * nat)%type :=
    if nm.2 %% 5 == 0 then Ret (inl nm.2)
    else f nm.1 >>= (fun x => Ret (inr (nm.1.+1, x))).

Let dividefac1 n := while (divide5_body (fun n => factdelay (n, 1))) (n, 1).

Let dividefac2 n := while (divide5_body (fun n => Ret n`!)) (n, 1).

Lemma eq_dividefac n : dividefac1 n ≈ dividefac2 n.
Proof.
rewrite /dividefac1 /dividefac2 /divide5_body.
apply: whilewB => -[k l].
case: ifPn => //= _.
by rewrite factdelay_fact !bindretf mul1n.
Qed.

End factorial.

Section collatz.
Variable M : delayMonad.

Let collatzm_body m n : M (nat + nat)%type :=
  if n == 1 then Ret (inl m)
  else if n %% 2 == 0 then Ret (inr n./2)
       else Ret (inr (3 * n).+1).

Definition collatzm m := while (collatzm_body m).

Lemma collatzmwB m n p :
  collatzm m n >>= (fun q => Ret (p * q)) ≈ collatzm (p * m) n.
Proof.
rewrite /collatzm naturalitywB/=.
apply: whilewB => q.
have [->|q1] := eqVneq q 1.
  by rewrite bindretf/= fmapE bindretf.
rewrite /collatzm_body (negbTE q1).
by case: ifPn; rewrite bindretf/= fmapE bindretf.
Qed.

End collatz.

Section minus.
Variable M : delayMonad.

Let minus1_body nm : M ((nat + nat * nat) + nat * nat)%type :=
  if nm.1 is n'.+1 then Ret (inr (n', nm.2))
                   else if nm.2 is m'.+1 then Ret (inl (inr (m', m')))
                                         else Ret (inl (inl 0)).

Let minus1 := fun nm => while (while minus1_body) nm.

Let minus2_body nm : M (nat + nat * nat)%type :=
  if nm.1 is n'.+1 then Ret (inr (n', nm.2))
                   else if nm.2 is m'.+1 then Ret (inr (m', m'))
                                         else Ret (inl 0).

Let minus2 := fun nm => while minus2_body nm.

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
Variable M : delayMonad.

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
Variable M : delayMonad.

Let mc91_body nm : M (nat + nat * nat)%type :=
  if nm.1 == 0 then Ret (inl nm.2)
  else if nm.2 > 100 then Ret (inr (nm.1.-1, nm.2 - 10))
       else Ret (inr (nm.1.+1, nm.2 + 11)).

Definition mc91 n m := while mc91_body (n.+1, m).

Lemma wBisim_mc91S n m : 90 <= m < 101 -> mc91 n m ≈ mc91 n m.+1.
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

Lemma wBisim_mc91_101 m n : 90 <= m <= 101 -> mc91 n m ≈ mc91 n 101.
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
rewrite -addn1 (addnC l 1) addnA wBisim_mc91S ?m89// addn1.
by apply: IH => //; exact: leq_trans.
Qed.

Lemma wBisim_mc91_91 n : mc91 n 101 ≈ Ret 91.
Proof.
elim: n => [|n IH]; rewrite /mc91 /mc91_body fixpointwB bindretf/=.
  by rewrite fixpointwB bindretf.
by rewrite -/mc91_body // -/(mc91 n 91) wBisim_mc91_101 // IH.
Qed.

Lemma wBisim_mc91 n m : m <= 101 -> mc91 n m ≈ Ret 91.
Proof.
move=> m101.
have [m89|] := leqP 90 m.
  move: (conj m89 m101) => /andP Hm.
  by rewrite wBisim_mc91_101// wBisim_mc91_91.
move=> /ltnW /subnKC.
set k := 90 - m.
clearbody k.
elim: k {-2}k (leqnn k) n m {m101} => k.
  rewrite leqn0 => /eqP -> n m.
  rewrite addn0 => ->.
  by rewrite wBisim_mc91_101// wBisim_mc91_91.
move=> IH k' Hk n m Hm.
have -> : m = 90 - k' by rewrite -Hm addnK.
rewrite /mc91 /mc91_body fixpointwB //=.
rewrite ltn_subRL addnC/=.
rewrite bindretf/= -/mc91_body -/(mc91 _ _).
have [k'11|k'11] := leqP k' 11.
  by rewrite wBisim_mc91_101 ?wBisim_mc91_91//; lia.
by rewrite (IH (k' - 11))//; lia.
Qed.

End mc91.
