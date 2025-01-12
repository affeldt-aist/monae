From mathcomp Require Import all_ssreflect.
From mathcomp Require boolp.
Require Import hierarchy.
Require Import Lia.

Local Open Scope monae_scope.

Section delayexample.
Variable M : delayMonad.

Let fact_body a : M (nat + nat * nat)%type :=
  match a with
  | (O, a2) => Ret (inl a2)
  | (n'.+1, a2) => Ret (inr (n', a2 * n'.+1))
  end.
Let factdelay := fun nm => while fact_body nm.

Lemma eq_fact_factdelay : forall n m, factdelay (n, m) ≈ Ret (m * n`!).
Proof.
move => n.
rewrite /factdelay.
elim: n => [m | n IH m]; rewrite fixpointE bindretf/=.
  by rewrite muln1.
by rewrite mulnA.
Qed.

Let collatzm_body m n : M (nat + nat)%type :=
  if n == 1 then Ret (inl m)
  else if n %% 2 == 0 then Ret (inr n./2)
       else Ret (inr ((3 * n).+1)).
Let collatzm m := fun n => while (collatzm_body m) n.
Let delaymul m d : M nat := d >>= (fun n => Ret (m * n)).

Lemma collatzmwB m n p : delaymul p (collatzm m n) ≈ collatzm (p * m) n.
Proof.
rewrite /collatzm /delaymul naturalityE.
apply: whilewB => q.
have [Hs|Hns] := eqVneq q 1.
  by rewrite Hs bindretf/= fmapE bindretf/=.
rewrite /collatzm_body !(ifN_eq _ _ Hns).
by have [|] := eqVneq (q %% 2) 0; rewrite bindretf/= fmapE bindretf.
Qed.

Let minus1_body nm : M ((nat + nat * nat) + nat * nat)%type :=
  match nm with
  | (O, m) => match m with
             |O => Ret (inl (inl O))
             |S m' => Ret (inl (inr (m', m')))
             end
  | (n'.+1, m) => Ret (inr (n', m))
  end.
Let minus1 := fun nm => while (while minus1_body) nm.
Let minus2_body nm : M (nat + nat * nat)%type :=
  match nm with
  | (O, m) => match m with
            |O => Ret (inl O)
            |S m' => Ret (inr (m', m'))
            end
  | (n'.+1, m) => Ret (inr (n',m))
  end.
Let minus2 := fun nm => while minus2_body nm.

Lemma eq_minus nm : minus1 nm ≈ minus2 nm.
Proof.
rewrite /minus1 /minus2 -codiagonalE.
apply: whilewB.
move => [n m].
case: n => [|n /=].
  by case: m => //= [|n]; rewrite fmapE bindretf //.
by rewrite fmapE bindretf.
Qed.

Let divide5_body (f : nat -> M nat) nm : M (nat + nat * nat)%type :=
  match nm with (n, m) =>
    if m %% 5 == 0 then Ret (inl m)
    else f n >>= (fun x => Ret (inr (n.+1, x)))
  end.
Let dividefac1 n := while (divide5_body (fun n => factdelay (n, 1))) (n, 1).
Let dividefac2 n := while (divide5_body (fun n => Ret n`!)) (n, 1).

Lemma eq_dividefac : forall n, dividefac1 n ≈ dividefac2 n.
Proof.
move => n.
rewrite /dividefac1 /dividefac2.
apply whilewB.
move => [k l].
have [Hl|Hln] := eqVneq (l %% 5) 0 => /=.
  by rewrite Hl.
by rewrite !(ifN_eq _ _ Hln) eq_fact_factdelay !bindretf mul1n.
Qed.

Let fastexp_body nmk : M (nat + nat * nat * nat)%type :=
  match nmk with (n, m, k) =>
    if n == 0 then Ret (inl m)
    else (if odd n then Ret (inr (n.-1 , m * k, k))
          else Ret (inr (n./2, m, k * k) )) end.
Let fastexp n m k := while fastexp_body (n, m, k).

Lemma expE n: forall m k, fastexp n m k ≈ Ret (m * expn k n).
Proof.
rewrite /fastexp /fastexp_body.
elim: n {-2}n (leqnn n) => n.
  rewrite leqn0 => /eqP H0 m k.
  by rewrite H0 fixpointE /= bindretf /= expn0 mulnS muln0 addn0.
move => IH [|m'] Hmn m k.
  by rewrite fixpointE /= bindretf /= mulnS muln0 addn0.
case/boolP: (odd (m'.+1)) => Hm'.
  by rewrite fixpointE Hm' bindretf/= IH//= expnSr (mulnC (k^m') k) mulnA.
rewrite fixpointE ifN //= bindretf /= IH.
  by rewrite uphalfE mulnn -expnM mul2n (even_halfK Hm').
rewrite ltnS in Hmn.
rewrite leq_uphalf_double.
apply: (leq_trans Hmn).
rewrite -addnn.
by apply: leq_addr.
Qed.

Let mc91_body nm : M (nat + nat * nat)%type :=
  match nm with (n, m) => if n == 0 then Ret (inl m)
                          else if m > 100 then Ret (inr (n.-1, m - 10))
                                          else Ret (inr (n.+1, m + 11))
  end.
Let mc91 n m := while mc91_body (n.+1, m).

Lemma mc91succE n m : 90 <= m < 101 -> mc91 n m ≈ mc91 n (m.+1).
Proof.
move => /andP [Hmin].
rewrite /mc91 fixpointE /= ltnNge => Hmax.
rewrite ifN // bindretf /= fixpointE /=.
have -> : 100 = 89 + 11 by [].
rewrite ltn_add2r ifT //.
rewrite bindretf fixpointE /= fixpointE.
have -> // : m + 11 - 10 = m.+1.
by rewrite -addnBA // addn1.
Qed.
Lemma mc91E_aux m n : 90 <= m <= 101 -> mc91 n m ≈ mc91 n 101.
Proof.
move => /andP [Hmin Hmax].
case/boolP: (m < 101).
  move/ltnW/subnKC.
  set k:= 101 - m.
  clearbody k.
  move: m Hmin Hmax.
  elim: k.
    move => m Hmin Hmax.
    by rewrite addn0 => ->.
  move => l IH m Hmin.
  rewrite leq_eqVlt => /orP [/eqP H101 | Hm].
    by rewrite H101 => _.
  rewrite -addn1 (addnC l 1) addnA mc91succE ?Hmin // addn1.
  apply IH => //.
  by apply: leq_trans.
rewrite -leqNgt => H100.
have -> //: m = 101.
apply anti_leq => //.
by rewrite Hmax.
Qed.
Lemma mc91_101E n : mc91 n 101 ≈ Ret 91.
Proof.
elim: n => [|n IH]; rewrite/mc91/mc91_body fixpointE bindretf/=.
  by rewrite fixpointE bindretf.
by rewrite -/mc91_body // -/(mc91 n 91) mc91E_aux // IH.
Qed.
Lemma mc91E n m : m <= 101 -> mc91 n m ≈ Ret 91.
Proof.
move => H101.
have [H89|] := leqP 90 m.
  move: (conj H89 H101) => /andP Hm.
  by rewrite mc91E_aux // mc91_101E.
move/ltnW/subnKC.
set k:= 90 - m.
clearbody k.
elim: k {-2}k (leqnn k) n m {H101} => k.
  rewrite leqn0 => /eqP H0 n m.
  rewrite H0 (addn0 m) => ->.
  by rewrite mc91E_aux// mc91_101E.
move =>IH k' Hk n m Hm.
have ->: m = 90 - k' by rewrite -Hm addnK.
rewrite/mc91/mc91_body fixpointE //=.
rewrite ifF; last by rewrite ltn_subRL addnC.
rewrite bindretf/= -/mc91_body -/(mc91 _ _).
case/boolP: (k' <= 11) => Hk'.
  by rewrite mc91E_aux ?mc91_101E//; lia.
rewrite -ltnNge in Hk'.
by rewrite (IH (k' - 11))//; lia.
Qed.
