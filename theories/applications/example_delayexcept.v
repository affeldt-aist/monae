From mathcomp Require Import all_ssreflect.
From mathcomp Require Import boolp.
Require Import preamble hierarchy monad_lib fail_lib state_lib.

Local Open Scope monae_scope.

Section delayexcept_example.

Variable M : delayExceptMonad.

Definition select l := let max := \max_(i <- l) i in (max, rem max l).

Definition muloflistover10d_body ln : M (nat + (seq nat) * nat)%type :=
  match ln with (l, n) =>
                  match l with
                    |[::] => Ret (inl n)
                    |h::tl => let (m, res) := select l in catch (if m <= 10 then fail else Ret (inr (res, m * n))) (Ret (inl n))
                  end
  end.

Definition muloflistover10d := while muloflistover10d_body.

Definition muloflistover10 l := foldr (fun x z => if 10 < x then x * z else z) 1 l.

Lemma all_under10 l : (forall i, i \in l -> i <= 10) -> muloflistover10 l = 1.
Proof.
elim: l => //= n l' Hl H.
have [H10|_] := ltnP 10 n.
  contradict H10.
  apply/negP.
  rewrite -leqNgt.
  apply H.
  by rewrite in_cons eq_refl.
apply Hl => m Hl'.
apply H.
by rewrite in_cons Hl' orbT.
Qed.

Lemma muloflistover10_aux(l : seq nat) (k : nat): 10 < k -> k \in l -> k * muloflistover10 (rem k l) = muloflistover10 l.
move => Hk Hink.
rewrite/muloflistover10.
elim: l Hink => //= n l' IH Hink.
have  [Hnk|/negPf Hnk] := eqVneq n k.
  have [|?] := ltnP 10 n.
    by rewrite Hnk.
  contradict Hk.
  rewrite -Hnk.
  apply/negP.
  by rewrite -ltnNge.
have Hkl': k \in l'.
  move: Hink.
  by rewrite in_cons eq_sym Hnk/=.
have [Hn|HnN] := ltnP 10 n.
  rewrite -(IH Hkl')/= Hn.
  by rewrite mulnA (mulnC k n) -mulnA.
by rewrite -(IH Hkl')/= ltnNge HnN/=.
Qed.

Lemma maxinseq (l : seq nat): ~~(nilp l) -> \max_(i <- l) i \in l.
Proof.
move => Hn.
rewrite -(in_tupleE l) big_tuple.
case: (eq_bigmax (tnth (in_tuple l))) => [|x ->].
  by rewrite cardT size_enum_ord lt0n.
by rewrite mem_tnth.
Qed.

Lemma muloflistover10E (l : seq nat) (n : nat) : muloflistover10d (l, n) ≈ Ret (n * (muloflistover10 l)).
Proof.
move Hlen: (size l) => len.
move: n.
elim: len l Hlen.
- move => l /eqP/nilP Hl n.
  by rewrite/muloflistover10/muloflistover10d/muloflistover10d_body Hl /= fixpointE /= bindretf /= mulnS muln0 addn0.
move => m IH l' Hs n.
rewrite/muloflistover10d/muloflistover10d_body fixpointE /=.
elim: l' Hs => //= [h l''] _ Hs.
case: Hs => Hs.
have [/bigmax_leqP_seq Hm10|Hm10] := leqP (\max_(i <- (h :: l'')) i) 10.
  rewrite catchfailm bindretf /=.
  have -> : (10 < h) = false.
    apply/negP/negP.
    rewrite -leqNgt.
    apply Hm10 => //=.
    by rewrite in_cons eq_refl.
  rewrite all_under10.
    by rewrite mulnS muln0 addn0.
  move => i Hini.
  apply Hm10 => //=.
  by rewrite in_cons Hini orbT.
rewrite catchret bindretf /=.
rewrite -/muloflistover10d_body -/muloflistover10d.
have [Ht|Hf] := eqVneq h (\max_(i <- (h :: l'')) i).
  by rewrite {2}Ht (ifT _ _ Hm10) (IH l'' Hs) -Ht (mulnC h n) mulnA.
move: Hm10.
set k := \max_(i <- (h :: l'')) i => Hk.
have Hmaxin : k \in (h :: l'').
  subst k.
  by apply maxinseq.
rewrite IH/=.
  rewrite /= (mulnC k n) -mulnA fun_if.
  rewrite (mulnA k h _) (mulnC k h) -mulnA (muloflistover10_aux _ _ Hk) //.
  by move: Hmaxin; rewrite in_cons eq_sym (negPf Hf) /=.
subst k.
rewrite  size_rem.
  case: l'' Hs Hf Hk Hmaxin => [? contr|h' l'''  Hs ? ?].
    contradict contr.
    by rewrite big_cons big_nil maxn0 eq_refl.
  by rewrite prednK //=.
move: Hmaxin.
by rewrite in_cons eq_sym (negPf Hf) /=.
Qed.
