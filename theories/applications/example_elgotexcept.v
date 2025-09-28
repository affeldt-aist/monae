(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2025 monae authors, license: LGPL-2.1-or-later               *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import boolp.
Require Import preamble hierarchy monad_lib fail_lib state_lib.

(**md**************************************************************************)
(* # Applications of the Elgot-exception monad                                *)
(*                                                                            *)
(******************************************************************************)

Local Open Scope monae_scope.

Section select.
Variable M : elgotExceptMonad.

Definition select l := let max := \max_(i <- l) i in (max, rem max l).

Definition muloflistover10d_body ln : M (nat + (seq nat) * nat)%type :=
  match ln with
    (l, n) => if l is h::tl then
                let (m, res) := select l in
                catch (if m <= 10 then
                         fail
                       else Ret (inr (res, m * n))) (Ret (inl n))
              else
                Ret (inl n)
  end.

Definition muloflistover10d := while muloflistover10d_body.

Definition muloflistover10 l := foldr (fun x z => if 10 < x then x * z else z) 1 l.

Lemma all_under10 l : (forall i, i \in l -> i <= 10) -> muloflistover10 l = 1.
Proof.
elim: l => //= n l' Hl H.
have [n10|_] := ltnP 10 n.
  contradict n10.
  by apply/negP; by rewrite -leqNgt H// mem_head.
rewrite Hl// => m Hl'.
by rewrite H// inE Hl' orbT.
Qed.

Lemma muloflistover10_aux(l : seq nat) (k : nat) : 10 < k -> k \in l ->
  k * muloflistover10 (rem k l) = muloflistover10 l.
Proof.
move=> Hk Hink.
rewrite /muloflistover10.
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

Lemma maxinseq (l : seq nat) : ~~ nilp l -> \max_(i <- l) i \in l.
Proof.
move => Hn.
rewrite -(in_tupleE l) big_tuple.
have [|x ->] := eq_bigmax (tnth (in_tuple l)).
  by rewrite cardT size_enum_ord lt0n.
by rewrite mem_tnth.
Qed.

Lemma muloflistover10wB (l : seq nat) (n : nat) :
  muloflistover10d (l, n) ≈ Ret (n * (muloflistover10 l)).
Proof.
move Hlen: (size l) => len.
move: n.
elim: len l Hlen.
  move => l /eqP/nilP Hl n.
  rewrite/muloflistover10/muloflistover10d/muloflistover10d_body Hl /=.
  by rewrite fixpointwB /= bindretf /= mulnS muln0 addn0.
move=> m IH l' Hs n.
rewrite/muloflistover10d/muloflistover10d_body fixpointwB /=.
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
rewrite -/muloflistover10d_body -/muloflistover10d.
have [Ht|Hf] := eqVneq h (\max_(i <- h :: l'') i).
  by rewrite {2}Ht (ifT _ _ Hm10) (IH l'' Hs) -Ht (mulnC h n) mulnA.
move: Hm10.
set k := \max_(i <- h :: l'') i => k10.
have Hmaxin : k \in (h :: l'') by rewrite maxinseq.
rewrite IH/=.
  rewrite /= (mulnC k n) -mulnA fun_if.
  rewrite (mulnA k h _) (mulnC k h) -mulnA (muloflistover10_aux _ _ k10) //.
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
