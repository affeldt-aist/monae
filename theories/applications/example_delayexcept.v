From mathcomp Require Import all_ssreflect.
From mathcomp Require Import boolp.
Require Import preamble hierarchy monad_lib fail_lib state_lib.

Local Open Scope monae_scope.
Notation "a '≈' b" := (wBisim a b).

Section delayexcept_example.
Variable M : delayExceptMonad.

Definition select (l: seq nat) := let max := \max_(i <- l) i in (max, rem max l).
(*bigopでselectを定義する*)
Definition muloflistover10d_body (ln: (seq nat)*nat): M (nat + (seq nat)*nat)%type :=
  match ln with (l, n) =>
                  match l with
                    |[::] => @ret M _ (inl n)
                    |h::tl => let (m,res) := select l in catch (if m <= 10  then fail else @ret M _ (inr (res, m*n))) (@ret M _ (inl n))
end
end.
Definition muloflistover10d := while muloflistover10d_body.
Definition muloflistover10 (l: seq nat) :=  foldr (fun x z => if 10 < x then x*z else z) 1 l.
Lemma all_under10 (l: seq nat): (forall i, i \in l -> i <= 10) -> muloflistover10 l = 1.
Proof.
elim: l => //= n l' Hl H.
case/boolP: (10 < n) => H10.
- contradict H10.
  apply/negP.
  rewrite -leqNgt.
  apply H.
  rewrite in_cons.
  apply /orP.
  left.
  by apply/eqP.
- apply Hl.
  move => m Hl'.
  apply H.
  rewrite in_cons.
  apply/orP.
  by right.
Qed.
Lemma muloflistover10_aux(l:seq nat)(k: nat): 10 < k -> k \in l -> k * muloflistover10 (rem k l) = muloflistover10 l.
move => Hk Hink.
rewrite/muloflistover10.
elim: l Hink => //= n l' IH Hink.
case Hnk: (n == k).
case/boolP: (10 < n) => Hn10.
- move: Hnk => /eqP Hnk.
  by rewrite Hnk.
  move: Hnk => /eqP Hnk.
  contradict Hk.
  rewrite -Hnk.
  by apply/negP.
  have Hkl': k \in l'.
    move: Hink.
    by rewrite in_cons eq_sym Hnk /=.
  simpl.
  case/boolP : (10 < n) => Hn.
  rewrite -(IH Hkl').
  by rewrite mulnA (mulnC k n) -mulnA.
  by rewrite -(IH Hkl').
Qed.
Lemma maxinseq (l:seq nat): ~~(nilp l) -> \max_(i <- l) i \in l.
Proof.
(*seq_sub in Fintype.v*)
(*ex_maxn *)
move => Hn.
rewrite -(in_tupleE l).
rewrite big_tuple.
case: (eq_bigmax (tnth (in_tuple l))).
- rewrite cardT.
  rewrite size_enum_ord.
  rewrite lt0n. done.
- move => x ->.
  by rewrite mem_tnth.
Qed.

Lemma muloflistover10E (l: seq nat)(n: nat): muloflistover10d (l, n) ≈ @ret _ _ (n * (muloflistover10 l)).
Proof.
move Hlen: (size l) => len.
move: n.
elim: len l Hlen.
- move => l /eqP/nilP Hl n.
  by rewrite/muloflistover10/muloflistover10d/muloflistover10d_body Hl /= fixpointE /= bindretf /= mulnS muln0 addn0.
- move => m IH l' Hs n.
  rewrite/muloflistover10d/muloflistover10d_body fixpointE /=.
  elim: l' Hs => //= [h l''] _ Hs.
  case: Hs => Hs.
  case:ifP.
  case/boolP: (\max_(i <- (h :: l'')) i <= 10) => [/bigmax_leqP_seq Hm10|Hm10].
    + rewrite catchfailm.
      rewrite bindretf /=.
      have -> : (10 < h) = false.
        apply/negP.
        apply/negP.
        rewrite -leqNgt.
        apply Hm10 => //=.
        rewrite in_cons.
        by rewrite eq_refl.
      rewrite all_under10.
      * by rewrite mulnS muln0 addn0.
      * move => i Hini.
        apply Hm10 => //=.
        rewrite in_cons.
        by rewrite Hini orbT.
      rewrite catchret bindretf /=.
      rewrite -/muloflistover10d_body -/muloflistover10d.
      case Hh : (h == \max_(i <- (h :: l'')) i).
        * move: Hh Hm10 => /eqP Hh.
          rewrite -ltnNge -Hh.
          case: (10 < h) => //= _.
          rewrite (IH l'' Hs).
          by rewrite (mulnC h n) mulnA.
        * move:Hm10.
          set k := \max_(i <- (h :: l'')) i.
          have Hmaxin: k \in (h::l'').
            subst k.
            apply maxinseq.
            by [].
          rewrite IH.
          ** rewrite -ltnNge /= (mulnC k n) -mulnA.
             have -> : (k * (if 10 < h then h * muloflistover10 (rem k l'') else muloflistover10 (rem k l''))) = ((if 10 < h then h * (k * muloflistover10 (rem k l'')) else k*muloflistover10 (rem k l''))).
               case/boolP : (10 < h) => Hh10 //=.
               by rewrite mulnA (mulnC k h) -mulnA.
             move => Hk.
             rewrite (muloflistover10_aux _ _ Hk) /=.
               *** by [].
               *** move: Hmaxin.
                   rewrite in_cons.
                   subst k.
                   by rewrite eq_sym Hh /=.
           ** subst k.
              rewrite /= size_rem.
              *** rewrite Hs.
                  case: l'' Hs Hh Hmaxin => [? contr|h' l'''  Hs ? ?].
                  **** contradict contr.
                       by rewrite big_cons big_nil maxn0 eq_refl.
                  **** rewrite prednK //=.
                       rewrite -Hs /=.
                       by apply ltn0Sn.
              *** move: Hmaxin.
                  by rewrite in_cons eq_sym Hh /=.
Qed.
