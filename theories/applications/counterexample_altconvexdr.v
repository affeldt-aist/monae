(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2025 monae authors, license: LGPL-2.1-or-later               *)
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint finmap.
From mathcomp Require Import boolp classical_sets reals unstable.
From mathcomp Require Import ring.
From mathcomp Require Import archimedean interval interval_inference.
From mathcomp Require Import constructive_ereal topology sequences exp.
From infotheo Require Import classical_sets_ext realType_ext fdist proba.
From infotheo Require Import fsdist convex.
From HB Require Import structures.
Require Import preamble hierarchy monad_lib proba_lib alt_lib.

(**md**************************************************************************)
(* # collapse of the probabilistic choice in altConvexDrMonad                 *)
(*                                                                            *)
(* This file exhibits undesirable consequences of combining the probabilistic *)
(* and nondeterministic choice operators together with the right-             *)
(* distributivity of the bind operator over the probabilistic choice.         *)
(*                                                                            *)
(* ```                                                                        *)
(*  altConvexDrMonad == altCIMonad (nondet. choice)                           *)
(*                    + convexDrMonad (prob. choice and right-distr.)         *)
(* ```                                                                        *)
(*                                                                            *)
(* References:                                                                *)
(* - [Abou-Saleh, et al.]:                                                    *)
(*   Abou-Saleh, F., Cheung, K.-H., and Gibbons, J. (2016).                   *)
(*   Reasoning about probability and nondeterminism.                          *)
(*   In POPL workshop on Probabilistic Programming Semantics.                 *)
(*   https://www.cs.ox.ac.uk/jeremy.gibbons/publications/prob-nondet.pdf      *)
(* - [Keimel, et al.]:                                                        *)
(*   Keimel, K. and Plotkin, G. D. (2017).                                    *)
(*   Mixed powerdomains for probability and nondeterminism.                   *)
(*   Logical Methods in Computer Science, 13(1:2):1–84.                       *)
(*   https://homepages.inf.ed.ac.uk/gdp/publications/mixed_powerdomains.pdf   *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Order.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope monae_scope.
Local Open Scope proba_monad_scope.

Local Notation "{% q }" := {| Prob.p := q; Prob.Op1 := Prob.O1 _ |}
                             (at level 0, format "{% q }").

Section to_be_removed.
Local Open Scope ring_scope.
Lemma le_val {R : realType} : {mono @Prob.p R : x y / (x <= y)%O >-> (x <= y)%O}.
Proof. by try exact: le_val. Qed.
Lemma lt_val {R : realType} : {mono @Prob.p R : x y / (x < y)%O >-> (x < y)%O}.
Proof. by try exact: lt_val. Qed.
End to_be_removed.

(* TODO: move the three sections below to infotheo *)

Section move_to_realType_ext.
Canonical magnified_prob.
End move_to_realType_ext.

Section prob_orderedConvType.
Variable (R : realType).

(* the OrderedConvexSpace interface should (have a subclass that) include this
   compabitility of conv with <= *)
Local Lemma le_convl (p b : {prob R}) :
  {homo (fun a => conv p a b) : a a'  / a <= a'}.
Proof. by move=> ? ? ?; rewrite -le_val/= lerD2r ler_wpM2l. Qed.

Local Lemma le_convr (p a : {prob R}) :
  {homo conv p a : b b'  / b <= b'}.
Proof. by move=> ? ? ?; rewrite 2!(convC _ a) le_convl. Qed.

Local Lemma conv_itv (a b p : {prob R}) :
  a <= b -> conv p a b \in `[a, b].
Proof.
move=> ab; rewrite in_itv/=.
rewrite -[X in X <= _ <= _](convmm p a) -[X in _ <= _ <= X](convmm p b).
by rewrite le_convl// le_convr.
Qed.

Local Lemma conv_ge_le (a b p : {prob R}) : a <= b -> a <= conv p a b <= b.
Proof. by move/(conv_itv p). Qed.

End prob_orderedConvType.

Section conv_conv.
Local Open Scope ring_scope.
Local Open Scope convex_scope.
Variables (R : realType) (T : convType R) (p q r : {prob R}) (x y : T).

(* TODO: better name *)
Local Lemma conv_ge_leK (pr : p < r) :
  magnified_prob pr (conv_ge_le q (ltW pr)) = q.
Proof.
apply/val_inj => /=.
rewrite /magnified_weight /=.
rewrite opprD addrCA.
rewrite -[r in r - _]mul1r -mulrBl -/(_.~) onemK.
rewrite -mulrN -mulrDr addrC -mulrA divff ?mulr1//.
by rewrite lt0r_neq0// subr_gt0.
Qed.

Lemma conv_conv :
  p <= r -> x <| p <|q|> r|> y = (x <|p|> y) <|q|> (x <|r|> y).
Proof.
rewrite le_eqVlt => /orP[/eqP->|pr]; first by rewrite !convmm.
by rewrite -(magnify_conv _ _ pr (conv_ge_le q (ltW pr))) conv_ge_leK.
Qed.

End conv_conv.

#[short(type=altConvexDrMonad)]
HB.structure Definition MonadAltConvexDr {R : realType} :=
  { M of isMonadAltCI M & isMonadConvexDr R M }.

Section choiceDalt.
Variables (R : realType).

(* technical equality from [Abou-Saleh, et al.] *)
Local Lemma altEbindarb (M : altMonad) (T : Type) (x y : M T) :
  x [~] y = arb >>= fun b => if b then x else y.
Proof. by rewrite alt_bindDl !bindretf. Qed.

Local Lemma choiceDif (M : convexMonad R) (T : Type)
  (b : bool) (p : {prob R}) (x y z w : M T) :
  (if b then x <| p |> y else z <| p |> w) =
  (if b then x else z) <| p |> (if b then y else w).
Proof. by case: b. Qed.

(* the right distr. of bind implies the distr. of nondeterminism over probability *)
Fact choiceDalt (M : altConvexDrMonad R) (T : Type) (p : {prob R}) :
  right_distributive (fun x y : M T => x [~] y) (fun x y : M T => x <| p |> y).
Proof.
move=> x y z.
rewrite -[in LHS](choicemm p x) altEbindarb.
transitivity (arb >>= (fun b : bool => (if b then x else y) <|p|> if b then x else z)).
  by congr (@bind M bool T (@arb M) _); apply: funext => b; rewrite choiceDif.
by rewrite choice_bindDr -!altEbindarb.
Qed.

End choiceDalt.

Section collapse.
Variables (R : realType) (M : altConvexDrMonad R) (T : Type).

Local Definition magnify_choice p q r x y pq prq :=
  @magnify_choice R M T p q r x y pq prq.

Local Lemma collapse_hull (x y : M T) (p r : {prob R}) :
  p < r -> x <|p|> y = x <|r|> y ->
  forall q, p <= q <= r -> x <|q|> y = x <|p|> y.
Proof.
by move=> pr xpry q pqr; rewrite -(magnify_choice x y pr pqr) xpry choicemm.
Qed.

Section collapse_left.

Variables (x y : M T) (p q r : {prob R}).
Variables (qpr : q < p < r) (q_gt0 : {%0} < q).

Let q_pos := PosNum q_gt0.
Canonical q_pos.

Let p_gt0 : {%0} < p := lt_trans q_gt0 (andP qpr).1.
Let r_gt0 : {%0} < r := lt_trans p_gt0 (andP qpr).2.
Let p_pos := PosNum p_gt0.
Let r_pos := PosNum r_gt0.
Canonical p_pos.
Canonical r_pos.

Let rp_gt0 : 0 < Prob.p r / Prob.p p := divr_gt0 r_gt0 p_gt0.
Let pr_gt0 : 0 < Prob.p p / Prob.p r := divr_gt0 p_gt0 r_gt0.
Let rpXk_gt0 {k} : 0 < (Prob.p r / Prob.p p)^+k := exprn_gt0 k rp_gt0.
Let prXk_gt0 {k} : 0 < (Prob.p p / Prob.p r)^+k := exprn_gt0 k pr_gt0.

Local Definition q_ := geometric (Prob.p q) (Prob.p r / Prob.p p).
Local Lemma qkE {k} : q_ k = Prob.p q * (Prob.p r / Prob.p p) ^+ k.
Proof. by []. Qed.

Local Lemma qSE {k} : q_ k.+1 = q_ k * (Prob.p r / Prob.p p).
Proof. by rewrite qkE exprS (mulrC (_ / _)) mulrA -qkE. Qed.

Let qk_gt0 {k} : 0 < q_ k.
Proof. by rewrite qkE mulr_gt0. Qed.

Local Lemma qk_eqE a k :
  0 < a -> (q_ k == a) = ((ln a - ln q) / (ln r - ln p) == k%:R).
Proof.
move=> a_gt0.
have lnrp_neq0 : ln r - ln p != 0.
  by rewrite lt0r_neq0// subr_gt0 ltr_ln//; exact: (andP qpr).2.
have[->|k_neq0]:= eqVneq k 0.
  rewrite qkE expr0 mulr1 mulf_eq0 subr_eq0 invr_eq0.
  rewrite (negPf lnrp_neq0) orbF eq_sym.
  apply/idP/idP; first by move/eqP->.
  by move/eqP/ln_inj/eqP; apply.
have->: (q_ k == a) = (ln (q_ k) == ln a).
  apply/idP/idP; first by move/eqP->.
  by move/eqP/ln_inj/eqP; apply => //; rewrite posrE.
rewrite qkE lnM ?posrE// lnXn// ln_div ?posrE// -[in LHS](mulr_natr _ k) addrC.
rewrite eq_sym -subr_eq [in LHS]mulrC.
by rewrite -[X in (X == _) = _]mulr1 -eqr_div// ?pnatr_eq0// divr1.
Qed.

Local Lemma qk_leE a k :
  0 < a -> (q_ k <= a) = (k%:R <= (ln a - ln q) / (ln r - ln p)).
Proof.
move=> a_gt0.
rewrite -[in X in X = _]ler_ln ?posrE// qkE.
rewrite lnM ?posrE// lnXn// ln_div ?posrE// -[in X in X = _]mulr_natr.
rewrite -lerBrDl ler_pdivlMr; first by rewrite mulrC.
by rewrite ltrBrDl addr0 ltr_ln ?posrE//; exact: (andP qpr).2.
Qed.

Local Lemma qk_gtE a k :
  0 < a -> (a < q_ k) = ((ln a - ln q) / (ln r - ln p) < k%:R).
Proof. by move=> a_gt0; rewrite ltNge qk_leE// -ltNge. Qed.

Let Th := (ln p - ln q) / (ln r - ln p).

Local Lemma Th_ge0 : 0 <= Th.
Proof.
by have/andP[??]:= qpr; apply: divr_ge0; rewrite subr_ge0 ler_ln// ltW.
Qed.

Local Lemma qk_prob_proof k : k%:R <= Th -> 0 <= q_ k <= 1.
Proof. by rewrite (ltW qk_gt0)/= /Th -qk_leE// => /le_trans; apply. Qed.

Let qk_prob k (kTh : k%:R <= Th) := Prob.mk_ (qk_prob_proof kTh).
Canonical qk_prob.

Local Lemma qS_le_r k : k%:R <= Th -> q_ k.+1 <= Prob.p r.
Proof.
rewrite qSE -ler_pdivlMr// invfM mulrA divff ?lt0r_neq0// div1r invrK.
by rewrite /Th -qk_leE.
Qed.

Local Lemma qS_prob_proof k : k%:R <= Th -> 0 <= q_ k.+1 <= 1.
Proof. by rewrite (ltW qk_gt0)/=; move/qS_le_r/le_trans; apply. Qed.
Let qS_prob k (kTh : k%:R <= Th) := Prob.mk_ (qS_prob_proof kTh).
Canonical qS_prob.

Local Lemma qk_magnifiable k (kTh : k%:R <= Th) : {%0} <= qk_prob kTh <= p.
Proof. by rewrite -!le_val/= prob_ge0//= qk_leE. Qed.

Local Lemma qS_prob_conv k (kTh : k%:R <= Th) :
  qS_prob kTh = conv (magnified_prob p_gt0 (qk_magnifiable kTh)) {%0} r.
Proof.
apply/val_inj => /=.
rewrite /magnified_weight/= mulr0 add0r subr0 qSE.
by rewrite (mulrBl _^-1) divff ?lt0r_neq0// -/(_.~) onemK (mulrC _ _^-1) mulrA.
Qed.

Section collapse_left_proof.
Variable (xpry : x <|p|> y = x <|r|> y).

Local Lemma conv_qS k (kTh : k%:R <= Th) :
  x <|qS_prob kTh|> y = x <|qk_prob kTh|> y.
Proof.
rewrite qS_prob_conv choice_conv conv_conv//.
by rewrite -!choice_conv -xpry magnify_choice.
Qed.

Local Lemma conv_qk_aux k (SkTh : k.+1%:R <= Th) (kTh : k%:R <= Th) :
  x <|qk_prob SkTh|> y = x <|qk_prob kTh|> y.
Proof. by rewrite -[in RHS]conv_qS; congr conv; apply/val_inj. Qed.

Local Lemma conv_qk k (kTh : k%:R <= Th) :
  x <|q|> y = x <|qk_prob kTh|> y.
Proof.
elim: k kTh.
  move=> H; suff: q = qk_prob H by move->.
  by apply/val_inj => /=; rewrite /q_ /= expr0 mulr1.
move=> k IHk SkTh.
by rewrite conv_qk_aux// (le_trans _ SkTh)// ler_nat.
Qed.

Local Lemma conv_q_qS k (kTh : k%:R <= Th) :
  x <|q|> y = x <|qS_prob kTh|> y.
Proof. by rewrite conv_qS -conv_qk. Qed.

Local Lemma collapse_left :  x <|q|> y = x <|p|> y.
Proof.
case/andP: qpr => qp pr.
have:= Th_ge0; rewrite -truncn_le; set k := Num.truncn Th.
move=> kTh; rewrite (conv_q_qS kTh).
apply: (collapse_hull (andP qpr).2) => //.
rewrite -!le_val/= qS_le_r// andbT ltW//.
by rewrite qk_gtE// truncnS_gt.
Qed.

End collapse_left_proof.
End collapse_left.

Section collapse_right.

Variables (x y : M T) (p q r : {prob R}).
Variables (qpr : p < r < q) (q_lt1 : q < {%1}).
Variable (xpry : x <|p|> y = x <|r|> y).

Local Lemma collapse_right : x <|q|> y = x <|r|> y.
Proof.
rewrite (choiceC q) (choiceC r).
apply: (@collapse_left y x {%r.~} {%q.~} {%p.~}).
- by rewrite -!lt_val -!onem_lt andbC.
- by rewrite -lt_val onem_gt0.
by rewrite -!choiceC xpry.
Qed.

End collapse_right.

(* [Keimel et al.] A.2 *)
Lemma propagate_collapse (x y : M T) (p r : {prob R}) :
  p != r ->
  x <|p|> y = x <|r|> y ->
  forall q1 q2 : {oprob R}, x <|q1|> y = x <|q2|> y.
Proof.
wlog pr : p r / p < r.
  move=> + /[dup] pr.
  rewrite real_neqr_lt ?num_real//= => + /orP [] pq0'; first exact.
  move=> /(_ r p) /[swap] /[dup] -> /esym /[swap] /[apply]; apply => //.
  by rewrite eq_sym.
move=> _ xpry.
suff xqpr : forall q : {oprob R}, x <|q|> y = x <|p|> y.
  by move=> q1 q2; rewrite [LHS]xqpr [RHS]xqpr.
move=> q.
have[qr|rq] := leP (q : {prob R}) r.
  have[pq|qp] := leP p q; first by apply/(collapse_hull pr xpry)/andP; split.
  apply: (@collapse_left x y p q r); [by rewrite qp pr| | by []].
  by rewrite -lt_val/= oprob_gt0.
rewrite xpry.
apply: (@collapse_right x y p q r); [by rewrite pr rq| | by []].
by rewrite -lt_val/= oprob_lt1.
Qed.

End collapse.

Arguments propagate_collapse {R M T}.

Section collapsed_choice.
Variables (R : realType) (M : altConvexDrMonad R) (T : Type).

Local Lemma choice_nondetAR (p : {prob R}) (x y : M T) :
  (x <|p|> y) [~] x = x <|p|> (x [~] y).
Proof. by rewrite altC choiceDalt altmm. Qed.

Local Lemma choice_nondetAL (p : {prob R}) (x y : M T) :
  (x <|p|> y) [~] y = (x [~] y) <|p|> y.
Proof. by rewrite altC choiceDalt altmm altC. Qed.

Local Lemma expand_nondet (p : {prob R}) (x y : M T) :
  x <|p|> y = (x <|p|> (x [~] y)) <|p|> ((x [~] y) <|p|> y).
Proof. by rewrite -[LHS]altmm choiceDalt choice_nondetAR choice_nondetAL. Qed.

Local Lemma witness_at_sqr (p : {prob R}) (x y : M T) :
  x <|{%(p:R) ^+ 2}|> (x [~] y) = x <|p|> (x [~] y).
Proof.
have[->|pneq1]:= eqVneq p 1%:pr.
  by congr (x <| _ |> (x [~] y)); apply/val_inj => /=; rewrite expr1n.
rewrite [RHS]expand_nondet altA altmm.
rewrite -choiceA' !choicemm.
congr (x <| _ |> (x [~] y)).
by apply/val_inj; rewrite /=p_of_rsE.
Qed.

(* move to infotheo? *)
Lemma oprob_neq_sqr (p : {oprob R}) : {%(p:R) ^+ 2} != p.
Proof.
rewrite -(inj_eq val_inj)/= -[eqbRHS]mulr1 -eqr_div ?divff ?oprob_neq0//.
by rewrite divr1 oprob_neq1.
Qed.

Local Lemma collapse_beside_nondetR (p q : {oprob R}) (x y : M T) :
  x <|p|> (x [~] y) = x <|q|> (x [~] y).
Proof.
by apply: propagate_collapse; [exact: (oprob_neq_sqr p)|exact: witness_at_sqr].
Qed.

Local Lemma collapse_beside_nondetL (p q : {oprob R}) (x y : M T) :
  (x [~] y) <|p|> y = (x [~] y) <|q|> y.
Proof.
rewrite [RHS]choiceC -choice_nondetAL choiceC choice_nondetAR [in RHS]altC.
by have:= (collapse_beside_nondetR p.~%:opr q.~%:opr); exact.
Qed.

(* (the essential part of) [Keimel et al.] A.3 *)
Theorem collapsed_choice_collapsed (p q : {oprob R}) (x y : M T) :
  x <|p|> y = x <|q|> y.
Proof.
set Y := RHS.
rewrite expand_nondet.
rewrite (collapse_beside_nondetL p q).
rewrite (collapse_beside_nondetR p q).
rewrite choiceACA.
rewrite (collapse_beside_nondetL p q).
rewrite (collapse_beside_nondetR p q).
by rewrite -expand_nondet.
Qed.

End collapsed_choice.
