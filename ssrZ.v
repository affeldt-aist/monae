(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Require Import ZArith.

(***********************************)
(* SSReflect-like lemmas for Coq Z *)
(***********************************)

Local Open Scope Z_scope.

Notation "`| x |" := (Z.abs x) : zarith_ext_scope.
Notation "'Z<=nat'" := (Z.of_nat) (at level 9) : zarith_ext_scope.
Notation "'| x |" := (Z.abs_nat x) : zarith_ext_scope.
Notation "'gcdZ'" := Z.gcd : zarith_ext_scope.
Notation "'sgZ'" := Z.sgn : zarith_ext_scope.
Notation "'divZ'" := Z.div : zarith_ext_scope.

Local Open Scope zarith_ext_scope.

Lemma eqZP : Equality.axiom Zeq_bool.
Proof. move=> x y; apply: (iffP idP) => H; by apply/Zeq_is_eq_bool. Qed.

Canonical Z_eqMixin := EqMixin eqZP.
Canonical Z_eqType := Eval hnf in EqType Z Z_eqMixin.

Arguments eqZP [x y].

Definition addZ0 := Zplus_0_r.
Definition add0Z := Zplus_0_l.

Definition addZC : commutative Zplus := Zplus_comm.
Definition addZA : associative Zplus := Zplus_assoc.

Definition addZZ := Zplus_diag_eq_mult_2.

Definition subZ0 := Z.sub_0_r.
(* aka Zminus_0_r *)
Definition subZZ := Z.sub_diag.

Definition addZNE a b : a + - b = a - b := Z.add_opp_r a b.

Definition addZK n : cancel (Zplus^~ n) (Zminus^~ n).
Proof. move=> ?; exact: Z.add_simpl_r. Qed.

Definition addZN n : n + - n = 0 := Z.add_opp_diag_r n.
(* aka Zplus_opp_r *)

Lemma subZKC m n : m + (n - m) = n. Proof. exact: Zplus_minus. Qed.

Lemma eqZ_add2r p m n : (m + p = n + p) <-> (m = n).
Proof.
split; last by move=> ->.
rewrite -!(addZC p); exact: Z.add_reg_l.
Qed.
(* NB: Zplus_reg_l *)

Lemma eqZ_add2l p m n : (p + m = p + n) <-> (m = n).
Proof. split; [exact: Z.add_reg_l | by move=> ->]. Qed.

Lemma eqZ_opp x y : (- x = - y) <-> (x = y).
Proof. exact: Z.opp_inj_wd. Qed.

(* Z.leb_spec0 : forall x y : Z, Bool.reflect (x <= y) (x <=? y) *)
Lemma leZP {m n} : reflect (m <= n) (Zle_bool m n).
Proof. apply: (iffP idP); by apply Z.leb_le. Qed.

(* Z.ltb_spec0  forall x y : Z, reflect (x < y) (x <? y) *)
Lemma ltZP {m n} : reflect (m < n) (m <? n).
Proof. apply: (iffP idP); by apply Z.ltb_lt. Qed.

Lemma geZP {m n} : reflect (m >= n) (m >=? n).
Proof. apply: (iffP idP); rewrite /Z.ge /Zge_bool; by destruct (m ?= n). Qed.

Lemma gtZP {m n} : reflect (m > n) (m >? n).
Proof. apply: (iffP idP); rewrite /Z.gt /Zgt_bool; by destruct (m ?= n). Qed.

Lemma leZNgt n m : n <= m <-> ~ m < n.
Proof. split; [exact: Zle_not_lt | exact: Z.Private_Tac.not_gt_le]. Qed.
Definition leZNgt' := Z.leb_antisym.

Lemma ltZNge n m : n < m <-> ~ m <= n.
Proof. split; [exact: Zlt_not_le | exact: Z.Private_Tac.not_ge_lt]. Qed.
Definition ltZNge' := Z.ltb_antisym.

Definition ltZ_eqF := Z.lt_neq.
(* aka Zlt_not_eq *)

Lemma gtZ_eqF a b : a < b -> b <> a.
Proof. by move/ltZ_eqF/nesym. Qed.

Definition leZZ := Z.le_refl.
Definition leZZ' := Z.leb_refl.
Definition ltZZ := Z.lt_irrefl.
Definition ltZZ' := Z.ltb_irrefl.

Lemma leZ_trans {m n p} : n <= m -> m <= p -> n <= p.
Proof. exact: Z.le_trans. Qed.

Lemma ltZ_trans {m n p} : n < m -> m < p -> n < p.
Proof. exact: Z.lt_trans. Qed.

Lemma leZ_ltZ_trans {m n p} : n <= m -> m < p -> n < p.
Proof. exact: Z.le_lt_trans. Qed.

Lemma ltZ_leZ_trans {m n p} : n < m -> m <= p -> n < p.
Proof. exact: Z.lt_le_trans. Qed.

Definition oppZK := Z.opp_involutive.
Definition oppZ0 := Z.opp_0.

Definition ltZW {m n} : m < n -> m <= n := Z.lt_le_incl m n.
(* aka Zlt_le_weak *)
Lemma ltZW' {m n} : m <? n -> m <=? n.
Proof. move/ltZP => ?; apply/leZP; omega. Qed.

Lemma leZ_eqVlt m n : (m <= n) <-> (m = n) \/ (m < n).
Proof.
split => [|[->|]].
  case/Zle_lt_or_eq => ?; by [right|left].
exact: leZZ.
exact: ltZW.
Qed.
Lemma leZ_eqVlt' m n : (m <=? n) = (m == n) || (m <? n).
Proof.
apply/idP/idP => [/leZP/leZ_eqVlt[/eqP -> //|/ltZP ->]|/orP[/eqP ->|/ltZP]].
  by rewrite orbT.
by rewrite leZZ'.
by move/ltZP/ltZW'.
Qed.

Lemma ltZ_neqAle m n : (m <? n) = (m != n) && (m <=? n).
Proof.
apply/idP/idP => [/ltZP mn|].
  apply/andP; split; [apply/eqP; omega | exact/ltZW'/ltZP].
case/andP => /eqP H1 /leZP H2; apply/ltZP; omega.
Qed.

Definition mul0Z : left_zero 0 Z.mul := Zmult_0_l.
Definition mulZ0 : right_zero 0 Z.mul := Zmult_0_r.
Definition mul1Z : left_id 1 Z.mul := Zmult_1_l.
Definition mulZ1 : right_id 1 Z.mul := Zmult_1_r.
Definition mulZC : commutative Zmult := Zmult_comm.
Lemma mulN1Z n : -1 * n = - n.
Proof. by rewrite mulZC Zopp_eq_mult_neg_1. Qed.
Lemma mulZN1 n : n * -1 = - n.
Proof. by rewrite Z.opp_eq_mul_m1. Qed.

Definition mulZN x y : x * (- y) = - (x * y) := Z.mul_opp_r x y.
Definition mulNZ x y : (- x) * y = - (x * y) := Z.mul_opp_l x y.
Lemma mulZNN x y : (- x) * (- y) = x * y. Proof. by rewrite Z.mul_opp_opp. Qed.
(* NB: Z.mul_opp_comm : forall n m : Z, - n * m = n * - m *)
(* NB: Zopp_mult_distr_l : forall n m : Z, - (n * m) = - n * m *)

Lemma eqZ_mul2l p n m :  p <> 0 -> p * n = p * m <-> n = m.
Proof. move=> p0; split; [exact: Zmult_reg_l | by move=> ->]. Qed.

Lemma eqZ_mul2r p n m :  p <> 0 -> n * p = m * p <-> n = m.
Proof. move=> p0; split; [exact: Z.mul_reg_r | by move=> ->]. Qed.

Lemma mulZDl : left_distributive Zmult Zplus.
Proof. move=> *; by rewrite Z.mul_add_distr_r. (* aka Zmult_plus_distr_l *) Qed.
Lemma mulZDr : right_distributive Zmult Zplus.
Proof. move=> *; by rewrite Z.mul_add_distr_l. (* aka Zmult_plus_distr_r *) Qed.
Lemma mulZBl : left_distributive Zmult Zminus.
Proof. move=> *; by rewrite Z.mul_sub_distr_r. (* aka Zmult_minus_distr_r *) Qed.
Lemma mulZBr : right_distributive Zmult Zminus.
Proof. move=> *; by rewrite Zmult_minus_distr_l. Qed.

Lemma mulZ_eq0 (x y : Z) : (x * y == 0) = ((x == 0) || (y == 0)).
Proof.
apply/idP/idP => [/eqP/Zmult_integral[] ->| ]; try by rewrite eqxx // orbC.
case/orP => /eqP ->; by rewrite ?mulZ0 ?mul0Z.
Qed.

Definition mulZA : associative Zmult := Zmult_assoc.

Lemma leZ_oppr x y : (x <= - y) <-> (y <= - x).
Proof. by split=> /Z.opp_le_mono; rewrite oppZK. Qed.

Lemma leZ_oppl x y : (- x <= y) <-> (- y <= x).
Proof. by split=> /Z.opp_le_mono; rewrite oppZK. Qed.

Lemma ltZ_oppr x y : (x < - y) <-> (y < - x).
Proof. by split=> /Z.opp_lt_mono; rewrite oppZK. Qed.

Lemma ltZ_oppl x y : (- x < y) <-> (- y < x).
Proof. by split=> /Z.opp_lt_mono; rewrite oppZK. Qed.

Definition addZ_ge0 := Z.add_nonneg_nonneg. (* 0 <= n -> 0 <= m -> 0 <= n + m *)
(* aka Zplus_le_0_compat *)
Definition addZ_gt0 := Z.add_pos_pos.       (* 0 < n  -> 0 <= m -> 0 < n + m *)
Definition addZ_gt0wr := Z.add_nonneg_pos.  (* 0 <= n -> 0 < m  -> 0 < n + m  *)
Definition addZ_gt0wl := Z.add_pos_nonneg.  (* 0 < n  -> 0 <= m -> 0 < n + m *)

Definition leZ_add := Z.add_le_mono.        (* n <= m -> p <= q -> n + p <= m + q *)
(* aka Zplus_le_compat *)
Definition leZ_lt_add := Z.add_le_lt_mono.  (* x <= y -> z < t -> x + z < y + t *)
(* aka Zplus_le_lt_compat *)
Definition ltZ_le_add := Z.add_lt_le_mono.  (* x < y -> z <= t -> x + z < y + t *)

Lemma leZ_sub x y z t : x <= y -> t <= z -> x - z <= y - t.
Proof. exact: Z.sub_le_mono. Qed.

Lemma leZ_add2r {p m n} : m + p <= n + p <-> m <= n.
Proof. split; [exact: Zplus_le_reg_r | exact: Zplus_le_compat_r]. Qed.
Lemma leZ_add2r' p m n : (m + p <=? n + p) = (m <=? n).
Proof. by apply/idP/idP => [/leZP/leZ_add2r/leZP //|/leZP/leZ_add2r/leZP]. Qed.

Definition ltZ_add := Z.add_lt_mono.
(* aka Zplus_lt_compat *)

Lemma leZ_add2l {p m n} : p + m <= p + n <-> m <= n.
Proof. split; [exact: Zplus_le_reg_l | exact: Zplus_le_compat_l]. Qed.

Lemma ltZ_add2r p {m n : Z} : (m + p < n + p) <-> (m < n).
Proof. split; [exact/Zplus_lt_reg_r | exact/Zplus_lt_compat_r]. Qed.
Lemma ltZ_add2r' (p m n : Z) : (m + p <? n + p) = (m <? n).
Proof. by apply/idP/idP => [/ltZP/ltZ_add2r/ltZP|/ltZP/(@ltZ_add2r p)/ltZP]. Qed.

Lemma ltZ_add2l p {m n : Z} : (p + m  < p + n) <-> (m < n).
Proof. split; [exact/Zplus_lt_reg_l | exact/Zplus_lt_compat_l]. Qed.
Lemma ltZ_add2l' p {m n} : (p + m  <? p + n) = (m <? n).
Proof. by rewrite 2!(addZC p) ltZ_add2r'. Qed.

Lemma pmulZ_rge0 x y : 0 < x -> (0 <= x * y) <-> (0 <= y).
Proof. exact: Z.mul_nonneg_cancel_l. Qed.
(* NB: Zmult_gt_0_le_0_compat *)

(* TODO: Zmult_gt_0_lt_0_reg_r *)

(* TODO: Zmult_lt_0_reg_r *)

Lemma leZ_sub2r n {m p} : n <= m -> n - p <= m - p.
Proof. move=> H; omega. Qed.

Lemma ltZ_sub2r {n m p} : n < m -> n - p < m - p.
Proof. move=> H; omega. Qed.

Definition mulZ_gt0 := Z.mul_pos_pos.       (* 0 < n -> 0 < m -> 0 < n * m *)
(* aka Zmult_lt_0_compat *)
Definition mulZ_ge0 := Z.mul_nonneg_nonneg. (* 0 <= n -> 0 <= m -> 0 <= n * m *)
(* aka Zmult_le_0_compat *)

Lemma leZ_wpmul2r p n m : 0 <= p -> n <= m -> n * p <= m * p.
Proof. by move=> *; apply Zmult_le_compat_r. Qed.
Lemma leZ_wpmul2l p n m : 0 <= p -> n <= m -> p * n <= p * m.
Proof. by move=> *; apply Zmult_le_compat_l. Qed.
Lemma leZ_pmul m n p q : 0 <= n -> 0 <= m -> n <= p -> m <= q -> n * m <= p * q.
Proof. move=> *; exact/Zmult_le_compat. Qed.

Lemma ltZ_pmul m n p q : 0 < n -> 0 < m -> n <= p -> m < q -> n * m < p * q.
Proof. move=> *; exact: Zmult_lt_compat2. Qed.

Lemma leZ_pmul2r m n1 n2 : 0 < m -> n1 * m <= n2 * m <-> (n1 <= n2).
Proof.
move=> m0; split; first by apply: Zmult_le_reg_r; apply Z.lt_gt.
move=> *; apply leZ_wpmul2r => //; exact: ltZW.
Qed.
Lemma leZ_pmul2r' m n1 n2 : 0 < m -> n1 * m <=? n2 * m = (n1 <=? n2).
Proof. by move=> H; apply/idP/idP => /leZP/(leZ_pmul2r _ _ _ H)/leZP. Qed.

Lemma leZ_pmul2l m n1 n2 : 0 < m -> m * n1 <= m * n2 <-> (n1 <= n2).
Proof.
move=> m0; split; first by rewrite !(mulZC m); exact: Zmult_lt_0_le_reg_r.
move/Zmult_le_compat_l; apply; exact/ltZW.
Qed.
Lemma leZ_pmul2l' m n1 n2 : 0 < m -> m * n1 <=? m * n2 = (n1 <=? n2).
Proof. move=> ?; by rewrite -(mulZC n1) -(mulZC n2) leZ_pmul2r'. Qed.

Lemma ltZ_pmul2r m n1 n2 : 0 < m -> (n1 * m < n2 * m) <-> (n1 < n2).
Proof.
move=> ?; split; [exact/Zmult_gt_0_lt_reg_r/Z.lt_gt|exact/Zmult_lt_compat_r].
Qed.
Lemma ltZ_pmul2r' m n1 n2 : 0 < m -> n1 * m <? n2 * m = (n1 <? n2).
Proof. by move=> H; apply/idP/idP => /ltZP/(ltZ_pmul2r _ _ _ H)/ltZP. Qed.

Lemma ltZ_pmul2l m n1 n2 : 0 < m -> (m * n1 < m * n2) <-> (n1 < n2).
Proof. rewrite 2!(mulZC m); exact: ltZ_pmul2r. Qed.

Lemma leZ_subLR m n p : (m - n <= p) <-> (m <= n + p).
Proof. by rewrite Zle_plus_swap Z.sub_opp_r addZC. Qed.

Lemma ltZ_subLR m n p : (m - n < p) <-> (m < n + p).
Proof. by rewrite Zlt_plus_swap Z.sub_opp_r addZC. Qed.

Lemma leZ_subRL m n p : (n <= p - m) <-> (m + n <= p).
Proof.
split => H.
- move/(@leZ_add2l m) : H; by rewrite subZKC.
- by apply (@leZ_add2l m); rewrite subZKC.
Qed.

Lemma ltZ_subRL m n p : (n < p - m) <-> (m + n < p).
Proof.
split => H.
- move/(@ltZ_add2l m) : H; by rewrite subZKC.
- by apply (@ltZ_add2l m); rewrite subZKC.
Qed.
(* NB: Z.lt_add_lt_sub_r : forall n m p : Z, n + p < m <-> n < m - p *)
Lemma ltZ_subRL' m n p : (n <? p - m) = (m + n <? p).
Proof. by apply/idP/idP => /ltZP/ltZ_subRL/ltZP. Qed.

Definition ltZ_addr_subl := ltZ_subRL.

Lemma Z_of_nat_inj : forall x y, Z_of_nat x = Z_of_nat y -> x = y.
Proof. exact: Nat2Z.inj. Qed.

Lemma Z_of_nat_inj_neq x y : Z_of_nat x <> Z_of_nat y -> x <> y.
Proof. move=> H H'; by apply H; f_equal. Qed.

Lemma Z_of_nat_le n m : (n <= m)%nat = (Z<=nat n <=? Z<=nat m).
Proof.
case/boolP : (n <= m)%nat => H; first by apply/esym/leZP/Nat2Z.inj_le/leP.
apply/esym/negbTE; by apply: contra H => /leZP/Nat2Z.inj_le/leP.
Qed.

Lemma Z_of_nat_lt n m : (n < m)%nat = (Z<=nat n <? Z<=nat m).
Proof.
case/boolP : (n < m)%nat => H; first by apply/esym/ltZP/Nat2Z.inj_lt/ltP.
apply/esym/negbTE; by apply: contra H => /ltZP/Nat2Z.inj_lt/ltP.
Qed.

Definition normZ0 := Z.abs_0.

Lemma normZM : {morph Z.abs : x y / x * y : Z}. Proof. exact: Z.abs_mul. Qed.
(*Lemma Z.abs_mul : forall n m : Z, `|n * m| = `|n| * `|m|*)

Lemma geZ0_norm x : 0 <= x -> `|x| = x. Proof. exact: Z.abs_eq. Qed.

Lemma normZ_ge0 : forall z, 0 <= `| z |. Proof. by case. Qed.
