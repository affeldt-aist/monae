(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2020 monae authors, license: LGPL-2.1-or-later               *)
Require Import ZArith.
From mathcomp Require Import all_ssreflect.
From mathcomp Require boolp.
From infotheo Require Import ssrZ.
Require Import monae_lib hierarchy. (*monad_lib fail_lib state_lib.*)

(******************************************************************************)
(*                         Type store examples                                *)
(*                                                                            *)
(******************************************************************************)

Local Open Scope monae_scope.

Inductive ml_type : Set :=
  | ml_int
  | ml_bool
  | ml_unit
  | ml_ref (_ : ml_type)
  | ml_arrow (_ : ml_type) (_ : ml_type)
  | ml_undef.

Inductive undef_t : Set := Undef.

Variant loc : ml_type -> Type := mkloc T : nat -> loc T.

Module MLtypes.
Definition ml_type_eq_dec (T1 T2 : ml_type) : {T1=T2}+{T1<>T2}.
revert T2; induction T1; destruct T2;
  try (right; intro; discriminate); try (now left);
  try (case (IHT1_5 T2_5); [|right; injection; intros; contradiction]);
  try (case (IHT1_4 T2_4); [|right; injection; intros; contradiction]);
  try (case (IHT1_3 T2_3); [|right; injection; intros; contradiction]);
  try (case (IHT1_2 T2_2); [|right; injection; intros; contradiction]);
  (case (IHT1 T2) || case (IHT1_1 T2_1)); try (left; now subst);
    right; injection; intros; contradiction.
Defined.

Local Definition ml_type := ml_type.
Local Definition undef := Undef.
Local Definition loc := loc.
Local Definition locT := [eqType of nat].
Definition loc_id {T} (l : loc T) := let: mkloc _ n := l in n.

Section with_monad.
Context [M : Type -> Type].

(* Generated type translation function *)
Fixpoint coq_type (T : ml_type) : Type :=
  match T with
  | ml_int => nat
  | ml_bool => bool
  | ml_unit => unit
  | ml_arrow T1 T2 => coq_type T1 -> M (coq_type T2)
  | ml_ref T1 => loc T1
  | ml_undef => undef_t
  end.
End with_monad.
Local Definition ml_undef := ml_undef.
End MLtypes.

Module IMonadTS := MonadTypedStore (MLtypes).
Import MLtypes.
Import IMonadTS.

Section factorial.
Variable M : typedStoreMonad.
Notation coq_type := (@MLtypes.coq_type M).

Fixpoint fact_ref (r : loc ml_int) (n : nat) : M unit :=
  if n is m.+1 then cget r >>= fun p => cput r (n * p) >> fact_ref r m
  else skip.

Theorem fact_ref_ok n :
  crun (cnew ml_int 1 >>= fun r => fact_ref r n >> cget r) = Some (fact_rec n).
Proof.
set fn := fact_rec n.
set m := n.
set s := 1.
have smn : s * fact_rec m = fn by rewrite mul1n.
elim: m s smn => [|m IH] s /= smn.
  rewrite /fact_ref -smn muln1.
  under eq_bind do rewrite bindskipf.
  by rewrite cnewgetret crunret // crunnew0.
under eq_bind do rewrite bindA.
rewrite cnewget.
under eq_bind do rewrite bindA.
by rewrite cnewput IH // (mulnC m.+1) -mulnA.
Qed.
End factorial.

Section forloop.
Variable M : monad.

Definition forloop (n_1 n_2 : nat) (b : nat -> M unit) : M unit :=
  if n_2 < n_1 then Ret tt else
  iteri (n_2.+1 - n_1)
       (fun i (m : M unit) => m >> b (n_1 + i))
       skip.

Lemma iteriSr T n (f : nat -> T -> T) x :
  iteri n.+1 f x = iteri n (f \o succn) (f 0 x).
Proof. by elim: n x => // n IH x /=; rewrite -IH. Qed.

Lemma iteriD T n m (f : nat -> T -> T) x :
  iteri (n + m) f x = iteri m (f \o addn n) (iteri n f x).
Proof. by elim: n x f => // n IH x f; rewrite addSn iteriSr IH iteriSr. Qed.

Lemma iteri_bind n (f : nat -> M unit) (m1 m2 : M unit) :
  iteri n (fun i (m : M unit) => m >> f i) (m1 >> m2) =
  m1 >> iteri n (fun i (m : M unit) => m >> f i) m2.
Proof. by elim: n m2 => // n IH m2; rewrite iteriS IH !bindA. Qed.

Lemma forloopS m n (f : nat -> M unit) :
  m <= n -> forloop m n f = f m >> forloop m.+1 n f.
Proof.
rewrite /forloop => mn.
rewrite ltnNge mn /= subSS subSn // iteriSr bindskipf.
rewrite -[f _]bindmskip iteri_bind addn0 ltnS -subn_eq0.
case: (n-m) => //= k.
rewrite addSnnS; apply eq_bind => _; congr bind.
apply eq_iteri => i x; by rewrite addSnnS.
Qed.

Lemma forloop0 m n (f : nat -> M unit) :
  m > n -> forloop m n f = skip.
Proof. by rewrite /forloop => ->. Qed.
End forloop.
Arguments forloop {M}.

Section fact_for.
Variable M : typedStoreMonad.
Notation coq_type := (@MLtypes.coq_type M).

Notation "'do' x <- m ; e" := (m >>= (fun x => e))
  (at level 60, x name, m at level 200, e at level 60).

Definition fact_for (n : coq_type ml_int) : M (coq_type ml_int) :=
  do v <- cnew ml_int 1;
  do _ <-
  (do u <- Ret 1;
   do v_1 <- Ret n;
   forloop u v_1
     (fun i =>
        do v_1 <- (do v_1 <- cget v; Ret (v_1 * i));
        cput v v_1));
  cget v.

Theorem fact_for_ok n : crun (fact_for n) = Some (fact_rec n).
Proof.
rewrite /fact_for.
under eq_bind do rewrite !bindA !bindretf.
transitivity (crun (cnew ml_int (fact_rec n) >> Ret (fact_rec n) : M _));
  last by rewrite crunret // crunnew0.
congr crun.
rewrite -{1}/(fact_rec 0).
pose m := n.
have -> : 0 = n - m by rewrite subnn.
have : m <= n by [].
elim: m => [|m IH] mn.
  rewrite subn0.
  under eq_bind do rewrite forloop0 ?leqnn // bindretf -cgetret.
  by rewrite cnewget.
rewrite subnSK //.
under eq_bind do (rewrite forloopS; last by apply leq_subr).
under eq_bind do rewrite !bindA.
rewrite cnewget.
under eq_bind do rewrite bindretf.
rewrite cnewput -IH; last by apply ltnW.
by rewrite subnS mulnC -(@prednK (n-m)) // lt0n subn_eq0 -ltnNge.
Qed.
End fact_for.

Section fibonacci.
Variable M : typedStoreMonad.
Notation coq_type := (@MLtypes.coq_type M).

Fixpoint fibo_rec n :=
  if n is m.+1 then
    if m is k.+1 then fibo_rec k + fibo_rec m else 1
  else 1.

Fixpoint fibo_ref n (a b : loc ml_int) : M unit :=
  if n is n.+1 then
    cget a >>= (fun x => cget b >>= fun y => cput a y >> cput b (x + y))
           >> fibo_ref n a b
  else skip.

Theorem fibo_ref_ok n :
  crun (cnew ml_int 1 >>=
             (fun a => cnew ml_int 1 >>= fun b => fibo_ref n a b >> cget a))
  = Some (fibo_rec n).
Proof.
set x := 1.
pose y := x.
rewrite -{2}/y.
pose i := n.
rewrite -[in LHS]/i.
have : (x, y) = (fibo_rec (n-i), fibo_rec (n.+1-i)).
  by rewrite subnn -addn1 addKn.
have : i <= n by [].
elim: i x y => [|i IH] x y Hi.
  rewrite !subn0 => -[] -> ->.
  rewrite -/(fibo_rec n.+1).
  under eq_bind do under eq_bind do rewrite /= bindskipf.
  rewrite -cnewchk.
  under eq_bind do rewrite -cgetret cchknewget.
  by rewrite cnewget -bindA crunret // crunnew // crunnew0.
rewrite subSS => -[] Hx Hy.
rewrite -(IH y (x + y) (ltnW Hi)); last first.
  subst x y.
  congr pair.
  case: n Hi {IH} => // n.
  rewrite subSS ltnS => Hi.
  by rewrite -addn2 -addn1 -addnBAC // -addnBAC // addn2 addn1.
rewrite /=.
under eq_bind do under eq_bind do rewrite !bindA.
rewrite -cnewchk.
under eq_bind do rewrite cchknewget.
rewrite cnewget.
under eq_bind do under eq_bind do rewrite !bindA.
under eq_bind do rewrite cnewget.
under eq_bind do under eq_bind do rewrite !bindA.
rewrite -[in LHS]cnewchk.
under eq_bind do rewrite cchknewput.
rewrite cnewput.
by under eq_bind do rewrite cnewput.
Qed.
End fibonacci.

Require Import PrimInt63.
Require Sint63.

Module MLtypes63.
Local Definition ml_type_eq_dec := ml_type_eq_dec.
Local Definition ml_type := ml_type.
Local Definition undef := Undef.
Local Definition loc := loc.
Local Definition locT := [eqType of nat].
Local Definition loc_id := @loc_id.

Section with_monad.
Context [M : Type -> Type].

(* Generated type translation function *)
Fixpoint coq_type (T : ml_type) : Type :=
  match T with
  | ml_int => int
  | ml_bool => bool
  | ml_unit => unit
  | ml_arrow T1 T2 => coq_type T1 -> M (coq_type T2)
  | ml_ref T1 => loc T1
  | ml_undef => undef_t
  end.
End with_monad.
Local Definition ml_undef := ml_undef.
End MLtypes63.

Module IMonadTS63 := hierarchy.MonadTypedStore (MLtypes63).
Import MLtypes63.
Import IMonadTS63.

Section fact_for_int63.
Variable M : typedStoreMonad.
Notation coq_type := (@MLtypes63.coq_type M).

Definition uint2N (n : int) : nat :=
  if Uint63.to_Z n is Zpos pos then Pos.to_nat pos else 0.

Notation "'do' x <- m ; e" := (m >>= (fun x => e))
  (at level 60, x name, m at level 200, e at level 60).

Definition forloop63 (n_1 n_2 : int) (b : int -> M unit) : M unit :=
  if Sint63.ltb n_2 n_1 then Ret tt else
  iter (uint2N (sub n_2 n_1)).+1
       (fun (m : M int) => do i <- m; do _ <- b i; Ret (Uint63.succ i))
       (Ret n_1) >> Ret tt.

Lemma ltsbNlesb m n : ltsb m n = ~~ lesb n m.
Proof.
case/boolP: (lesb n m) => /Sint63.lebP nm; apply/Sint63.ltbP => /=;
  by [apply Z.le_ngt | apply Z.nle_gt].
Qed.

Lemma ltsbNltsbS m n : ltsb m n -> ~ ltsb n (Uint63.succ m).
Proof.
move/Sint63.ltbP => mn.
move/Sint63.ltbP/Zlt_not_le; elim.
rewrite Sint63.succ_spec Sint63.cmod_small.
  by apply/Zlt_le_succ.
split.
  apply (Z.le_trans _ (Sint63.to_Z m)). by case: (Sint63.to_Z_bounded m).
  by apply Z.le_succ_diag_r.
apply (Z.le_lt_trans _ (Sint63.to_Z n)).
  by apply/Zlt_le_succ.
apply (Z.le_lt_trans _ (Sint63.to_Z Sint63.max_int)).
  by case: (Sint63.to_Z_bounded n).
rewrite Sint63.to_Z_max. by apply Z.lt_sub_pos.
Qed.

Lemma ltsbW m n : ltsb m n -> lesb m n.
Proof. move/Sint63.ltbP/Z.lt_le_incl => mn; by apply/Sint63.lebP. Qed.

Lemma iter_bind T n (f : T -> M T) (m1 : M unit) m2 :
  iter n (fun (m : M T) => m >>= f) (m1 >> m2) =
  m1 >> iter n (fun (m : M T) => m >>= f) m2.
Proof. by elim: n m2 => // n IH m2; rewrite iterS IH !bindA. Qed.

Lemma lesb_ltsb_eq m n : lesb m n -> ltsb n (Uint63.succ m) -> m = n.
Proof.
move/Sint63.lebP => mn /Sint63.ltbP nSm.
move: (nSm).
rewrite Sint63.succ_of_Z -Sint63.is_int; last first.
  split.
    apply Z.le_le_succ_r.
    by case: (Sint63.to_Z_bounded m).
  apply Zlt_le_succ, (Z.le_lt_trans _ _ _ mn), (Z.lt_le_trans _ _ _ nSm).
  by case: (Sint63.to_Z_bounded (Uint63.succ m)).
move/Zlt_le_succ/Zsucc_le_reg => nm.
by apply Sint63.to_Z_inj, Zle_antisym.
Qed.

Lemma uint63_min n : (0 <= Uint63.to_Z n)%Z.
Proof. by case: (Uint63.to_Z_bounded n). Qed.

Lemma uint63_max n : (Uint63.to_Z n < Uint63.wB)%Z.
Proof. by case: (Uint63.to_Z_bounded n). Qed.

Lemma succ_pred m n : sub n (Uint63.succ m) = Uint63.pred (sub n m).
Proof.
apply Uint63.to_Z_inj.
rewrite Uint63.sub_spec Uint63.succ_spec Uint63.pred_spec Uint63.sub_spec.
rewrite Zminus_mod Zmod_mod -Zminus_mod Z.sub_add_distr.
apply/esym.
by rewrite Zminus_mod Zmod_mod -Zminus_mod.
Qed.

Lemma uint2N_pred n : n <> 0%int63 -> uint2N n = (uint2N (Uint63.pred n)).+1.
Proof.
move=> Hn.
rewrite /uint2N Uint63.pred_spec.
case HnZ: (Uint63.to_Z n) => [|m|m].
- rewrite (_ : 0 = Uint63.to_Z 0)%Z // in HnZ.
  move/Uint63.to_Z_inj in HnZ.
  by elim Hn.
- have Hm1 : (0 <= Z.pos m - 1 < Uint63.wB)%Z.
    split. by apply leZsub1, Pos2Z.is_pos.
    apply (Z.lt_trans _ (Z.pos m)).
      by apply leZsub1, Z.le_refl.
    rewrite -HnZ; by apply uint63_max.
  rewrite Zmod_small //.
  case HmZ: (Z.pos m - 1)%Z => [|p|p].
  + by move/Z.sub_move_r: HmZ => /= [] ->.
  + apply Nat2Z.inj => /=.
    rewrite positive_nat_Z Pos2SuccNat.id_succ Pos2Z.inj_succ -HmZ.
    by rewrite (Z.succ_pred (Z.pos m)).
  + by destruct m.
- move: (uint63_min n).
  rewrite HnZ => /Zle_not_lt; elim.
  by apply Zlt_neg_0.
Qed.      

Lemma uint2N_sub_succ m n : ltsb m n ->
  uint2N (sub n m) = (uint2N (sub n (Uint63.succ m))).+1.
Proof.
move=> mn.
rewrite succ_pred uint2N_pred //.
rewrite Sint63.sub_of_Z => /(f_equal Uint63.to_Z).
rewrite Uint63.of_Z_spec.
move/Sint63.ltbP in mn.
rewrite Zmod_small.
  rewrite Z.sub_move_r /= => nm.
  rewrite nm in mn.
  by move/Z.lt_irrefl in mn.
split. by apply Zle_minus_le_0, Z.lt_le_incl.
apply
 (Z.le_lt_trans _ (Sint63.to_Z Sint63.max_int - Sint63.to_Z Sint63.min_int))%Z.
  apply leZ_sub.
    by case: (Sint63.to_Z_bounded n).
  by case: (Sint63.to_Z_bounded m).
done.
Qed.

Lemma forloop63S m n (f : int -> M unit) :
  ltsb m n -> forloop63 m n f = f m >> forloop63 (Uint63.succ m) n f.
Proof.
rewrite /forloop63 => mn.
rewrite ltsbNlesb (ltsbW _ _ mn) /=.
case: ifPn => nSm.
  by elim (ltsbNltsbS _ _ mn).
rewrite ltsbNlesb negbK in nSm.
rewrite uint2N_sub_succ //.
by rewrite iterSr bindretf !bindA iter_bind !bindA.
Qed.

Lemma forloop631 m (f : int -> M unit) :
  forloop63 m m f = f m.
Proof. rewrite /forloop63.
case: (Sint63.ltbP m m) => [/Z.lt_irrefl // | _].
rewrite /= bindA.
rewrite /uint2N Uint63.sub_spec Z.sub_diag Zmod_0_l /=.
by rewrite !(bindretf,bindA) bindmskip.
Qed.

Lemma forloop630 m n (f : int -> M unit) :
  ltsb n m -> forloop63 m n f = skip.
Proof. by rewrite /forloop63 => ->. Qed.

Definition fact_for63 (n : coq_type ml_int) : M (coq_type ml_int) :=
  do v <- cnew ml_int 1%int63;
  do _ <-
  (do u <- Ret 1%int63;
   do v_1 <- Ret n;
   forloop63 u v_1
     (fun i =>
        do v_1 <- (do v_1 <- cget v; Ret (mul v_1 i));
        cput v v_1));
  cget v.

Definition N2int n := Uint63.of_Z (Z.of_nat n).

Lemma N2int_succ : {morph N2int : x / x.+1 >-> Uint63.succ x}.
Proof.
move=> x; apply Uint63.to_Z_inj; rewrite Uint63.succ_spec !Uint63.of_Z_spec.
by rewrite Zplus_mod /= Zpos_P_of_succ_nat /Z.succ Zplus_mod Zmod_mod.
Qed.

Lemma N2int_mul : {morph N2int : x y / x * y >-> mul x y}.
Proof.
move=> x y; apply Uint63.to_Z_inj.
by rewrite Uint63.mul_spec !Uint63.of_Z_spec Nat2Z.inj_mul Zmult_mod.
Qed.

Lemma N2int_bounded n :
  (Z.of_nat n <= Sint63.to_Z Sint63.max_int)%Z ->
  (Sint63.to_Z Sint63.min_int <= Z.of_nat n <= Sint63.to_Z Sint63.max_int)%Z.
Proof.
split => //.
apply (Z.le_trans _ 0).
  rewrite -[0%Z]/(Sint63.to_Z 0).
  by case: (Sint63.to_Z_bounded 0).
by apply Zle_0_nat.
Qed.

Section fact_for63_ok.
Variable n : nat.
Hypothesis Hn : (Z.of_nat n < Sint63.to_Z Sint63.max_int)%Z.

Let n_bounded :
  (Sint63.to_Z Sint63.min_int <= Z.of_nat n <= Sint63.to_Z Sint63.max_int)%Z.
Proof. by apply N2int_bounded, Z.lt_le_incl. Qed.

Lemma ltsb_succ : ltsb (N2int n) (Uint63.succ (N2int n)).
Proof.
apply/Sint63.ltbP.
rewrite Sint63.succ_spec Sint63.cmod_small.
  by apply/Zle_lt_succ/Z.le_refl.
split.
  apply leZ_addr => //; by case: (Sint63.to_Z_bounded (N2int n)).
apply Z.lt_add_lt_sub_r; by rewrite -Sint63.is_int.
Qed.

Lemma ltsb_subr m : m.+1 < n -> ltsb (N2int (n - m.+1)) (N2int n).
Proof.
move=> Smn.
apply/Sint63.ltbP.
have Hm : n - m.+1 < n.
  rewrite ltn_subLR.
    by rewrite addSn ltnS leq_addl.
  by apply ltnW.
rewrite /N2int -!Sint63.is_int //.
- by apply/inj_lt/ltP.
- move/ltP/inj_lt in Hm.
  by split; apply N2int_bounded, Z.lt_le_incl, (Z.lt_trans _ _ _ Hm).
Qed.

Theorem fact_for63_ok :
  crun (fact_for63 (N2int n)) = Some (N2int (fact_rec n)).
Proof.
rewrite /fact_for63.
under eq_bind do rewrite !bindA !bindretf.
set fn := N2int (fact_rec n).
transitivity (crun (cnew ml_int fn >> Ret fn : M _));
  last by rewrite crunret // crunnew0.
congr crun.
have {1}-> : (1 = N2int 1)%int63 by [].
rewrite -/(fact_rec 0).
have -> : (1 = Uint63.succ (N2int 0))%int63 by [].
pose m := n.
have -> : 0 = n - m by rewrite subnn.
have : m <= n by [].
elim: m => [|m IH] mn.
  rewrite subn0.
  under eq_bind do rewrite forloop630 (ltsb_succ,bindretf) // -cgetret.
  by rewrite cnewget.
rewrite -N2int_succ subnSK //.
case: m IH mn => [|m] IH mn.
  under eq_bind do rewrite subn0 forloop631 !(ltsb_subr,bindA) //.
  rewrite cnewget.
  under eq_bind do rewrite bindretf -cgetret.
  rewrite cnewput -N2int_mul mulnC -{1}(prednK mn) cnewget subn1.
  by rewrite -/(fact_rec n.-1.+1) prednK.
under eq_bind do rewrite forloop63S !(ltsb_subr,bindA) //.
rewrite cnewget.
under eq_bind do rewrite bindretf.
rewrite cnewput -IH (ltnW,subnS) // -N2int_mul mulnC -(@prednK (n-m.+1)) //.
by rewrite lt0n subn_eq0 -ltnNge.
Qed.
End fact_for63_ok.
End fact_for_int63.
