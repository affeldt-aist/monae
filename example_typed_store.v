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

Section fact_for_int63.
Variable M : typedStoreMonad.
Notation coq_type := (@MLtypes.coq_type M).

Definition nat_of_uint (n : int) : nat :=
  if Uint63.to_Z n is Zpos pos then Pos.to_nat pos else 0.

Definition forloop63 (n_1 n_2 : int) (b : int -> M unit) : M unit :=
  if Sint63.ltb n_2 n_1 then Ret tt else
  iteri (nat_of_uint (sub n_2 n_1))
       (fun i (m : M unit) => m >> b (add n_1 (Uint63.of_Z (Z.of_nat i))))
       (Ret tt).
End fact_for_int63.
