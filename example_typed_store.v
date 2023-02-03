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
Variant loc : ml_type -> Type := mkloc T : nat -> loc T.

Section with_monad.
Context [M : Type -> Type].

Local (* Generated type translation function *)
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

Arguments cget {s} [T].
Arguments cput {s} [T].
Arguments cchk {s} [T].
Arguments crun {s} [A].

Lemma cgetret (M : typedStoreMonad) T :
  @cget _ T = fun r => (cget r : M _) >>= Ret.
Proof. by apply boolp.funext => r; rewrite bindmret. Qed.

Lemma crunnew0 (M : typedStoreMonad) T s : crun (cnew T s : M _).
Proof. by rewrite -[cnew _ _]bindskipf crunnew // crunskip. Qed.

Lemma funext {T U : UU0} [f g : T -> U] : f =1 g -> (fun x => f x) = g.
Proof. exact: boolp.funext. Qed.

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
  under funext do rewrite bindskipf.
  by rewrite cgetret cnewget crunret // crunnew0.
under funext do rewrite bindA.
rewrite cnewget.
under funext do rewrite bindA.
by rewrite cnewput IH // (mulnC m.+1) -mulnA.
Qed.
End factorial.

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
  under funext do under funext do rewrite /= bindskipf.
  under funext do rewrite cgetret.
  rewrite -cnewchk.
  under funext do rewrite cnewgetC.
  by rewrite cnewget -bindA crunret // crunnew // crunnew0.
rewrite subSS => -[] Hx Hy.
rewrite -(IH y (x + y) (ltnW Hi)); last first.
  subst x y.
  congr pair.
  case: n Hi {IH} => // n.
  rewrite subSS ltnS => Hi.
  by rewrite -addn2 -addn1 -addnBAC // -addnBAC // addn2 addn1.
rewrite /=.
under funext do under funext do rewrite !bindA.
rewrite -cnewchk.
under funext do rewrite cnewgetC.
rewrite cnewget.
under funext do under funext do rewrite !bindA.
under funext do rewrite cnewget.
under funext do under funext do rewrite !bindA.
rewrite -cnewchk.
under funext do rewrite cnewputC.
rewrite cnewput.
by under funext do rewrite cnewput.
Qed.
End fibonacci.
