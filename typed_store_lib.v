(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2023 monae authors, license: LGPL-2.1-or-later               *)
Ltac typeof X := type of X.

Require Import ssrmatching Reals JMeq.
From mathcomp Require Import all_ssreflect.
From mathcomp Require boolp.
From infotheo Require Import Reals_ext.
Require Import monae_lib hierarchy.

(******************************************************************************)
(*                      Lemmas using the typed store monad                    *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.

Section cchk.
Variables (MLU : ML_universe) (locT : eqType) (M : typedStoreMonad MLU locT).
Notation loc := (@loc MLU locT).
Definition cchk T (r : loc T) : M unit := cget r >> skip.

Lemma cnewchk T s (A : UU0) (k : loc T -> M A) :
  cnew T s >>= (fun r => cchk r >> k r) = cnew T s >>= k.
Proof.
under eq_bind do rewrite bindA.
rewrite cnewget.
by under eq_bind do rewrite bindskipf.
Qed.

Lemma cchknewC T1 T2 (r : loc T1) s (A : UU0) (k : loc T2 -> M A) :
  cchk r >> (cnew T2 s >>= fun r' => cchk r >> k r') =
  cchk r >> (cnew T2 s >>= k).
Proof.
rewrite !(bindA,bindskipf).
under eq_bind do under eq_bind do rewrite bindA.
rewrite cgetnewD.
by under eq_bind do under eq_bind do rewrite bindskipf.
Qed.

Lemma cchkgetC T1 T2 (r1: loc T1) (r2: loc T2) (A: UU0)
  (k: coq_type M T2 -> M A) :
  cchk r1 >> (cget r2 >>= k) = cget r2 >>= (fun s => cchk r1 >> k s).
Proof.
under [in RHS]eq_bind do rewrite bindA bindskipf.
by rewrite !(bindA,bindskipf) cgetC.
Qed.

Lemma cchknewE T1 T2 (r1 : loc T1) s (A : UU0) (k1 k2 : loc T2 -> M A) :
  (forall r2 : loc T2, loc_id r1 != loc_id r2 -> k1 r2 = k2 r2) ->
  cchk r1 >> (cnew T2 s >>= k1) = cchk r1 >> (cnew T2 s >>= k2).
Proof. move=> Hk; rewrite !(bindA,bindskipf); exact: cgetnewE. Qed.

Lemma cchknewget T T' (r : loc T) s (A : UU0) k :
  cchk r >> (cnew T' s >>= fun r' => cget r >>= k r') =
  cget r >>= (fun u => cnew T' s >>= k ^~ u) :> M A.
Proof. by rewrite bindA bindskipf cgetnewD. Qed.

Lemma cchknewput T T' (r : loc T) s s' (A : UU0) k :
  cchk r >> (cnew T' s' >>= fun r' => cput r s >> k r') =
  cput r s >> (cnew T' s' >>= k) :> M A.
Proof. by rewrite bindA bindskipf cputnewC. Qed.

Lemma cchkget T (r : loc T) (A: UU0) (k : coq_type M T -> M A) :
  cchk r >> (cget r >>= k) = cget r >>= k.
Proof. by rewrite bindA bindskipf cgetget. Qed.

Lemma cgetchk T (r : loc T) (A: UU0) (k : coq_type M T -> M A) :
  cget r >>= (fun s => cchk r >> k s) = cget r >>= k.
Proof. under eq_bind do rewrite bindA bindskipf; by rewrite cgetget. Qed.

Lemma cchkputC T1 T2 (r1 : loc T1) (r2 : loc T2) (s : coq_type M T2) :
  cchk r1 >> cput r2 s = cput r2 s >> cchk r1.
Proof. by rewrite bindA bindskipf cgetputC bindA. Qed.

Lemma cchkput T (r : loc T) (s : coq_type M T) :
  cchk r >> cput r s = cput r s.
Proof. by rewrite bindA bindskipf cgetput. Qed.

Lemma cputchk T (r : loc T) (s : coq_type M T) :
  cput r s >> cchk r = cput r s.
Proof. by rewrite cputget bindmskip. Qed.

Lemma cchkC T1 T2 (r1: loc T1) (r2: loc T2) :
  cchk r1 >> cchk r2 = cchk r2 >> cchk r1.
Proof. by rewrite !(bindA,bindskipf) cgetC. Qed.

Lemma cchkdup T (r : loc T) : cchk r >> cchk r = cchk r.
Proof. by rewrite bindA bindskipf cgetget. Qed.

Lemma cgetret T (r : loc T) : cget r >>= Ret = cget r :> M _.
Proof. by rewrite bindmret. Qed.

Lemma crunnew0 T s : crun (cnew T s : M _).
Proof. by rewrite -(bindskipf (cnew T s)) crunnew // crunskip. Qed.

Lemma cnewgetret T s : cnew T s >>= @cget _ _ _ _ = cnew T s >> Ret s :> M _.
Proof. under eq_bind do rewrite -cgetret; by rewrite cnewget. Qed.
End cchk.
Arguments cchk {MLU locT M} [T].
