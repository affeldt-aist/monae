(* monae: Monadic equational reasoning in Rocq                                *)
(* Copyright (C) 2025 monae authors, license: LGPL-2.1-or-later               *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require boolp.
Require Import preamble hierarchy.

(******************************************************************************)
(*                      Lemmas using the typed store monad                    *)
(*                                                                            *)
(*     cchk T (r : loc T) := cget r >> skip.                                  *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.

Section cchk.
Variables (MLU : ML_universe) (N : monad) (locT : eqType)
  (M : typedStoreMonad MLU N locT).
Notation loc := (@loc MLU locT).
Definition cchk {T} : loc T -> M unit := locked (fun r  => cget r >> skip).

Lemma cchkE {T} : @cchk T = fun r => cget r >> skip.
Proof. by rewrite /cchk -lock. Qed.

Lemma cnewchk T s (A : UU0) (k : loc T -> M A) :
  cnew T s >>= (fun r => cchk r >> k r) = cnew T s >>= k.
Proof.
under eq_bind do rewrite cchkE bindA.
rewrite cnewget.
by under eq_bind do rewrite bindskipf.
Qed.

Lemma cchknewC T1 T2 (r : loc T1) s (A : UU0) (k : loc T2 -> M A) :
  cchk r >> (cnew T2 s >>= fun r' => cchk r >> k r') =
  cchk r >> (cnew T2 s >>= k).
Proof.
rewrite cchkE !(bindA,bindskipf).
under eq_bind do under eq_bind do rewrite bindA.
rewrite cgetnewD.
by under eq_bind do under eq_bind do rewrite bindskipf.
Qed.

Lemma cchkgetC T1 T2 (r1: loc T1) (r2: loc T2) (A: UU0)
  (k: coq_type N T2 -> M A) :
  cchk r1 >> (cget r2 >>= k) = cget r2 >>= (fun s => cchk r1 >> k s).
Proof.
under [in RHS]eq_bind do rewrite cchkE bindA bindskipf.
by rewrite cchkE !(bindA,bindskipf) cgetC.
Qed.

Lemma cchknewE T1 T2 (r1 : loc T1) s (A : UU0) (k1 k2 : loc T2 -> M A) :
  (forall r2 : loc T2, loc_id r1 != loc_id r2 -> k1 r2 = k2 r2) ->
  cchk r1 >> (cnew T2 s >>= k1) = cchk r1 >> (cnew T2 s >>= k2).
Proof. move=> Hk; rewrite cchkE !(bindA,bindskipf); exact: cgetnewE. Qed.

Lemma cchknewget T T' (r : loc T) s (A : UU0) k :
  cchk r >> (cnew T' s >>= fun r' => cget r >>= k r') =
  cget r >>= (fun u => cnew T' s >>= k ^~ u) :> M A.
Proof. by rewrite cchkE bindA bindskipf cgetnewD. Qed.

Lemma cchknewput T T' (r : loc T) s s' (A : UU0) k :
  cchk r >> (cnew T' s' >>= fun r' => cput r s >> k r') =
  cput r s >> (cnew T' s' >>= k) :> M A.
Proof. by rewrite cchkE bindA bindskipf cputnewC. Qed.

Lemma cchkget T (r : loc T) (A : UU0) (k : coq_type N T -> M A) :
  cchk r >> (cget r >>= k) = cget r >>= k.
Proof. by rewrite cchkE bindA bindskipf cgetget. Qed.

Lemma cgetchk T (r : loc T) (A: UU0) (k : coq_type N T -> M A) :
  cget r >>= (fun s => cchk r >> k s) = cget r >>= k.
Proof. under eq_bind do rewrite cchkE bindA bindskipf; by rewrite cgetget. Qed.

Lemma cchkputC T1 T2 (r1 : loc T1) (r2 : loc T2) (s : coq_type N T2) :
  cchk r1 >> cput r2 s = cput r2 s >> cchk r1.
Proof. by rewrite cchkE bindA bindskipf cgetputC bindA. Qed.

Lemma cchkput T (r : loc T) (s : coq_type N T) :
  cchk r >> cput r s = cput r s.
Proof. by rewrite cchkE bindA bindskipf cgetput. Qed.

Lemma cputchk T (r : loc T) (s : coq_type N T) :
  cput r s >> cchk r = cput r s.
Proof. by rewrite cchkE cputget bindmskip. Qed.

Lemma cchkC T1 T2 (r1 : loc T1) (r2 : loc T2) :
  cchk r1 >> cchk r2 = cchk r2 >> cchk r1.
Proof. by rewrite !cchkE !(bindA,bindskipf) cgetC. Qed.

Lemma cchkdup T (r : loc T) : cchk r >> cchk r = cchk r.
Proof. by rewrite cchkE bindA bindskipf cgetget. Qed.

Lemma cgetret T (r : loc T) : cget r >>= Ret = cget r :> M _.
Proof. by rewrite bindmret. Qed.

Lemma cnewgetret T s : cnew T s >>= @cget _ _ _ _ _ = cnew T s >> Ret s :> M _.
Proof. under eq_bind do rewrite -cgetret; by rewrite cnewget. Qed.

End cchk.

Section crun.
Variables (MLU : ML_universe) (N : monad) (locT : eqType)
  (M : typedStoreRunMonad MLU N locT).
Notation loc := (@loc MLU locT).

Local Notation cchk := (cchk M).

Lemma crunnew0 T s : crun (cnew T s : M _).
Proof. by rewrite -(bindskipf (cnew T s)) crunnew // crunskip. Qed.

Lemma crunchkget A T (m : M A) (r : A -> loc T) :
  crun (m >>= fun x => cchk (r x)) = crun (m >>= fun x => cget (r x)) :> bool.
Proof. by rewrite cchkE -bindA crunmskip. Qed.

Lemma crunchkput A T (m : M A) (r : A -> loc T) s :
  crun (m >>= fun x => cchk (r x)) ->
  crun (m >>= fun x => cput (r x) (s x)).
Proof. rewrite crunchkget; exact: crungetput. Qed.

Lemma crunnewchkC A T1 T2 (m : M A) (r : A -> loc T1) s :
  crun (m >>= fun x => cchk (r x)) ->
  crun (m >>= fun x => cnew T2 (s x) >> cchk (r x)).
Proof.
rewrite crunchkget cchkE => Hck.
under eq_bind do rewrite -bindA.
rewrite -bindA crunmskip.
exact: crunnewgetC.
Qed.

Lemma crunnewchk A T (m : M A) s :
  crun m -> crun (m >>= fun x => cnew T (s x) >>= cchk).
Proof.
under eq_bind do rewrite cchkE cnewget.
rewrite -bindA crunmskip.
exact: crunnew.
Qed.

Lemma crunnewchk0 T s : crun (cnew T s >>= fun r => cchk r : M _).
Proof. by rewrite -(bindskipf (_ >>= _)) crunnewchk // crunskip. Qed.

End crun.

Arguments cchk {MLU N locT M} [T].
