(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2023 monae authors, license: LGPL-2.1-or-later               *)
Require Import ZArith.
From mathcomp Require Import all_ssreflect.
From mathcomp Require boolp.
From infotheo Require Import ssrZ.
Require Import monad_model.
From HB Require Import structures.
Require Import monae_lib hierarchy monad_lib typed_store_lib.

(******************************************************************************)
(*                         Typed store examples                               *)
(*                                                                            *)
(*  Inductive ml_type == generated by coqgen                                  *)
(*                                                                            *)
(*  Module MLTypesNat                                                         *)
(*    coq_type_nat          == adapted from code generated by coqgen          *)
(*    coq_type_nat0         == coq_type_nat with identity monad               *)
(*    Definition cycle                                                        *)
(*    Fixpoint fact_ref                                                       *)
(*    Definition fact_for                                                     *)
(*    Fixpoint fibo_ref                                                       *)
(*                                                                            *)
(*  Module MLtypes63                                                          *)
(*    Fixpoint coq_type63   == generated type translation function            *)
(*    Definition fact_for63                                                   *)
(******************************************************************************)

Local Open Scope monae_scope.

(******************************************************************************)
(*                             generated by coqgen                            *)
(******************************************************************************)
Module MLTypes.
Inductive ml_type : Set :=
  | ml_int
  | ml_bool
  | ml_unit
  | ml_ref (_ : ml_type)
  | ml_arrow (_ : ml_type) (_ : ml_type)
  | ml_rlist (_ : ml_type).

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

Definition val_nonempty (M : UU0 -> UU0) := tt.

Notation loc := (@loc _ monad_model.locT_nat).

Inductive rlist (a : Type) (a_1 : ml_type) :=
  | Nil
  | Cons (_ : a) (_ : loc (ml_rlist a_1)).

Definition ml_type_eq_mixin := EqMixin (comparePc MLTypes.ml_type_eq_dec).
Canonical ml_type_eqType := Eval hnf in EqType _ ml_type_eq_mixin.

End MLTypes.
(******************************************************************************)

Module CoqTypeNat.
Import MLTypes.

Section with_monad.
Context [M : Type -> Type].

Fixpoint coq_type_nat (T : ml_type) : Type :=
  match T with
  | ml_int => nat
  | ml_bool => bool
  | ml_unit => unit
  | ml_arrow T1 T2 => coq_type_nat T1 -> M (coq_type_nat T2)
  | ml_ref T1 => loc T1
  | ml_rlist T1 => rlist (coq_type_nat T1) T1
  end.
End with_monad.

HB.instance Definition _ := @isML_universe.Build ml_type
  (Equality.class ml_type_eqType) coq_type_nat ml_unit val_nonempty.

Definition typedStoreMonad (N : monad) :=
  typedStoreMonad ml_type N monad_model.locT_nat.

Section cyclic.
Variables (N : monad) (M : typedStoreMonad N).

Local Notation coq_type := hierarchy.coq_type.
Local Open Scope do_notation.

Definition cycle (T : ml_type) (a b : coq_type N T)
  : M (loc (ml_rlist T)) :=
  do r <- cnew (ml_rlist T) (Nil (coq_type N T) T);
  do l <-
  (do v <- cnew (ml_rlist T) (Cons (coq_type N T) T b r);
   Ret (Cons (coq_type N T) T a v));
  do _ <- cput r l; Ret r.

Definition rhd (T : ml_type) (def : coq_type N T)
  (param : loc (ml_rlist T)) : M (coq_type N T) :=
  do v <- cget param; Ret (match v with Nil => def | Cons a _ => a end).

Lemma rhd_is_true :
  crun (do l <- cycle ml_bool true false; rhd ml_bool false l) = Some true.
Proof.
rewrite bindA.
under eq_bind do rewrite !bindA.
under eq_bind do under eq_bind do
 rewrite !bindA bindretf !bindA bindretf cputget.
rewrite -bindA_uncurry -bindA crunret // crunchkput // bindA.
under eq_bind do rewrite !bindA.
under eq_bind do under eq_bind do rewrite bindretf /=.
by rewrite crunnewchkC // crunnewchk0.
Qed.

Definition rtl (T : ml_type) (param : loc (ml_rlist T))
  : M (loc (ml_rlist T)) :=
  do v <- cget param; Ret (match v with Nil => param | Cons _ t => t end).

Arguments cnew {ml_type N locT s T}.
Arguments cput {ml_type N locT s T}.
Arguments cget {ml_type N locT s T}.
Arguments Nil {a a_1}.
Arguments Cons {a a_1}.
Arguments rtl {T}.

Lemma rtl_tl_self T (a b : coq_type N T) :
  do l <- cycle T a b; do l1 <- rtl l; rtl l1 = cycle T a b.
Proof.
rewrite /cycle.
rewrite bindA.
rewrite -[LHS]cnewchk.
under eq_bind => r1.
  rewrite bindA; under eq_bind do rewrite !bindA.
  under cchknewE => r2 r1r2.
    rewrite bindretf bindA bindretf.
    rewrite bindA cputget.
    rewrite bindretf.
    rewrite -bindA.
    rewrite cputgetC //.
    over.
  rewrite cnewget.
  over.
rewrite cnewchk.
(*
under eq_bind do under eq_bind => v do rewrite -(bindretf (Cons true v)) bindA.
under eq_bind do rewrite -bindA.
done.
*)
under [RHS]eq_bind do (rewrite bindA; under eq_bind do rewrite bindretf).
done.
Qed.

Lemma _rtl_tl_self T (a b : coq_type N T) :
  do l <- cycle T a b; do l1 <- rtl l; rtl l1 = cycle T a b.
Proof.
rewrite /cycle bindA -[LHS]cnewchk.
under eq_bind => r1.
  rewrite bindA; under eq_bind do rewrite !bindA.
  under cchknewE do
    rewrite bindretf bindA bindretf bindA cputget bindretf -bindA cputgetC //.
  rewrite cnewget; over.
rewrite cnewchk.
by under [RHS]eq_bind do (rewrite bindA; under eq_bind do rewrite bindretf).
Qed.

Lemma rhd_tl_tl_is_true :
  crun (do l <- cycle ml_bool true false; do l1 <- rtl l; do l2 <- rtl l1;
        rhd ml_bool false l2) = Some true.
Proof.
rewrite -rhd_is_true -[in RHS]rtl_tl_self [in RHS]bindA.
under [in RHS]eq_bind do rewrite bindA.
done.
Qed.

Lemma perm3 T (s1 s2 s3 s4 : coq_type N T) :
  do r1 <- cnew s1; do r2 <- cnew s2; do r3 <- cnew s3; cput r1 s4 =
  do r1 <- cnew s4; do r2 <- cnew s2; do r3 <- cnew s3; skip :> M _.
Proof.
rewrite -cnewchk.
under eq_bind do rewrite -cchknewC -[cput _ _]bindmskip 2!cchknewput.
by rewrite cnewput.
Qed.

Fixpoint mkrlist (T : ml_type) (l : list (coq_type N T))
  (r : loc (ml_rlist T)) : M (loc (ml_rlist T)) :=
  if l is a :: l then
    do v <- mkrlist T l r;
    cnew (T:=ml_rlist T) (Cons a v)
  else Ret r.

Definition cyclel (T : ml_type) (a : coq_type N T) (l : list (coq_type N T))
  : M (loc (ml_rlist T)) :=
  do r <- cnew (T:=ml_rlist T) Nil;
  do v <- mkrlist T l r;
  do _ <- cput r (Cons a v); Ret r.

Fixpoint rdrop {T} n (l : loc (ml_rlist T)) : M (loc (ml_rlist T)) :=
  if n is n.+1 then rtl l >>= rdrop n else Ret l.
Definition rnth T x n l := do l' <- rdrop n l; rhd T x l'.

Lemma rdrop_add T m n (l : loc (ml_rlist T)) :
  rdrop (m+n) l = rdrop m l >>= rdrop n.
Proof.
elim: m l => /= [|m IH] l; first by rewrite bindretf.
by rewrite bindA; apply eq_bind => l'.
Qed.

Lemma mkrlist_cat T l1 l2 r :
  mkrlist T (l1++l2) r = mkrlist T l2 r >>= mkrlist T l1.
Proof.
elim: l1 => [|a l1 IH]; by [rewrite cat0s bindmret | rewrite /= IH bindA].
Qed.

Lemma cchkmkrlistC A T T1 l (r : loc T) r1 k :
  cchk r >> (mkrlist T1 l r1 >>= (fun r' => cchk r >> k r'))
  = cchk r >> (mkrlist T1 l r1 >>= k) :> M A.
Proof.
elim: l k => [|a l IH] k /=.
  by rewrite !bindretf -bindA cchkget.
symmetry.
rewrite bindA -IH.
under eq_bind do under eq_bind do rewrite -cchknewC.
by rewrite IH bindA.
Qed.

Lemma cgetmkrlistC A T T1 (r : loc T) r1 l k :
  cchk r >> (mkrlist T1 l r1 >>= (fun r' => cget r >>= k r'))
  = cget r >>= (fun v => mkrlist T1 l r1 >>= k ^~ v) :> M A.
Proof.
elim: l k => [|a l IH] k /=.
  under [in RHS]eq_bind do rewrite bindretf.
  by rewrite !bindretf cchkget.
symmetry.
under eq_bind do rewrite bindA.
rewrite -IH.
under [mkrlist _ _ _ >>= _]eq_bind do rewrite -cchknewget.
by rewrite cchkmkrlistC bindA.
Qed.

Lemma mkrlist_drop A T l r k :
  (mkrlist T l r >>= fun r' => rdrop (size l) r' >>= k r') =
  (mkrlist T l r >>= k ^~ r) :> M A.
Proof.
elim/last_ind: l r k => [|a l IH] r k.
  by rewrite !bindretf.
rewrite -cats1 mkrlist_cat size_cat bindA /= bindretf.
under eq_bind do under eq_bind do rewrite rdrop_add -bindA bindmret bindA.
rewrite -cnewchk.
under eq_bind => r1.
  rewrite IH.
  under [mkrlist _ _ _ >>= _]eq_bind do rewrite bindA.
  rewrite cgetmkrlistC.
  over.
rewrite cnewget /= -[cnew _ >>= _]bindA.
by under eq_bind do rewrite bindretf.
Qed.

Lemma cchk_mkrlist_put_drop A T l (r r1 : loc (ml_rlist T)) f k :
  cchk r >> (mkrlist T l r1 >>= fun r' => cput r (f r') >>
                                 (rdrop (size l) r' >>= k r')) =
  cchk r >> (mkrlist T l r1 >>= fun r' => rdrop (size l) r' >>=
                                 (fun r'' => cput r (f r') >> k r' r'')) :> M A.
Proof.
elim/last_ind: l r1 k => [|a l IH] r1 k.
  by rewrite !bindretf.
rewrite -cats1 mkrlist_cat size_cat /=.
under eq_bind do rewrite bindretf bindA.
rewrite -cchknewC.
under cchknewE => r2 rr2.
  under [mkrlist _ _ _ >>= _]eq_bind do rewrite rdrop_add bindA.
  rewrite IH mkrlist_drop /=.
  under [mkrlist _ _ _ >>= _]eq_bind do
    rewrite !bindA -[cput _ _ >> _]bindA cputgetC //.
  under eq_bind do under eq_bind do under eq_bind do rewrite !bindretf.
  over.
rewrite cchknewC.
symmetry.
under eq_bind do rewrite bindretf bindA.
under [LHS]cchknewE => r2 rr2.
  under eq_bind do rewrite rdrop_add bindA.
  rewrite mkrlist_drop /=.
  under eq_bind do rewrite /rtl bindmret /= bindA.
  under eq_bind do under eq_bind do rewrite bindretf.
  over.
done.
Qed.

Lemma cyclel_rdrop_self T a l :
  cyclel T a l >>= rdrop (size l).+1 = cyclel T a l.
Proof.
rewrite /cyclel -cnewchk bindA.
apply eq_bind => r.
rewrite bindA.
under eq_bind do rewrite -(bindA (mkrlist _ _ _)).
rewrite (bindA _ _ (rdrop _)) bindretf bindA /=.
under eq_bind do under eq_bind do
  rewrite /rtl -bindA cputget bindA bindretf -[rdrop _ _]bindmret.
by rewrite cchk_mkrlist_put_drop mkrlist_drop.
Qed.

Lemma rnth_is_true n :
  crun (do l <- cyclel ml_bool true (nseq n false); rnth ml_bool false n.+1 l)
  = Some true.
Proof.
rewrite /rnth -bindA -[in n.+1](size_nseq n false) cyclel_rdrop_self.
rewrite /rhd !bindA.
under eq_bind=> r.
  rewrite !bindA.
  under eq_bind do rewrite bindA bindretf cputget.
  rewrite -bindA.
  over.
rewrite -bindA crunret // -bindA_uncurry crunchkput // bindA -cnewchk.
under eq_bind => r.
  rewrite bindA.
  under eq_bind do under eq_bind do rewrite bindretf /= -[cchk _]bindmskip.
  rewrite cchkmkrlistC.
  over.
rewrite cnewchk -bindA crunmskip.
elim: n => /= [|n IH]. by rewrite bindmret crunnew0.
by rewrite -bindA crunnew.
Qed.

Fixpoint iappend (h : nat) (l1 l2 : coq_type N (ml_rlist ml_int))
  : M (coq_type N (ml_rlist ml_int)) :=
  if h is h.+1 then
    match l1 with
    | Nil => Ret l2
    | Cons a l1' =>
      do _ <-
      (do v <- (do v <- cget l1'; iappend h v l2);
       cput l1' v);
      Ret l1
    end
  else Ret (@Nil nat ml_int).

Fixpoint is_int_list (l : list nat) (rl : rlist nat ml_int) : M bool :=
  match l, rl with
  | [::], Nil => Ret true
  | (a :: t), (Cons b r) =>
      if a != b then Ret false else
      do rl' <- cget r; is_int_list t rl'
  | _, _ => Ret false
  end.

Fixpoint loc_ids_rlist (l : list nat) (rl : rlist nat ml_int)
  : M (list nat) :=
  match l with
  | [::] => Ret [::]
  | (_ :: t) =>
      match rl with
      | Nil => Ret [::]
      | Cons _ r =>
          do rl' <- cget r; do rs <- loc_ids_rlist t rl'; Ret (loc_id r :: rs)
      end
  end.

Lemma iappend_correct m l1 l2 :
  crun (do p : rlist nat ml_int * rlist nat ml_int <- m; let (rl1, rl2) := p in
        do a <- is_int_list l1 rl1; do b <- is_int_list l2 rl2;
        do rs1 <- loc_ids_rlist l1 rl1; do rs2 <- loc_ids_rlist l2 rl2;
        Ret (a && b && (allrel (fun r1 r2 => r1 != r2) rs1 rs2)))
       = Some true->
  crun (do p : rlist nat ml_int * rlist nat ml_int <- m; let (rl1, rl2) := p in
        do rl <- iappend (size l1).+1 rl1 rl2; is_int_list (l1 ++ l2) rl)
       = Some true.
Proof.
(* need more abstractions *)
Abort.
End cyclic.

Module eval_cyclic.
Section eval.
Import monad_model.ModelTypedStore.
                
Definition M :=
  [the typedStoreMonad idfun of @acto ml_type idfun].

Definition Env := Env ml_type idfun.

Definition empty_env : Env := [::].

(* copied from typed_store_model.v *)
Definition W (A : UU0) : UU0 := monad_model.option_monad (A * Env).

Definition Restart [A B] (r : W A) (f : M B) : W B :=
  if r is inr (_, env) then f env else inl tt.

Definition FromW [A] (r : W A) : M A :=
  fun env => if r is inr (a, _) then inr (a, env) else inl tt.

Definition it0 : W unit := inr (tt, empty_env).

Local Open Scope do_notation.
Local Notation mkloc := (mkloc (locT:=monad_model.locT_nat)).
Local Notation coq_type := (coq_type _).

Definition incr (l : loc ml_int) : M nat :=
  do x <- cget l; do _ <- cput l (succn x); Ret (succn x).

Definition l : W (loc ml_int) := Restart it0 (cnew ml_int 3).
Eval vm_compute in l.

Definition it1 := Restart l (do l <- FromW l; incr l).
Eval vm_compute in it1.

Definition it2 := Restart it1 (do l <- FromW l; incr l).
Eval vm_compute in it2.

Local Notation cycle := (cycle idfun M).
Local Notation rhd := (rhd idfun M).
Local Notation rtl := (rtl idfun M).

Definition it3 := Restart it2 (cycle ml_bool true false).
Eval vm_compute in crun (FromW it3).

Definition it4 := Restart it3 (do l <- FromW it3; Ret (rhd ml_bool false l)).

Definition it5 := Restart it4
                    (do l0 <- FromW it3;
                     do l1 <- rtl _ l0;
                     do l2 <- rtl _ l1;
                     Ret (rhd ml_bool false l2)).

End eval.
End eval_cyclic.

Section factorial.
Variable (N : monad) (M : typedStoreMonad N).

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

Section fact_for.
Variable (N : monad) (M : typedStoreMonad N).
Local Notation coq_type := (hierarchy.coq_type N).
Local Open Scope do_notation.

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
Variables (N : monad) (M : typedStoreMonad N).

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
have : (x, y) = (fibo_rec (n - i), fibo_rec (n.+1 - i)).
  by rewrite subnn -addn1 addKn.
have : i <= n by [].
elim: i x y => [|i IH] x y Hi.
  rewrite !subn0 => -[-> ->].
  rewrite -/(fibo_rec n.+1).
  under eq_bind do under eq_bind do rewrite /= bindskipf.
  rewrite -cnewchk.
  under eq_bind do rewrite -cgetret cchknewget.
  by rewrite cnewget -bindA crunret // crunnew // crunnew0.
rewrite subSS => -[] Hx Hy.
rewrite -(IH y (x + y) (ltnW Hi)); last first.
  rewrite {}Hx {}Hy; congr pair.
  rewrite subSn 1?ltnW//.
  case: n {IH} => // n in Hi *.
  by rewrite [in RHS]subSn -1?ltnS// subSS subSn -1?ltnS.
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

End CoqTypeNat.

Require Import PrimInt63.
Require Sint63.

Section Int63.
Definition uint2N (n : int) : nat :=
  if Uint63.to_Z n is Zpos pos then Pos.to_nat pos else 0.
Definition N2int n := Uint63.of_Z (Z.of_nat n).

Lemma ltsbNlesb m n : ltsb m n = ~~ lesb n m.
Proof.
case/boolP: (lesb n m) => /Sint63.lebP nm; apply/Sint63.ltbP => /=;
  by [apply Z.le_ngt | apply Z.nle_gt].
Qed.

Lemma ltsbW m n : ltsb m n -> lesb m n.
Proof. move/Sint63.ltbP/Z.lt_le_incl => mn; by apply/Sint63.lebP. Qed.

Lemma lesb_ltsbS_eq m n : lesb m n -> ltsb n (Uint63.succ m) -> m = n.
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

(* The opposite is not true ! (n = max_int) *)
Lemma ltsbS_lesb m n : ltsb m (Uint63.succ n) -> lesb m n.
Proof.
rewrite -[lesb _ _]negbK -ltsbNlesb => nSm; apply/negP => /[dup] /ltsbW nm.
by rewrite (lesb_ltsbS_eq n m) // => /Sint63.ltbP /Z.lt_irrefl.
Qed.

Lemma uint63_min n : (0 <= Uint63.to_Z n)%Z.
Proof. by case: (Uint63.to_Z_bounded n). Qed.

Lemma uint63_max n : (Uint63.to_Z n < Uint63.wB)%Z.
Proof. by case: (Uint63.to_Z_bounded n). Qed.

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

Lemma lesb_sub_bounded m n :
  lesb m n -> (0 <= Sint63.to_Z n - Sint63.to_Z m < Uint63.wB)%Z.
Proof.
move/Sint63.lebP => mn.
split. by apply Zle_minus_le_0.
apply
 (Z.le_lt_trans _ (Sint63.to_Z Sint63.max_int - Sint63.to_Z Sint63.min_int))%Z.
  apply leZ_sub.
    by case: (Sint63.to_Z_bounded n).
  by case: (Sint63.to_Z_bounded m).
done.
Qed.

Lemma ltsb_neq m n : ltsb m n -> m <> n.
Proof. by move/Sint63.ltbP/[swap]/(f_equal Sint63.to_Z)-> =>/Z.lt_irrefl. Qed.

(*
Lemma sub0_eq m n : sub m n = 0%int63 -> m = n.
Proof.
rewrite Sint63.sub_of_Z => /(f_equal Uint63.to_Z).
rewrite Uint63.of_Z_spec.
move/Sint63.ltbP in mn.
rewrite Zmod_small.
  rewrite Z.sub_move_r /= => nm.
  rewrite nm in mn.
  by move/Z.lt_irrefl in mn.
by apply /lesb_sub_bounded /Sint63.lebP /Z.lt_le_incl.
Qed.
*)

Lemma ltsb_sub_neq0 m n : ltsb m n -> sub n m <> 0%int63.
Proof.
move=> mn.
rewrite Sint63.sub_of_Z => /(f_equal Uint63.to_Z).
rewrite Uint63.of_Z_spec.
move/Sint63.ltbP in mn.
rewrite Zmod_small.
  rewrite Z.sub_move_r /= => nm.
  rewrite nm in mn.
  by move/Z.lt_irrefl in mn.
by apply /lesb_sub_bounded /Sint63.lebP /Z.lt_le_incl.
Qed.

Lemma sub_succ_pred m n : sub n (Uint63.succ m) = Uint63.pred (sub n m).
Proof.
apply Uint63.to_Z_inj.
rewrite Uint63.sub_spec Uint63.succ_spec Uint63.pred_spec Uint63.sub_spec.
rewrite Zminus_mod Zmod_mod -Zminus_mod Z.sub_add_distr.
apply/esym.
by rewrite Zminus_mod Zmod_mod -Zminus_mod.
Qed.

Lemma uint2N_sub_succ m n : ltsb m n ->
  uint2N (sub n m) = (uint2N (sub n (Uint63.succ m))).+1.
Proof. move/ltsb_sub_neq0 => mn. by rewrite sub_succ_pred uint2N_pred. Qed.

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
End Int63.

Module CoqTypeInt63.
Import MLTypes.

(******************************************************************************)
(*                             generated by coqgen                            *)
(******************************************************************************)
Section with_monad.
Context [M : Type -> Type].
Fixpoint coq_type63 (T : ml_type) : Type :=
  match T with
  | ml_int => int
  | ml_bool => bool
  | ml_unit => unit
  | ml_arrow T1 T2 => coq_type63 T1 -> M (coq_type63 T2)
  | ml_ref T1 => loc T1
  | ml_rlist T1 => rlist (coq_type63 T1) T1
  end.
End with_monad.
(******************************************************************************)

HB.instance Definition _ := @isML_universe.Build ml_type
  (Equality.class ml_type_eqType) coq_type63 ml_unit val_nonempty.

Section fact_for_int63.
Variable N : monad.
Variable M : typedStoreMonad ml_type N monad_model.locT_nat.
Local Notation coq_type := (hierarchy.coq_type N).
Local Open Scope do_notation.

Section forloop63.
Definition forloop63 (n_1 n_2 : int) (b : int -> M unit) : M unit :=
  if Sint63.ltb n_2 n_1 then Ret tt else
  iter (uint2N (sub n_2 n_1)).+1
       (fun (m : M int) => do i <- m; do _ <- b i; Ret (Uint63.succ i))
       (Ret n_1) >> Ret tt.

Lemma forloop63S m n (f : int -> M unit) :
  ltsb m n -> forloop63 m n f = f m >> forloop63 (Uint63.succ m) n f.
Proof.
rewrite /forloop63 => mn.
rewrite ltsbNlesb (ltsbW _ _ mn) /=.
case: ifPn => nSm.
  by move: mn; rewrite ltsbNlesb => /negP; elim; apply ltsbS_lesb.
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
End forloop63.

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

Section fact_for63_ok.
Variable n : nat.
(* Note: assuming n < max_int rather than n <= max_int is not strictly
   needed, but it simplifies reasoning about loops in concrete code *)
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

Theorem fact_for63_ok : crun (fact_for63 (N2int n)) = Some (N2int (fact_rec n)).
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

Section eval.
Require Import typed_store_model.

Definition M := [the typedStoreMonad ml_type _ monad_model.locT_nat of
                 acto ml_type].

Definition Env := typed_store_model.Env ml_type.

Definition empty_env := @typed_store_model.mkEnv ml_type nil.

Definition it0 : W unit := inr (tt, empty_env).

Local Open Scope do_notation.
Local Notation mkloc := (mkloc (locT:=monad_model.locT_nat)).
Local Notation coq_type := (coq_type M).

Definition incr (l : loc ml_int) : M int :=
  do x <- cget l; do _ <- cput l (Uint63.succ x); Ret (Uint63.succ x).

Definition l : W (loc ml_int) := Restart it0 (cnew ml_int 3)%int63.
Eval vm_compute in l.

Definition it1 := Restart l (do l <- FromW l; incr l).
Eval vm_compute in it1.

Definition it2 := Restart it1 (do l <- FromW l; incr l).
Eval vm_compute in it2.

Definition it3 := Restart it2 (fact_for63 M M 5)%uint63.
Eval vm_compute in it3.

Definition AppM {A B} (f : M (A -> M B)) (x : A) := do f <- f; f x.

Definition omega (T : ml_type) (n : coq_type T) : M (coq_type T) :=
  do r_1 <- cnew (ml_arrow T T) (fun x : coq_type T => Ret (x : coq_type T));
  let delta (i : coq_type T) : M (coq_type T) :=
    AppM (cget r_1) i in
  do _ <- cput r_1 delta; delta n.

Definition it_omega := Restart it3 (omega ml_unit tt).
Fail Timeout 1 Eval vm_compute in it_omega.

End eval.

End CoqTypeInt63.
