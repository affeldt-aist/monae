(* monae: Monadic equational reasoning in Rocq                                *)
(* Copyright (C) 2025 monae authors, license: LGPL-2.1-or-later               *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require boolp.
Require Import preamble hierarchy monad_lib alt_lib fail_lib state_lib.
Require Import array_lib example_quicksort.
From infotheo Require Import ssr_ext.

(**md**************************************************************************)
(* # Quicksort with the Array Monad                                           *)
(*                                                                            *)
(* ```                                                                        *)
(*    partl p (s, t) u == partition u into (x, y) w.r.t. pivot p and returns  *)
(*                        (s ++ x, t ++ y)                                    *)
(*            dispatch == if x <= p then qperm zs >>= f (rcons ys x)          *)
(*                        else qperm (rcons zs x) >>= f ys                    *)
(* qperm_partl p s t u == fusion of qperm and partl; this is a computation    *)
(*                        of type M (seq E * seq E * seq E) where E is the    *)
(*                        type of the values in the array monad               *)
(* ipartl p i ny nz nx == partition the array stored at i w.r.t. the pivot p, *)
(*                        the array is yz ++ zs ++ xs where the lengths of    *)
(*                        yz, zs, xs are resp. ny, nz, nx; it returns the     *)
(*                        lengths of the partitions this is a computation of  *)
(*                        of type M (nat * nat)                               *)
(*   dipartl p i y z x == same as ipartl except that it returns a dependent   *)
(*                        pair of type                                        *)
(*                        {(a, b)| a <= x + y + z && b <= x + y +z}           *)
(*       iqsort (i, n) == quicksort the list of size n stored from address i  *)
(* ```                                                                        *)
(*                                                                            *)
(* Reference:                                                                 *)
(* - [1] Shin-Cheng Mu, Tsung-Ju Chiang, Declarative Pearl: Deriving Monadic  *)
(*       Quicksort, FLOPS 2020                                                *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope order_scope.
Import Order.Theory.
Local Open Scope monae_scope.
Local Open Scope tuple_ext_scope.

Section partl.
Context d (E : orderType d) (M : plusArrayMonad E nat).
Implicit Types p : E.

(* tail-recursive *)
Fixpoint partl p (s : (seq E * seq E)%type) (xs : seq E)
    : (seq E * seq E)%type :=
  if xs is x :: xs then
    (if x <= p then partl p (rcons s.1 x, s.2) xs
              else partl p (s.1, rcons s.2 x) xs)
  else s.

Let partlE s t p u : let x := partition p u in
  partl p (s, t) u = (s ++ x.1, t ++ x.2).
Proof.
elim: u p s t => [|h tl ih] /= p a b; first by rewrite !cats0.
by case: ifPn => hp; rewrite ih /= -cats1 /= -catA.
Qed.

Lemma partition_partl p xs : partition p xs = partl p ([::], [::]) xs.
Proof. by rewrite partlE /=; case: partition. Qed.

End partl.

Section dispatch.
Context d (E : orderType d) (M : plusArrayMonad E nat).
Implicit Types i : nat.

Definition dispatch (x p : E) '(ys, zs) A (f : seq E -> seq E -> M A) : M A :=
  if x <= p then qperm zs >>= f (rcons ys x)
            else qperm (rcons zs x) >>= f ys.

Definition dispatch_Ret (x p : E) '(ys, zs, xs) : M (seq E * seq E * seq E)%type :=
  dispatch x p (ys, zs) (fun ys' zs' => Ret (ys', zs', xs)).

Lemma dispatch_Ret_isNondet x p yszsxs : plus_isNondet (dispatch_Ret x p yszsxs).
Proof.
rewrite /dispatch/=; move: yszsxs => [[ys zs] xs]/=; case: ifPn => xp.
  have [syn syn_qperm] := @qperm_isNondet M _ zs.
  exists (ndBind syn (fun s => ndRet (rcons ys x, s, xs))).
  by rewrite /= syn_qperm.
have [syn syn_qperm] := @qperm_isNondet M _ (rcons zs x).
by exists (ndBind syn (fun s => ndRet (ys, s, xs))); rewrite /= syn_qperm.
Qed.

End dispatch.
Arguments dispatch_Ret {d E M}.

#[global] Hint Extern 0 (plus_isNondet (dispatch_Ret _ _ _)) =>
  solve[exact: dispatch_Ret_isNondet] : core.

Section qperm_partl.
Context d (E : orderType d) (M : plusArrayMonad E nat).
Implicit Types p : E.

Fixpoint qperm_partl p (ys zs xs : seq E) : M (seq E * seq E)%type :=
  if xs is x :: xs then
    dispatch x p (ys, zs) (fun ys' zs' => qperm_partl p ys' zs' xs)
  else Ret (ys, zs).

Lemma qperm_partl_isNondet p (s a b : seq E) :
  plus_isNondet (qperm_partl p a b s).
Proof.
elim: s p a b => [p a b|h t ih p a b /=]; first by exists (ndRet (a, b)).
case: ifPn => hp.
  have [syn synE] := @qperm_isNondet M _ b.
  exists (ndBind syn (fun zs' => sval (ih p (rcons a h) zs'))) => /=.
  by rewrite synE /=; bind_ext =>  ? /=; case: ih.
have [syn synE] := @qperm_isNondet M _ (rcons b h).
exists (ndBind syn (fun zs' => sval (ih p a zs'))) => /=.
by rewrite synE /=; bind_ext => ? /=; case: ih.
Qed.

Lemma qperm_partl_cons (p x : E) (ys zs xs : seq E) :
  qperm_partl p ys zs (x :: xs) =
  dispatch_Ret x p (ys, zs, xs) >>= uncurry3 (qperm_partl p).
Proof.
by rewrite /=; case: ifPn => xp; rewrite bindA;
  under [RHS]eq_bind do rewrite bindretf.
Qed.

End qperm_partl.
Arguments qperm_partl {d E M}.

#[global] Hint Extern 0 (plus_isNondet (qperm_partl _ _ _ _)) =>
  solve[exact: qperm_partl_isNondet] : core.

Section ipartl.
Context d (T : orderType d).

Section arrayMonad.
Variable M : arrayMonad T nat.

Fixpoint ipartl p i ny nz nx : M (nat * nat)%type :=
  if nx is k.+1 then
    aget (i + (ny + nz)) >>= (fun x =>
      if x <= p then
        aswap (i + ny) (i + ny + nz) >> ipartl p i ny.+1 nz k
      else
        ipartl p i ny nz.+1 k)
  else Ret (ny, nz).

End arrayMonad.
Arguments ipartl {M}.

Section plusArrayMonad.
Variable M : plusArrayMonad T nat.

Lemma ipartl_guard p i ny nz nx :
  ipartl (M := M) p i ny nz nx =
  ipartl p i ny nz nx >>= (fun '(a, b) =>
    (guard ((a <= nx + ny + nz) && (b <= nx + ny + nz))%N >> Ret (a, b))).
Proof.
elim: nx ny nz => [ny nz|n ih ny nz].
  by rewrite /= bindretf add0n leq_addr leq_addl guardT bindskipf.
rewrite /= [in RHS]bindA; bind_ext => x; case: ifPn => xp.
- rewrite [in RHS]bindA; bind_ext => -[]; rewrite [in LHS]ih.
  by under eq_bind do rewrite -addSnnS.
- rewrite [in LHS]ih.
  by under [in RHS]eq_bind do rewrite addSnnS -addnA addSnnS addnA.
Qed.

End plusArrayMonad.
End ipartl.
Arguments ipartl {d T M}.

Section dipartl.
Context d (T : orderType d) (M : plusArrayMonad T nat).

Definition dipartlT y z x :=
  {n : nat * nat | (n.1 <= x + y + z) && (n.2 <= x + y + z)}.

Definition dipartlT1 y z x (a : dipartlT y z x) : nat := (sval a).1.
Definition dipartlT2 y z x (a : dipartlT y z x) : nat := (sval a).2.

Definition dipartl p i y z x : M (dipartlT y z x) :=
  ipartl p i y z x >>=
    dassert [pred n | (n.1 <= x + y + z) && (n.2 <= x + y + z)].

Local Open Scope mprog.
Lemma ipartlE p i y z x : ipartl p i y z x = (M # sval) (dipartl p i y z x).
Proof.
rewrite fmapE /dipartl bindA ipartl_guard bindA; bind_ext => -[a b].
rewrite bindA; apply: bind_ext_guard => /andP[na nb].
rewrite bindretf /dassert /=.
case: Bool.bool_dec => [nanb|/negP]; first by rewrite bindretf.
by rewrite negb_and => /orP[|] /negP.
Qed.
Local Close Scope mprog.

Section refin_dispatch_write3L_ipartl.
Variables (i : nat) (p : T) (xs : seq T).
Hypothesis ih : forall ys zs,
  writeList i (ys ++ zs ++ xs) >> ipartl (M := M) p i (size ys) (size zs) (size xs)
  `<=` qperm_partl p ys zs xs >>= write2L i.

Let refin_write3L_ipartl x :
  write3L i (x, xs) >>= uncurry3 (ipartl (M := M) p i)
  `<=` uncurry3 (qperm_partl p) (x, xs) >>= write2L i.
Proof.
case: x => ys zs.
by apply: refin_trans (ih _ _); rewrite bindA bindretf; exact: refin_refl.
Qed.

Lemma refin_dispatch_Ret_write3L_ipartl x ys zs :
  dispatch_Ret x p (ys, zs, xs) >>= write3L i >>= uncurry3 (ipartl (M := M) p i)
  `<=` dispatch_Ret x p (ys, zs, xs) >>= uncurry3 (qperm_partl p) >>= write2L i.
Proof.
by rewrite /= !if_bind; apply: refin_if => _; rewrite !bindA;
  apply/refin_bindl => zs'; rewrite !bindretf; exact: refin_write3L_ipartl.
Qed.
End refin_dispatch_write3L_ipartl.

End dipartl.
Arguments dipartl {d T M}.

(* top of page 11 *)
Section derivation_qperm_partl_ipartl.
Context d (E : orderType d) (M : plusArrayMonad E nat).
Implicit Types i : nat.

(* page 11 step 4 *)
Lemma qperm_preserves_length i (x p : E) (ys zs xs : seq E)
    D (k : nat -> nat -> nat -> M D) :
  (dispatch_Ret x p (ys, zs, xs) >>= write3L i) >>= uncurry3 k =
  writeList (i + (size ys + size zs).+1) xs >>
    dispatch_Ret x p (ys, zs, xs) >>= (fun '(ys', zs', xs') =>
      writeList i (ys' ++ zs') >>
        k (size ys') (size zs') (size xs')) :> M _.
Proof.
rewrite bindA [in RHS]bindA -[in RHS](plus_commute (dispatch_Ret _ _ _))//.
rewrite /=; case: ifPn => xp.
  rewrite !bindA.
  under eq_bind do rewrite bindretf write3LE.
  under [in RHS]eq_bind do rewrite bindretf -bindA.
  rewrite [RHS](qperm_preserves_size2 zs (fun a b =>
    (writeList (i + (size ys + b).+1) xs >>
    writeList i (rcons ys x ++ a)) >>
    k (size (rcons ys x)) (size a) (size xs))).
  bind_ext => zs' /=.
  rewrite -writeListC; last first.
    by rewrite size_cat size_rcons addSn.
  rewrite catA writeList_cat cat_rcons.
  by rewrite size_cat/= -addnS.
rewrite !bindA.
under eq_bind do rewrite bindretf write3LE.
under [in RHS]eq_bind do rewrite bindretf -bindA.
rewrite -addnS -(size_rcons zs x).
rewrite [RHS](qperm_preserves_size2 (rcons zs x) (fun a b =>
  (writeList (i + (size ys + b)) xs >>
  writeList i (ys ++ a)) >> k (size ys) (size a) (size xs))).
bind_ext => zs' /=.
rewrite (_ : (_ + (_ + _)) = (i + size (ys ++ zs'))); last by rewrite size_cat.
by rewrite -writeListC// catA writeList_cat.
Qed.

Lemma refin_qperm_partl_writeList (p x : E) (ys zs xs : seq E) i :
  (forall ys zs,
     writeList (M := M) i (ys ++ zs ++ xs) >>
       ipartl p i (size ys) (size zs) (size xs)
     `<=` qperm_partl p ys zs xs >>= write2L i) ->
  (writeList (M := M) (i + (size ys + size zs).+1) xs >>
    if x <= p then qperm zs >>= (fun zs' => writeList i (ys ++ x :: zs') >>
      ipartl p i (size ys).+1 (size zs') (size xs))
    else qperm (rcons zs x) >>= (fun zs' => writeList i (ys ++ zs') >>
      ipartl p i (size ys) (size zs') (size xs)))
  `<=`
  qperm_partl p ys zs (x :: xs) >>= write2L i.
Proof.
move=> ih; rewrite qperm_partl_cons.
apply: refin_trans; last exact: (refin_dispatch_Ret_write3L_ipartl ih).
rewrite qperm_preserves_length.
rewrite bindA; apply: refin_bindl => -[].
rewrite if_bind; apply: refin_if => _;
  rewrite bindA; apply: refin_bindl => zs'.
- by rewrite bindretf size_rcons -cats1 -catA /=; exact: refin_refl.
- by rewrite bindretf; exact: refin_refl.
Qed.

End derivation_qperm_partl_ipartl.

Section refin_qperm_partl.
Context d (E : orderType d) (M : plusArrayMonad E nat).

Let refin_qperm_partl_helper a b p xs :
  (apply_triple_snd qperm >=> uncurry3 (qperm_partl p)) (a, b, xs) `<=`
  apply_pair_snd (M := M) qperm (partl p (a, b) xs).
Proof.
elim: xs p a b => [/=|h t ih] p a b.
  by rewrite kleisliE apply_triple_sndE; exact: refin_refl.
rewrite [in X in _ `<=` X]/= -if_arg -fun_if if_pair(*if inside args*).
apply/(refin_trans _ (ih _ _ _))/eq_refin/esym.
rewrite -if_pair -[in LHS](if_same (h <= p) t) -if_pair(*if outside args*).
rewrite kleisliE -[X in apply_triple_snd X _]qperm_idempotent fun_if.
rewrite kleisliE apply_triple_sndE.
rewrite 2!apply_triple_snd_kleisli qperm_rcons bindA -bind_if bindA.
bind_ext => b'.
rewrite -apply_triple_snd_kleisli qperm_idempotent if_bind.
rewrite !bindA /=.
under eq_bind do rewrite bindretf.
by under [in X in if _ then _ else X]eq_bind do rewrite bindretf.
Qed.

(* footnote 8, page 10, partl'-spec *)
Lemma refin_qperm_partl a b p xs :
  qperm_partl (M := M) p a b xs `<=` apply_pair_snd qperm (partl p (a, b) xs).
Proof.
apply: refin_trans; last exact: refin_qperm_partl_helper.
rewrite kleisliE apply_triple_sndE.
rewrite -[X in X `<=` _](bindretf b (qperm_partl p a ^~ xs)).
exact/refin_bindr/refin_qperm_ret.
Qed.

End refin_qperm_partl.

(* specification of ipartl *)
Section refin_ipartl.
Context d (E : orderType d) (M : plusArrayMonad E nat).
Implicit Types i : nat.

(* page 12, used in the proof of lemma 10 *)
Let writeList_ipartl (p x : E) i (s xs : seq E) (k1 k2 : M (nat * nat)%type) :
  writeList (i + (size s).+1) xs >>
    (if x <= p then writeList i (rcons s x) >> k1
              else writeList i (rcons s x) >> k2) =
  writeList i (s ++ x :: xs) >> aget (i + size s) >>=
    (fun x => if x <= p then k1 else k2) :> M _.
Proof.
transitivity (writeList i (s ++ x :: xs) >> if x <= p then k1 else k2 : M _).
  case: ifPn => xp.
  - rewrite -cat1s catA writeList_cat.
    rewrite [in RHS]writeListC//.
    by rewrite cats1 size_rcons bindA.
  - rewrite -[in RHS]cat1s catA writeList_cat.
    rewrite writeListC//=.
    by rewrite cats1 size_rcons bindA.
rewrite bindA writeList_cat 2!bindA; bind_ext => -[].
by rewrite -bindA -writeList_ret_aget bindA bindretf.
Qed.

(* specification of ipartl, eqn 10 p.10 of mu2020flops *)
Lemma refin_ipartl p i (xs zs ys : seq E) :
  write3L i (ys, zs, xs) >>= uncurry3 (ipartl p i)
  `<=`
  qperm_partl (M := M) p ys zs xs >>= write2L i.
Proof.
elim: xs i p zs ys => [|h t ih] i p zs ys.
  apply: eq_refin.
  by rewrite /= bindretf cats0 bindA bindretf.
have : (forall ys zs,
    writeList i (ys ++ zs ++ t) >> ipartl (M := M) p i (size ys) (size zs) (size t)
    `<=` qperm_partl p ys zs t >>= write2L i).
  move=> {}ys {}zs; apply: (refin_trans _ (ih i p _ _)).
  by rewrite write3LE; exact: refin_refl.
move=> /(@refin_qperm_partl_writeList _ E M p h ys zs t i).
apply: refin_trans.
apply: (@refin_trans _ _ (writeList (i + (size ys + size zs).+1) t >>
  (if h <= p
   then writeList i (rcons (ys ++ zs) h) >>
        aswap (i + size ys) (i + size (ys ++ zs)) >>
        ipartl p i (size ys).+1 (size zs) (size t)
   else writeList i (rcons (ys ++ zs) h) >>
        ipartl p i (size ys) (size zs).+1 (size t)))); last first.
  apply: refin_bindl => -[].
  apply: refin_if => hp; last first.
    apply: (@refin_trans _ _ (Ret (rcons zs h) >>= fun zs' =>
        writeList i (ys ++ zs') >> ipartl p i (size ys) (size zs') (size t))); last first.
      exact/refin_bindr/refin_qperm_ret.
    by rewrite bindretf size_rcons rcons_cat; exact: refin_refl.
  rewrite -[X in _ `<=` X](qperm_preserves_size2 zs (fun a b =>
    writeList i (ys ++ h :: a) >> ipartl p i (size ys).+1 b (size t))).
  rewrite -[in X in _ `<=` X]bindA.
  exact/refin_bindr/refin_writeList_rcons_cat_aswap.
rewrite -size_cat.
rewrite bindA writeList_ipartl write3LE.
rewrite /uncurry3 /= -addnA -size_cat.
by rewrite bindA -catA; exact: refin_refl.
Qed.

End refin_ipartl.

Section iqsort_def.
Context d (T : orderType d) (M : plusArrayMonad T nat).

Local Obligation Tactic := idtac.

(* failed attempts *)
(*Fixpoint iqsort (i : Z) (n : nat) : M unit :=
  match n with
  | 0 => Ret tt
  | n.+1 => aget i >>= (fun p =>
         ipartl p (i) 0 0 n >>= (fun '(ny, nz) =>
         aswap i (i + ny%:Z) >>
         iqsort i ny >> iqsort (ny%:Z) nz))
  end.*)

(*Function iqsort (i : Z) (n : nat) {measure n} : M unit :=
  match n with
  | 0 => Ret tt
  | k.+1 => aget i >>= (fun p =>
            ipartl p (i + 1) 0 0 (n-1) >>= (fun '(ny, nz) => aswap i (i + ny%:Z) >> iqsort i ny))
  end.*)

(*Program Fixpoint iqsort' (ni : (Z * nat))
    (f : forall (n'j : (Z * nat)), (n'j.2 < ni.2)%coq_nat -> M unit) : M unit :=
  match ni.2 with
  | 0 => Ret tt
  | n.+1 => aget ni.1 >>= (fun p =>
            ipartl p (ni.1 + 1)%Z 0 0 n >>= (fun '(ny, nz) =>
              aswap ni.1 (ni.1 + ny%:Z) >>
              f (ni.1, ny) _ >> f ((ni.1 + ny%:Z + 1)%Z, nz) _))
  end.
Next Obligation.
move => [i [//|n']] /= _ n [<-] p [a b] /= a' _ [-> _] _.*)

(* From Equations Require Import Equations. *)

(* Equations? qperm (s : seq A) : M (seq A) by wf (size s) lt :=
| [::] => Ret [::]
| x :: xs =>
  splits_bseq xs >>=
    (fun '(ys, zs) => liftM2 (fun a b => a ++ x :: b) (qperm ys : M (seq A)) (qperm zs)).
Proof.
apply /ltP.
exact: (leq_ltn_trans (size_bseq b)).
apply /ltP.
exact: (leq_ltn_trans (size_bseq b0)).
Defined. *)

(* Set Printing All.
Equations? iqsort n i : M unit by wf n lt :=
iqsort O i := Ret tt ;
iqsort n.+1 i := aget i >>= (fun p =>
  dipartl p (i + 1) 0 0 n >>= (fun '(ny, nz) =>
  aswap i (i + ny%:Z) >>
  iqsort ny i >> iqsort nz (i + ny%:Z + 1)%Z)). *)

Program Fixpoint iqsort' ni
    (f : forall mj, (mj.2 < ni.2)%coq_nat -> M unit) : M unit :=
  match ni.2 with
  | 0 => Ret tt
  | n.+1 => aget ni.1 >>= (fun p =>
            dipartl p ni.1.+1 0 0 n >>= (fun nynz =>
              let ny := nynz.1 in
              let nz := nynz.2 in
              aswap ni.1 (ni.1 + ny) >>
              f (ni.1, ny) _ >> f (ni.1 + ny.+1, nz) _))
  end.
Next Obligation.
move => [i [//|n']] /= _ n [<-] p [[a b] /=] /andP[an _] _.
apply/ssrnat.ltP; rewrite ltnS.
by rewrite 2!addn0 in an.
Qed.
Next Obligation.
move => [i [//|n']] /= _ n [<-] p [[a b] /=] /andP[_ bn] _.
apply/ssrnat.ltP; rewrite ltnS.
by rewrite 2!addn0 in bn.
Qed.

Lemma well_founded_lt2 : well_founded (fun x y : nat * nat => (x.2 < y.2)%coq_nat).
Proof.
by apply: (@Wf_nat.well_founded_lt_compat _ _) => -[x1 x2] [y1 y2]; exact.
Qed.

Definition iqsort : nat * nat -> M unit :=
  Fix well_founded_lt2 (fun _ => M unit) iqsort'.

Lemma iqsort'_Fix (ni : nat * nat)
  (f g : forall (n'j : nat * nat), (n'j.2 < ni.2)%coq_nat -> M unit) :
  (forall (n'j : nat * nat) (p : (n'j.2 < ni.2)%coq_nat), f n'j p = g n'j p) ->
  iqsort' f = iqsort' g.
Proof.
by move=> ?; congr iqsort'; apply funext_dep => ?; apply boolp.funext.
Qed.

Lemma iqsort_nil i : iqsort (i, 0) = Ret tt.
Proof. by rewrite /iqsort Fix_eq //; exact: iqsort'_Fix. Qed.

Let iqsort_cons0 i (n : nat) : iqsort (i, n.+1) = aget i >>= (fun p =>
  dipartl p i.+1 0 0 n >>= (fun nynz =>
    let '(ny, nz) := (dipartlT1 nynz, dipartlT2 nynz) in
    aswap i (i + ny) >>
    iqsort (i, ny) >> iqsort (i + ny.+1, nz))).
Proof. by rewrite [in LHS]/iqsort Fix_eq //=; exact: iqsort'_Fix. Qed.

Lemma iqsort_cons i (n : nat) : iqsort (i, n.+1) = aget i >>= (fun p =>
  ipartl p i.+1 0 0 n >>= (fun nynz =>
    let '(ny, nz) := nynz in
    aswap i (i + ny) >>
    iqsort (i, ny) >> iqsort (i + ny.+1, nz))).
Proof.
rewrite iqsort_cons0; bind_ext => p.
rewrite ipartlE/= fmapE [in RHS]bindA; bind_ext => -[[ny nz] Hnynz].
by rewrite bindretf.
Qed.

End iqsort_def.
Arguments iqsort {d T M}.

Section iqsort_spec.
Context d (E : orderType d) (M : plusArrayMonad E nat).
Implicit Types i : nat.

(* eqn 12 page 13 *)
Lemma iqsort_slowsort i xs :
  writeList i xs >> iqsort (M := M) (i, size xs) `<=` slowsort xs >>= writeList i.
Proof.
have [n nxs] := ubnP (size xs); elim: n xs i => // n ih xs i in nxs *.
move: xs => [|p xs] in nxs *.
  by rewrite /= iqsort_nil slowsort_nil 2!bindretf /=; exact: refin_refl.
(* step 1: l.342 in IQSOrt.agda,
   corresponds to second equation on page 13 of mu2020flops *)
pose p1 : M unit := qperm_partl p [::] [::] xs >>= (fun '(ys, zs) =>
  writeList (i + (size ys).+1) zs >>
  qperm ys >>= (fun ys' => writeList i (rcons ys' p) >>
    iqsort (i, size ys) >>
    iqsort (i + (size ys).+1, size zs))).
apply: (@refin_trans _ _ p1).
- (* step 2: introduce aswap *)
  apply: (@refin_trans _ _ (qperm_partl p [::] [::] xs >>= (fun '(ys, zs) =>
         writeList (i + (size ys).+1) zs >>
         (writeList i (p :: ys) >> aswap i (i + size ys)) >>
         (iqsort (i, size ys)) >> iqsort (i + (size ys).+1, size zs)))).
    (* step 3: commute *)
  + rewrite [X in _ `<=` X](_ : _ = qperm_partl p [::] [::] xs >>= (fun '(ys, zs) =>
       aput i p >> writeList i.+1 (ys ++ zs) >>
       (aswap i (i + size ys)) >>
       (iqsort (i, size ys)) >> iqsort (i + (size ys).+1, size zs))); last first.
      bind_ext => -[ys zs].
      rewrite -bindA -writeListC//.
      by rewrite /= bindA writeList_cat !bindA -addSnnS.
    (* step 4: commute *)
    rewrite [X in _ `<=` X](_ : _ = aput i p >>
       qperm_partl p [::] [::] xs >>= (fun '(ys, zs) =>
       (writeList i.+1 (ys ++ zs) >>
        aswap i (i + size ys) >>
        iqsort (i, size ys) >> iqsort (i + (size ys).+1, size zs)))); last first.
      rewrite [RHS]bindA.
      rewrite -(plus_commute (qperm_partl p [::] [::] xs))//.
      by bind_ext=> -[a b]; rewrite !bindA.
    (* step 5 *)
    rewrite {nxs}.
    rewrite [X in _ `<=` X](_ : _ = aput i p >> qperm_partl p [::] [::] xs >>=
        (fun '(ys, zs) => write2L i.+1 (ys, zs)) >>= (fun '(ny, nz) =>
          aswap i (i + ny) >> iqsort (i, ny) >>
          iqsort (i + ny.+1, nz))); last first.
      by rewrite [in RHS]bindA; bind_ext => -[a b]; rewrite write2LE !bindA.
    (* step 6: refin_ipartl_qperm_partl *)
    rewrite [in X in _ `<=` X](bindA (aput i p)).
    apply: refin_trans; last first.
      by rewrite bindA; apply: refin_bindl => ttt; exact/refin_bindr/refin_ipartl.
    (* step 7 *)
    rewrite -[in X in _ `<=` X]bindA.
    rewrite (_ : aput i p >> _ = (writeList i (p :: xs) >> Ret p) >>=
        (fun p => ipartl p i.+1 0 0 (size xs))); last first.
      by rewrite /= bindA -[in LHS](bindA (aput i p)) [in RHS]bindA !bindretf.
    (* step 8 *)
    rewrite writeListRet 2![in X in _ `<=` X]bindA.
    by apply: refin_bindl => -[]; rewrite /= iqsort_cons bindA; exact: refin_refl.
  + apply: refin_bindl => -[ys sz].
    rewrite 4!bindA.
    apply: refin_bindl => -[].
    rewrite -2![in X in _ `<=` X]bindA.
    rewrite [in X in _ `<=` X](bindA _ (fun _ => iqsort _) (fun _ => iqsort _)).
    rewrite -2![in X in X `<=` _]bindA.
    rewrite [in X in X `<=` _](bindA _ (fun _ => iqsort _) (fun _ => iqsort _)).
    apply: refin_bindr.
    exact: refin_writeList_cons_aswap.
- (* step 1a: refin_partition_slowsort *)
  apply: refin_trans; last exact/refin_bindr/refin_partition_slowsort.
  rewrite bindretf.
  move pxs : (partition p xs) => tmp; case: tmp => [ys zs] in pxs *.
  (* step 1b: introduce qperm's and commute *)
  rewrite -qperm_slowsort 2!kleisliE !bindA.
  rewrite [X in _ `<=` X](_ : _ =
    (do zs' <- qperm zs; do ys' <- qperm ys; do ys'' <- slowsort ys';
     do zs'' <- slowsort zs'; writeList i (ys'' ++ p :: zs''))%Do); last first.
    rewrite (plus_commute (qperm zs))//.
    bind_ext => ys'.
    rewrite !bindA; under eq_bind do rewrite !bindA.
    rewrite -(plus_commute (qperm zs))//.
    bind_ext => zs'; bind_ext => ys''.
    by rewrite bindA; under eq_bind do rewrite bindretf.
  (* step 1c: refine partl to qperm_partl *)
  apply: refin_trans; first exact/refin_bindr/refin_qperm_partl.
  (* step 1d: execute the first qperm and record size information *)
  rewrite -partition_partl pxs bindA /=.
  under eq_bind do rewrite bindretf.
  rewrite bind_qperm_guard [in X in _ `<=` X]bind_qperm_guard(*NB: interesting?*).
  apply: refin_bindl => zs'.
  apply: refin_bind_guard => /eqP zszs'.
  (* step 1e: commutation *)
  rewrite ![in X in X `<=` _]bindA.
  rewrite -(plus_commute (qperm ys))//.
  (* step 1f: qperm_preserves_size2,
     execute the second qperm and record size information *)
  rewrite (qperm_preserves_size2 ys (fun a b =>
    (writeList (i + b.+1) zs' >> (writeList i (rcons a p) >>
      iqsort (i, b) >> iqsort (i + b.+1, size zs'))))).
  rewrite bind_qperm_guard [in X in _ `<=` X]bind_qperm_guard (*NB: interesting?*).
  apply: refin_bindl => ys'.
  apply: refin_bind_guard => /eqP ysys'.
  (* step 1g: ih *)
  rewrite -cats1 writeList_cat writeListC//.
  rewrite (bindA _ _ (fun _ => iqsort (i, size ys'))).
  apply: (@refin_trans _ _ (
      (writeList (i + (size ys').+1) zs' >>
      (writeList (i + size ys') [:: p] >>
      (slowsort ys' >>= writeList i))) >>
      iqsort (i + (size ys').+1, size zs'))).
    rewrite !bindA.
    do 2 apply: refin_bindl => -[].
    rewrite 2!bindretf -2!bindA; apply/refin_bindr/ih.
    move: nxs; rewrite /= ltnS; apply: leq_ltn_trans.
    by rewrite -ysys' -(size_partition p xs) pxs /= leq_addr.
  (* step 1h: slowsort_preserves_size2 *)
  rewrite -[in X in X `<=` _](plus_commute (slowsort ys'))//.
  rewrite !bindA.
  rewrite -[in X in X `<=` _](plus_commute (slowsort ys'))//.
  rewrite (slowsort_preserves_size2 _
    (fun a b => writeList (i + b.+1) zs' >>
      (writeList (i + b) [:: p] >> writeList i a >>
        iqsort (i + b.+1, size zs')))).
  rewrite bind_slowsort_guard [in X in _ `<=` X]bind_slowsort_guard.
  apply: refin_bindl => ys''.
  apply: refin_bind_guard => /eqP ys'ys''.
  rewrite -bindA -(writeListC _ _ ys'')//.
  under [in X in _ `<=` X]eq_bind do rewrite -cat_rcons.
  under [in X in _ `<=` X]eq_bind do rewrite writeList_cat.
  rewrite (plus_commute (slowsort zs'))//.
  rewrite -(writeList_cat i ys'' [:: p]) -(writeListC _ _ _ zs'); last first.
    by rewrite /= cats1 size_rcons/=.
  (* step 1i: ih *)
  rewrite cats1 bindA; apply: refin_bindl => -[].
  rewrite size_rcons; apply: ih.
  move: nxs; rewrite /= ltnS; apply: leq_ltn_trans.
  by rewrite -zszs' -(size_partition p xs) pxs /= leq_addl.
Qed.

End iqsort_spec.
