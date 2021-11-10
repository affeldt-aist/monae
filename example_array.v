(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2020 monae authors, license: LGPL-2.1-or-later               *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require boolp.
Require Import monae_lib hierarchy monad_lib fail_lib state_lib.
Require Import example_quicksort.
From infotheo Require Import ssr_ext.

(******************************************************************************)
(*                  Quicksort with the Array Monad (WIP)                      *)
(*                                                                            *)
(*  iqsort (i, n) == quicksort the sub-array of size n stored at address i    *)
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

From infotheo Require Import ssrZ.
Require Import ZArith.

Local Open Scope zarith_ext_scope.
(* TODO: is in infotheo master, remove *)
Lemma ltZ_addl a b c : (0 <= b -> a < c -> a < b + c)%Z.
Proof. by move=> b0 ac; rewrite -(add0Z a); exact: leZ_lt_add. Qed.

Lemma ltZ_addr a b c : (0 < c -> a <= b -> a < b + c)%Z.
Proof. by move=> b0 ac; rewrite -(addZ0 a); exact: leZ_lt_add. Qed.

Lemma intRD (n m : nat) : (n + m)%:Z = (n%:Z + m%:Z)%Z.
Proof. exact: Nat2Z.inj_add. Qed.

Lemma leZ0n (n : nat) : (0 <= n%:Z)%Z.
Proof. exact: Zle_0_nat. Qed.
(* /TODO: is in infotheo master, remove *)

Local Close Scope zarith_ext_scope.

Lemma kleisliA {M : monad} A B C D (f : A -> M B) (g : B -> M C) (h : C -> M D) :
  f >=> g >=> h = f >=> (g >=> h).
Proof.
  apply: fun_ext_dep => x.
  rewrite !kleisliE bindA.
  bind_ext => ?.
  by rewrite kleisliE.
Qed.

(* TODO: move *)
Definition second {M : monad} {A B C} (f : B -> M C) (xy : (A * B)%type) :=
  f xy.2 >>= (fun y' => Ret (xy.1, y')).

Definition uncurry3 :=
  (fun (A B C D : UU0) (f : A -> B -> C -> D) (X : A * B * C) =>
  let (p, c) := X in let (a, b) := p in f a b c).

Definition curry3 :=
  (fun (A B C D : UU0) (f : A * B * C -> D) =>
  fun a b c => f (a, b, c)).

Section dassert.
Context {M : failMonad} (N : failMonad) (A : Type) (p : pred A).

Definition dassert (a : A) : M { a | p a } :=
  if Bool.bool_dec (p a) true is left H then Ret (exist p a H) else fail.

End dassert.

(* TODO: move*)
Lemma bind_ext_guard {M : failMonad} A (b : bool) (m1 m2 : M A) : (b -> m1 = m2) ->
  guard b >> m1 = guard b >> m2.
Proof. by case: b => [->//|_]; rewrite guardF !bindfailf. Qed.

(* TODO: move*) (* NB: worth explaining *)
Lemma bind_refin_guard {M : plusMonad} A (b : bool) (m1 m2 : M A) : (b -> m1 `>=` m2) ->
  guard b >> m1 `>=` guard b >> m2.
Proof.
case: b => [h|_]; first by apply: refin_bindl => -[]; exact: h.
by rewrite guardF !bindfailf; exact: refin_refl.
Qed.

Section more_about_liftM2.

Lemma bind_liftM2 {M : monad} A B C (f : seq A -> seq B -> seq C)
    (m1 : M (seq A)) (m2 : M (seq B)) n :
  (forall a b, size (f a b) = size a + size b + n) ->
  liftM2 f m1 m2 >>= (fun x => Ret (x, size x)) =
  liftM2 (fun a b => (f a.1 b.1, a.2 + b.2 + n))
          (m1 >>= (fun x => Ret (x, size x)))
          (m2 >>= (fun x => Ret (x, size x))).
Proof.
move=> hf.
rewrite /liftM2 !bindA; bind_ext => x1.
rewrite !bindretf !bindA.
bind_ext=> x2.
by rewrite !bindretf /= hf.
Qed.
Arguments bind_liftM2 {M A B C} {f} {m1} {m2} _.

Lemma nondetPlus_sub_liftM2 {M : plusMonad} A B C f ma mb :
  nondetPlus_sub ma -> nondetPlus_sub mb ->
  nondetPlus_sub (@liftM2 M A B C f ma mb).
Proof.
move=> [s1 s1_ma] [s2 s2_mb].
exists (ndBind s1 (fun a => ndBind s2 (fun b => ndRet (f a b)))).
by rewrite /= s1_ma s2_mb.
Qed.

End more_about_liftM2.

Definition preserves {M : monad} A B (f : A -> M A) (g : A -> B) :=
  forall x, (f x >>= fun x' => Ret (x' , g x')) = (f x >>= fun x' => Ret (x' , g x)).

Section more_about_qperm.
Variable M : plusMonad.

Lemma nondetPlus_sub_splits A (s : seq A) : nondetPlus_sub (@splits M _ s).
Proof.
elim: s => [|h t ih /=]; first by exists (ndRet ([::], [::])).
have [syn syn_splits] := ih.
exists (ndBind syn (fun '(a, b) => ndAlt (ndRet (h :: a, b)) (ndRet (a, h :: b)))).
rewrite /= syn_splits.
by bind_ext => -[].
Qed.

Lemma nondetPlus_sub_tsplits A (s : seq A) : nondetPlus_sub (tsplits s : M _).
Proof.
elim: s => [|h t ih]; first by exists (ndRet (bseq0 0 A, bseq0 0 A)).
have [syn syn_tsplits] := ih.
exists (ndBind syn (fun '(a, b) => ndAlt
    (ndRet ([bseq of h :: a], widen_bseq (leqnSn _) b))
    (ndRet (widen_bseq (leqnSn _) a, [bseq of h :: b])))).
by rewrite /= syn_tsplits; bind_ext => -[].
Qed.

Lemma nondetPlus_sub_qperm A (s : seq A) : nondetPlus_sub (@qperm M _ s).
Proof.
have [n sn] := ubnP (size s); elim: n s => // n ih s in sn *.
move: s => [|h t] in sn *; first by exists (ndRet [::]); rewrite qperm_nil.
rewrite qperm_cons.
rewrite example_quicksort.splitsE /=. (*TODO: rename, there are two splitsE lemmas*)
rewrite fmapE (*TODO: broken ret notation*).
rewrite bindA.
have [syn syn_tsplits] := nondetPlus_sub_tsplits t.
have nondetPlus_sub_liftM2_qperm : forall a b : (size t).-bseq A,
  nondetPlus_sub (@liftM2 M _ _ _ (fun x y => x ++ h :: y) (qperm a) (qperm b)).
  move=> a b; apply nondetPlus_sub_liftM2 => //; apply: ih.
  - by rewrite (leq_ltn_trans (size_bseq a)).
  - by rewrite (leq_ltn_trans (size_bseq b)).
exists (ndBind syn (fun a => sval (nondetPlus_sub_liftM2_qperm a.1 a.2))).
rewrite /= syn_tsplits.
bind_ext => -[a b] /=.
rewrite bindretf.
by case: (nondetPlus_sub_liftM2_qperm _ _).
Qed.

Lemma nondetPlus_sub_slowsort d (A : porderType d) (s : seq A) : nondetPlus_sub (@slowsort M _ _ s).
Proof.
rewrite /slowsort.
rewrite kleisliE.
have [syn syn_qperm] := nondetPlus_sub_qperm s.
exists (ndBind syn (fun a => ndBind (if sorted <=%O a then ndRet tt else ndFail unit) (fun _ : unit => ndRet a))).
rewrite /=.
rewrite syn_qperm.
bind_ext => s'.
(* TODO: too many unfolds *)
rewrite /assert.
unlock.
rewrite /guard.
unlock.
by case: ifPn.
Qed.

End more_about_qperm.

Local Open Scope zarith_ext_scope.

Section marray.
Context {d : unit} {E : porderType d} {M : plusArrayMonad E Z_eqType}.

Fixpoint readList (i : Z) (n : nat) : M (seq E) :=
  if n isn't k.+1 then Ret [::] else liftM2 cons (aget i) (readList (i + 1) k).

Fixpoint writeList (i : Z) (s : seq E) : M unit :=
  if s isn't x :: xs then Ret tt else aput i x >> writeList (i + 1) xs.

Definition writeL (i : Z) (s : seq E) := writeList i s >> Ret (size s).

Definition write2L (i : Z) '(s1, s2) :=
  writeList i (s1 ++ s2) >> Ret (size s1, size s2).

Definition write3L (i : Z) '(xs, ys, zs) :=
  writeList i (xs ++ ys ++ zs) >> Ret (size xs, size ys, size zs).

Lemma writeList_cat (i : Z) (xs ys : seq E) :
  writeList i (xs ++ ys) = writeList i xs >> writeList (i + (size xs)%:Z) ys.
Proof.
elim: xs i => [|h t ih] i /=; first by rewrite bindretf addZ0.
by rewrite ih bindA -addZA add1Z natZS.
Qed.

Definition swap (i j : Z) : M unit :=
  aget i >>= (fun x => aget j >>= (fun y => aput i y >> aput j x)).

Lemma swapii (i : Z) : swap i i = skip.
Proof.
rewrite /swap agetget.
under eq_bind do rewrite aputput.
by rewrite agetpustskip.
Qed.

Lemma writeList_cons {i : Z} (x : E) (xs : seq E) :
  writeList i (x :: xs) = aput i x >> writeList (i + 1) xs.
Proof. by done. Qed.

Lemma writeList_rcons {i : Z} (x : E) (xs : seq E) :
  writeList i (rcons xs x) = writeList i xs >> aput (i + (size xs)%:Z)%Z x.
Proof. by rewrite -cats1 writeList_cat /= -bindA bindmskip. Qed.

Lemma aput_writeListC (i j : Z) {x : E} {xs : seq E}:
  (i < j)%Z ->
  aput i x >> writeList j xs =
  writeList j xs >> aput i x.
Proof.
  elim: xs i j => [|h t ih] i j hyp.
  by rewrite bindretf bindmskip.
  rewrite /= -bindA aputC.
  rewrite !bindA.
  bind_ext => ?.
  apply: ih _.
  by rewrite ltZadd1; apply ltZW.
  by left; apply/eqP/ltZ_eqF.
Qed.

Lemma write_writeListC (i j : Z) {x : E} {xs : seq E}:
  (i < j)%Z ->
  aput i x >> writeList j xs =
  writeList j xs >> aput i x.
Proof.
  elim: xs i j => [|h t ih] i j hyp.
  by rewrite bindretf bindmskip.
  rewrite /= -bindA aputC.
  rewrite !bindA.
  bind_ext => ?.
  apply: ih _.
  by rewrite ltZadd1; apply ltZW.
  by left; apply/eqP/ltZ_eqF.
Qed.

Lemma writeList_writeListC {i j : Z} {ys zs : seq E}:
  (i + (size ys)%:Z <= j)%Z ->
  writeList i ys >> writeList j zs =
  writeList j zs >> writeList i ys.
Proof.
elim: ys zs i j => [|h t ih] zs i j hyp.
  by rewrite bindretf bindmskip.
rewrite /= write_writeListC; last first.
  by rewrite ltZadd1; exact: leZZ.
rewrite bindA write_writeListC; last first.
  apply: (ltZ_leZ_trans _ hyp).
  by apply: ltZ_addr => //; exact: leZZ.
rewrite -!bindA ih => [//|].
by rewrite /= natZS -add1Z (* -> addZ1 *) addZA in hyp.
Qed.

Lemma aput_writeListCR (i j : Z) {x : E} {xs : seq E}:
  (j + (size xs)%:Z <= i)%Z ->
  aput i x >> writeList j xs =
  writeList j xs >> aput i x.
Proof.
move=> ?.
have->: aput i x = writeList i [:: x].
by rewrite /= bindmskip.
by rewrite writeList_writeListC.
Qed.

Lemma write_read {i : Z} {p} : aput i p >> aget i = aput i p >> Ret p :> M _.
Proof. by rewrite -[RHS]aputget bindmret. Qed.

Lemma write_readC {i j : Z} {p} :
  i != j -> aput i p >> aget j = aget j >>= (fun v => aput i p >> Ret v) :> M _.
Proof. by move => ?; rewrite -aputgetC // bindmret. Qed.

Lemma introduce_read {i : Z} (p : E) (xs : seq E) :
  writeList i (p :: xs) >> Ret p =
  writeList i (p :: xs) >> aget i.
Proof.
  rewrite /=.
  elim/last_ind: xs p i => [/= p i|].
  by rewrite bindmskip write_read.
  move => h t ih p i /=.
  transitivity (
    (aput i p >> writeList (i + 1) h >> aput (i + 1 + (size h)%:Z)%Z t) >> aget i
  ); last first.
  by rewrite writeList_rcons !bindA.
  rewrite ![RHS]bindA.
  rewrite write_readC.
  rewrite -2![RHS]bindA -ih [RHS]bindA.
  transitivity (
    (aput i p >> writeList (i + 1) h >> aput (i + 1 + (size h)%:Z)%Z t) >> Ret p
  ).
  by rewrite writeList_rcons !bindA.
  rewrite !bindA.
  bind_ext => ?.
  bind_ext => ?.
  by rewrite bindretf.
  apply/negP =>/eqP/esym.
  apply ltZ_eqF.
  rewrite -{1}(addZ0 i) -addZA ltZ_add2l.
  apply addZ_gt0wl => //.
  apply/leZP.
  rewrite -natZ0 -leZ_nat //. (* TODO: cleanup *)
Qed.

(* TODO *)
Lemma aput_writeList_cons {i : Z} {x h : E} {t : seq E} :
  writeList i (rcons (h :: t) x) =
  writeList i (rcons (x :: t) h) >> swap i (i + (size (rcons t h))%:Z).
  (* aput i x >> writeList (i + 1) (rcons t h) >> swap i (i + (size (rcons t h))%:Z). *)
  (* aput i h >> writeList (i + 1) (rcons t x) =
  aput i x >>
      ((aput (i + 1)%Z h >> writeList (i + 1 + 1) t) >>
        swap i (i + (size t).+1%:Z)). *)
Proof.
  rewrite /swap -!bindA.
  rewrite writeList_rcons.
  rewrite /=.
  rewrite aput_writeListC.
  rewrite bindA.
  rewrite aput_writeListC.
  rewrite writeList_rcons.
  rewrite !bindA.
  bind_ext => ?.
  under [RHS] eq_bind do rewrite -bindA.
  rewrite aputget.
  rewrite -bindA.
  rewrite size_rcons.
  rewrite -addZA natZS -add1Z.
  under [RHS] eq_bind do rewrite -!bindA.
  rewrite aputgetC.
  rewrite -!bindA.
  rewrite aputget.
  rewrite aputput aputC.
  rewrite bindA.
  by rewrite aputput.
  - by right.
  - apply /eqP/ltZ_eqF.
    apply /ltZ_addr; last by apply leZZ.
    by rewrite add1Z -natZS.
  - by rewrite ltZadd1; exact: leZZ.
  - by rewrite ltZadd1; exact: leZZ.
Qed.

Lemma aput_writeList_rcons {i : Z} {x h : E} {t : seq E}:
  aput i x >> writeList (i + 1) (rcons t h) =
  aput i h >>
      ((writeList (i + 1) t >> aput (i + 1 + (size t)%:Z)%Z x) >>
        swap i (i + (size t).+1%:Z)).
Proof.
rewrite /swap -!bindA.
rewrite writeList_rcons -bindA.
rewrite aput_writeListC; last by rewrite ltZadd1; exact: leZZ.
rewrite aput_writeListC; last by rewrite ltZadd1; exact: leZZ.
rewrite !bindA.
bind_ext => ?.
under [RHS] eq_bind do rewrite -bindA.
rewrite aputgetC; last first.
- apply /eqP/gtZ_eqF.
  rewrite -addZA.
  apply /ltZ_addr; last by apply leZZ.
  by rewrite add1Z -natZS.
rewrite -bindA.
rewrite -addZA natZS -add1Z aputget.
under [RHS] eq_bind do rewrite -!bindA.
rewrite aputget aputC; last first.
- by right.
by rewrite -!bindA aputput bindA aputput.
Qed.

(* used in the proof of writeList_ipartl *)
Lemma introduce_read_sub {i : Z} (p : E) (xs : seq E) (f : E -> M (nat * nat)%type):
  writeList i (p :: xs) >> Ret p >> f p =
  writeList i (p :: xs) >> aget i >>= f.
Proof.
  rewrite introduce_read 2!bindA /=.
  rewrite aput_writeListC; last first.
  rewrite ltZadd1 leZ_eqVlt; exact: or_introl.
  rewrite 2!bindA.
  under [LHS] eq_bind do rewrite -bindA aputget.
  by under [RHS] eq_bind do rewrite -bindA aputget.
Qed.

End marray.

(* TODO: move *)
Lemma mem_rcons_cat (A : eqType) (b : seq A) h : h \in b -> exists b1 b2, b = rcons b1 h ++ b2.
Proof.
move=> hb; exists (take (index h b) b), (drop (index h b).+1 b).
rewrite -cats1 -catA -{1}(cat_take_drop (index h b) b); congr (_ ++ _) => /=.
by rewrite -{2}(nth_index h hb) -drop_nth // index_mem.
Qed.

Section ssplits.
Variable (d : unit) (E : porderType d) (M : plusArrayMonad E Z_eqType).

Let split_pair A n : Type := {x : seq A * seq A | size x.1 + size x.2 = n}.

Local Obligation Tactic := idtac.

Program Fixpoint ssplits A (s : seq A) : M (split_pair A (size s))%type :=
  match s with
  | [::] => Ret (exist _ ([::], [::]) _)
  | x :: xs => (do yz <- ssplits xs; Ret (exist _ (x :: yz.1, yz.2) _) [~]
                                  Ret (exist _ (yz.1, x :: yz.2) _))%Do
  end.
Next Obligation. by []. Qed.
Next Obligation.
by move=> A [//|x' xs'] x xs [xx' xsxs'] [[a b] /=] <-; rewrite addSn.
Qed.
Next Obligation.
by move=> A [//|x' xs'] x xs [xx' xsxs'] [[a b] /=] <-; rewrite -addnS.
Qed.

Local Open Scope mprog.
Lemma splitsE A (s : seq A) :
  splits s = fmap (fun xy => ((sval xy).1, (sval xy).2)) (ssplits s) :> M _.
Proof.
elim: s => [|h t ih]; first by rewrite fmapE /= bindretf.
rewrite /= fmapE bindA ih /= fmapE !bindA; bind_ext => -[[a b] ab] /=.
by rewrite bindretf /= alt_bindDl /=; congr (_ [~] _); rewrite bindretf.
Qed.
Local Close Scope mprog.

Lemma splits_preserves_subseq (A : eqType) (s : seq A) :
  splits s = (do x <- splits s;
    guard [&& subseq x.1 s, subseq x.2 s & (perm_eq (x.1 ++ x.2) s)] >> Ret x)%Do :> M _.
Proof.
have [n ns] := ubnP (size s); elim: n s ns => // n ih s ns.
move: s => [|h t] in ns *.
  by rewrite /= bindretf /= perm_refl guardT bindskipf.
rewrite /= ltnS in ns.
rewrite /= !bindA.
rewrite ih // !bindA; bind_ext => -[a b] /=.
rewrite !bindA.
apply: bind_ext_guard => /and3P[ta tb abt].
rewrite !bindretf /=.
rewrite !alt_bindDl !bindretf; congr (_ [~] _) => /=.
  rewrite eqxx ta /=.
  rewrite perm_cons abt andbT.
  destruct b as [|b1 b2].
    by rewrite guardT bindskipf.
  case: ifPn => [/eqP->|b1h].
    by rewrite (cons_subseq tb) guardT bindskipf.
  by rewrite tb guardT bindskipf.
rewrite -cat_rcons -cats1 -catA perm_catCA perm_cons abt.
rewrite eqxx tb 2!andbT.
destruct a as [|a1 a2].
  by rewrite guardT bindskipf.
case: ifPn => [/eqP->|a1h].
  by rewrite (cons_subseq ta) guardT bindskipf.
by rewrite ta guardT bindskipf.
Qed.

(* NB: can't use the preserves predicate because the input/output of splits
   are of different sizes *)
(* NB: not used *)
Lemma splits_preserves_size (A : eqType) (x : seq A) :
  (splits x >>= fun x' => Ret (x', size x'.1 + size x'.2)) =
  (splits x >>= fun x' => Ret (x', size x)) :> M _.
Proof.
rewrite splits_preserves_subseq 2!bindA; bind_ext => -[a b] /=.
rewrite 2!bindA; apply: bind_ext_guard => /and3P[_ _ abx].
by rewrite 2!bindretf /= -size_cat (perm_size abx).
Qed.

Lemma qperm_preserves_size A : preserves (@qperm M A) size.
Proof.
move=> s.
have [n ns] := ubnP (size s); elim: n s ns => // n ih s ns.
move: s => [|p s] in ns *.
  by rewrite !qperm_nil !bindretf.
rewrite /= ltnS in ns.
rewrite qpermE !bindA.
(*bind_ext => -[a b]. (* we lose the size information *)*)
rewrite !splitsE !fmapE !bindA.
bind_ext => -[[a b] /= ab].
rewrite !bindretf.
rewrite (@bind_liftM2 _ _ _ _ _ _ _ 1%N); last first.
  by move=> x y; rewrite size_cat /= addn1 -addnS.
rewrite {1}/liftM2.
rewrite ih; last by rewrite (leq_trans _ ns)// ltnS -ab leq_addr.
rewrite /liftM2 !bindA.
bind_ext => xa.
rewrite bindretf.
rewrite ih; last by rewrite (leq_trans _ ns)// ltnS -ab leq_addl.
rewrite !bindA.
bind_ext => xb.
rewrite !bindretf /=.
by rewrite ab addn1.
Qed.

(* NB: easier to user than qperm_preserves_size? worth explaining? *)
Lemma qperm_preserves_size2 (x : seq E) B (f : seq E -> nat -> M B) :
  (do x' <- qperm x; f x' (size x))%Do = (do x' <- qperm x; f x' (size x'))%Do :> M _.
Proof.
transitivity ((do x' <- (do y <- qperm x; Ret (y, size y)); f x'.1 x'.2)%Do).
  by rewrite qperm_preserves_size bindA; bind_ext => s; rewrite bindretf.
by rewrite bindA; bind_ext => s; rewrite bindretf.
Qed.

Lemma bind_qperm_guard (s : seq E) B (f : seq E -> M B) :
  (do x <- qperm s; f x = do x <- qperm s; guard (size s == size x) >> f x)%Do.
Proof.
rewrite -(qperm_preserves_size2 s (fun a b => guard (size s == b) >> f a)).
rewrite eqxx guardT.
by under [in RHS]eq_bind do rewrite bindskipf.
Qed.

Lemma qperm_preserves_elements (s : seq E) :
  qperm s = (do x <- qperm s; guard (perm_eq x s) >> Ret x)%Do :> M _.
Proof.
have [n ns] := ubnP (size s); elim: n s ns => // n ih s ns.
move: s => [|h t] in ns *.
  by rewrite qperm_nil bindretf perm_refl guardT bindskipf.
rewrite /= ltnS in ns.
rewrite qperm_cons bindA.
rewrite splits_preserves_subseq !bindA.
bind_ext => -[a b].
rewrite /= !bindA.
apply: bind_ext_guard => /and3P[_ _ abt].
rewrite /=.
rewrite /liftM2 /=.
rewrite !bindretf.
rewrite !bindA.
rewrite ih; last first.
  by rewrite (leq_trans _ ns) // ltnS -(perm_size abt) size_cat leq_addr.
rewrite !bindA.
bind_ext => a'.
rewrite !bindA.
apply: bind_ext_guard => aa'.
rewrite !bindretf !bindA.
rewrite ih; last first.
  by rewrite (leq_trans _ ns) // ltnS -(perm_size abt) size_cat leq_addl.
rewrite !bindA.
bind_ext => b'.
rewrite !bindA.
apply: bind_ext_guard => bb'.
rewrite !bindretf.
rewrite -cat_rcons -cats1 -catA perm_catCA perm_cons.
have ab'ab := perm_cat aa' bb'.
by rewrite (perm_trans ab'ab abt) guardT bindskipf.
Qed.

Lemma slowsort_preserves_size : preserves (@slowsort M _ E) size.
Proof.
move=> s.
have [n ns] := ubnP (size s); elim: n s ns => // n ih s ns.
move: s => [|p s] in ns *.
  by rewrite /= slowsort_nil 2!bindretf.
rewrite /= ltnS in ns.
rewrite /slowsort kleisliE !bindA.
rewrite (qperm_preserves_size2 _ (fun a b => (do x' <- assert (sorted <=%O) a; Ret (x', b))%Do)).
bind_ext => ht.
rewrite assertE 2!bindA.
apply: bind_ext_guard => _.
by rewrite 2!bindretf.
Qed.

Lemma slowsort_preserves_size2 (x : seq E) B (f : seq E -> nat -> M B) :
  (do x' <- slowsort x; f x' (size x))%Do = (do x' <- slowsort x; f x' (size x'))%Do :> M _.
Proof.
transitivity ((do x' <- (do y <- slowsort x; Ret (y, size y)); f x'.1 x'.2)%Do).
  by rewrite slowsort_preserves_size bindA; bind_ext => s; rewrite bindretf.
by rewrite bindA; bind_ext => s; rewrite bindretf.
Qed.

Lemma bind_slowsort_guard (s : seq E) B (f : seq E -> M B) :
  (do x <- slowsort s; f x = do x <- slowsort s; guard (size s == size x) >> f x)%Do.
Proof.
rewrite -(slowsort_preserves_size2 s (fun a b => guard (size s == b) >> f a)).
rewrite eqxx guardT.
by under [in RHS]eq_bind do rewrite bindskipf.
Qed.

Lemma arbitrary_perm (A : eqType) def (a b : seq A) : perm_eq a b ->
  arbitrary def a = arbitrary def b :> M _.
Proof.
elim: a def b => [def b| h [|t1 t2] ih def b htb].
  by move/perm_size/esym/size0nil ->.
- destruct b as [|b1 b2].
    by have := perm_size htb.
  destruct b2 as [|b2 b3]; last first.
    by have := perm_size htb.
  move/perm_consP : htb => [i [s [ihb1s /perm_size/size0nil s0]]].
  move: ihb1s; rewrite s0 /=.
  destruct i => /=.
    by rewrite rot0 => -[->].
  by rewrite /rot /= => -[->].
- have [b1 [b2 Hb]] : exists b1 b2, b = rcons b1 h ++ b2.
    have hb : h \in b.
      move/perm_mem : htb => /(_ h).
      by rewrite mem_head.
    exact: mem_rcons_cat.
  rewrite Hb arbitrary_cons //.
  rewrite (ih _ (b1 ++ b2)); last first.
    move: htb.
    rewrite Hb -cats1 -catA perm_sym (perm_catCA b1 [:: h] b2).
    by rewrite perm_cons perm_sym.
  destruct b2 as [|b2 b3].
    rewrite 2!cats0.
    rewrite cats0 in Hb.
    destruct b1 as [|b1 b11].
      move: htb.
      rewrite Hb.
      by move/perm_size.
    by rewrite -cats1 arbitrary_cat// arbitrary1 altC.
  rewrite [in RHS]arbitrary_cat ?size_rcons//.
  destruct b1 as [|b1 b11] => //.
  rewrite arbitrary_cat//.
  rewrite altA.
  congr (_ [~] _).
  by rewrite -cats1 arbitrary_cat// arbitrary1 altC.
Qed.

Lemma arbitrary_flatten A def (s : seq A) (f : A -> A) : (0 < size s)%nat ->
  (do x <- arbitrary def s; Ret (f x))%Do =
  arbitrary def (flatten [seq [:: f y] | y <- s]) :> M _.
Proof.
elim: s f => // a [_ f _ /=|h t ih f _].
  by rewrite /arbitrary /= bindretf.
rewrite [h :: t]lock /= -lock.
rewrite [in RHS]arbitrary_cons// -ih//.
by rewrite arbitrary_cons// alt_bindDl bindretf.
Qed.

(* NB: not used *)
Lemma arbitrary_flatten2 A def (s : seq A) (f g : A -> A) : (0 < size s)%nat ->
  (do x <- arbitrary def s; Ret (f x) [~] Ret (g x))%Do =
  arbitrary def (flatten [seq [:: f y; g y] | y <- s]) :> M _.
Proof.
elim: s def f g => //.
move=> h [|t1 t2] ih def f g _.
  by rewrite /= arbitrary1 bindretf arbitrary_cons //.
rewrite [t1 :: t2]lock /= -lock.
rewrite [in RHS]arbitrary_cons//.
rewrite [in RHS]arbitrary_cons//.
rewrite -ih//.
rewrite arbitrary_cons//.
by rewrite alt_bindDl bindretf altA.
Qed.

(* NB: not used *)
Lemma bind_ext_splits A (s : seq E) (f : seq E -> seq E -> M A) (m : seq E -> M A) :
  (forall ys zs, subseq ys s -> subseq zs s -> perm_eq (ys ++ zs) s -> f ys zs = m s) ->
  (do x <- splits s; (let '(ys, zs) := x in f ys zs))%Do = m s.
Proof.
move=> h.
transitivity ((do x <- splits s; (let '(ys, zs) := x in m s))%Do).
  rewrite splits_preserves_subseq !bindA.
  bind_ext => -[a b] /=.
  rewrite !bindA.
  apply: bind_ext_guard => /and3P[sa sb abs].
  rewrite !bindretf.
  by rewrite h.
clear h f.
transitivity (splits s >> m s).
  by bind_ext => -[].
(* TODO splits inde *)
elim: s m => /= [m|].
  by rewrite bindretf.
move=> h t ih m.
rewrite bindA.
under eq_bind do rewrite alt_bindDl.
rewrite alt_bindDr.
under eq_bind do rewrite bindretf.
under [in X in _[~]X]eq_bind do rewrite bindretf.
by rewrite (ih (fun s => m (h :: s))) altmm.
Qed.

Lemma gt0_flatten A (s : seq A) (f : A -> A) : (0 < size s)%nat ->
  (0 < size (flatten [seq [:: f y] | y <- s]))%nat.
Proof. by case: s. Qed.

Lemma perm_eq_flatten_map (A : eqType) (s : seq A) (f g : A -> A) :
  perm_eq (flatten [seq [:: f y; g y] | y <- s])
          (flatten [seq [:: f y] | y <- s] ++ flatten [seq [:: g y] | y <- s]).
Proof.
elim: s f g => // h t ih f g.
rewrite /=.
rewrite -[in X in perm_eq _ X](cat1s (f h)).
rewrite -[in X in perm_eq _ X](cat1s (g h)).
rewrite catA.
apply: (@perm_trans _ (([:: f h] ++ [:: g h]) ++ flatten [seq [:: f y] | y <- t] ++ flatten [seq [:: g y] | y <- t])); last first.
  rewrite perm_catACA.
  exact: perm_refl.
rewrite -(cat1s (f h)).
rewrite -(cat1s (g h)).
rewrite catA.
by apply perm_cat => //.
Qed.

Lemma nondetPlus_sub_insert A (s : seq A) a : nondetPlus_sub (@insert M _ a s).
Proof.
elim: s => /= [|h t ih]; first by exists (ndRet [:: a]).
rewrite insertE /=.
have [syn synE] := ih.
exists (ndAlt (ndRet [:: a, h & t]) (ndBind syn (fun x => ndRet (h :: x)))) => /=.
by rewrite synE fmapE.
Qed.

Lemma nondetPlus_sub_perm A (s : seq A) : nondetPlus_sub (@perm M _ s).
Proof.
elim: s => /=.
Abort.

Lemma insertC A a b (s : seq A) : (do x <- insert b s; insert a x)%Do =
                                  (do x <- insert a s; insert b x)%Do :> M _.
Proof.
have [n ns] := ubnP (size s); elim: n s ns a b => // n ih s ns a b.
case: s ns => [|h t] ns.
  by rewrite !insertE !bindretf !insertE altC !fmapE !bindretf.
rewrite ltnS /= in ns.
rewrite (insertE _ _ (h :: t)) alt_bindDl bindretf.
rewrite (insertE _ _ [:: b, h & t]) [in LHS](insertE _ _ (h :: t)).
rewrite [in RHS](insertE _ _ (h :: t)) [in RHS]alt_bindDl bindretf.
rewrite 2![in RHS]insertE.
rewrite [in LHS]alt_fmapDr ![in LHS]altA [in LHS](altC (Ret [:: a, b, h & t])).
rewrite -!altA; congr (_ [~] _); first by rewrite fmapE bindretf.
rewrite alt_fmapDr -!altA; congr (_ [~] _); first by rewrite fmapE bindretf.
rewrite [in LHS]altC bind_fmap /= [in LHS]/comp /=.
under eq_bind do rewrite insertE.
rewrite alt_bindDr.
under [in X in (_ [~] X) [~] _]eq_bind do rewrite fmapE.
rewrite -bindA.
rewrite [in LHS]ih //.
rewrite [in RHS]altC bind_fmap /= [in RHS]/comp /=.
under [in RHS]eq_bind do rewrite insertE.
rewrite alt_bindDr [in RHS]altC.
rewrite -!altA; congr (_ [~] _).
  rewrite !fmapE !bindA.
  by under [in RHS]eq_bind do rewrite !bindretf.
rewrite [in RHS]altC; congr (_ [~] _); last first.
  rewrite !fmapE !bindA.
  by under eq_bind do rewrite bindretf.
rewrite bindA.
by under [in RHS]eq_bind do rewrite fmapE.
Qed.

Lemma perm_insert A a b (b1 b2 : seq A) :
  (do x <- perm (b :: b1 ++ b2); insert a x)%Do =
  (do x <- perm (rcons b1 a ++ b2); insert b x)%Do :> M _.
Proof.
elim: b1 a b b2 => [/=|h t ih] a b b2.
  rewrite !bindA.
  by under eq_bind do rewrite insertC.
rewrite [h :: t]lock /= -lock.
rewrite ih /= !bindA.
suff : (do x <- perm (rcons t b ++ b2); do x0 <- insert a x; insert h x0)%Do =
       (do x <- perm (rcons t a ++ b2); do x0 <- insert b x; insert h x0)%Do :> M _.
  under eq_bind do rewrite insertC.
  move=> ->.
  by under eq_bind do rewrite insertC.
rewrite -bindA -ih /= -bindA.
rewrite -[in RHS]ih /= !bindA.
bind_ext => a'.
by rewrite -bindA insertC bindA.
Qed.

Lemma perm_eq_perm (A : eqType) (a b : seq A) : perm_eq a b -> perm a = perm b :> M _.
Proof.
have [n na] := ubnP (size a); elim: n a na b => // n ih a na b.
case: a => [|a1 a2] in na *.
  by move=> /perm_size/esym/size0nil ->.
rewrite /= ltnS in na.
case: b => [/perm_size //|b1 b2 ab].
have [a1b1|a1b1] := eqVneq a1 b1.
  rewrite {}a1b1 in ab *.
  rewrite perm_cons in ab.
  by rewrite /= (ih _ na b2).
have [b21 [b22 Hb]] : exists b21 b22, b2 = rcons b21 a1 ++ b22.
  apply: mem_rcons_cat.
  by move/perm_mem : ab => /(_ a1); rewrite mem_head inE (negbTE a1b1).
have {}ab : perm_eq a2 (b1 :: b21 ++ b22).
  move: ab; rewrite Hb -cats1 -catA -cat_cons perm_sym.
  by rewrite perm_catCA perm_cons perm_sym.
by rewrite /= (ih _ na _ ab) Hb perm_insert.
Qed.

Lemma insert_cat A h (a b : seq A) u :
  insert h (a ++ u :: b) = (do x <- insert h a; Ret (x ++ u :: b))%Do [~]
                          (do x <- insert h b; Ret (a ++ u :: x))%Do :> M _.
Proof.
elim: a h u b => [h u b|a1 a2 ih h u b].
  rewrite /= (insertE _ h nil) bindretf insertE; congr (_ [~] _).
  by rewrite fmapE.
rewrite cat_cons.
rewrite [in LHS]insertE [u :: b]lock /= -lock [in LHS]ih.
rewrite [in RHS]insertE [in RHS]alt_bindDl.
rewrite bindretf -altA; congr (_ [~] _).
rewrite [in RHS]bind_fmap.
rewrite [in LHS]fmapE [in LHS]alt_bindDl.
by rewrite !bindA; congr (_ [~] _); under eq_bind do rewrite bindretf.
Qed.

Lemma perm_cons_splits (A : eqType) (s : seq A) u :
  perm (u :: s) = (do a <- splits s;
                  (let '(ys, zs) := a in liftM2 (fun x y => x ++ u :: y) (perm ys) (perm zs)))%Do :> M _.
Proof.
have [n ns] := ubnP (size s); elim: n s ns => // n ih s ns.
move: s ns => [|h t] ns.
  by rewrite /= bindretf insertE bindretf /= /liftM2 /= !bindretf.
rewrite /= ltnS in ns.
rewrite [in RHS]/=.
rewrite bindA.
under eq_bind do rewrite alt_bindDl.
under eq_bind do rewrite bindretf.
under eq_bind do rewrite bindretf.
transitivity (perm [:: h, u & t] : M _).
  apply perm_eq_perm.
  rewrite -cat1s -(cat1s h).
  by rewrite perm_catCA.
rewrite [u :: t]lock /= -lock.
rewrite ih // bindA.
rewrite splits_preserves_subseq !bindA.
bind_ext => -[a b] /=; rewrite !bindA.
apply: bind_ext_guard => /and3P[ta tb abt].
rewrite !bindretf /liftM2 !bindA /=.
rewrite -alt_bindDr.
bind_ext => a'.
rewrite !bindA.
rewrite (_ : commute (insert h a') (perm b) _) //; last first.
  apply: commute_plus.
  exact: nondetPlus_sub_insert.
rewrite -alt_bindDr.
bind_ext => b'.
by rewrite bindretf /= insert_cat.
Qed.

Lemma perm_qperm (A : eqType) : @perm M A = @qperm M A.
Proof.
rewrite boolp.funeqE => s.
have [n ns] := ubnP (size s); elim: n s ns => // n ih s ns.
move: s ns => [|h t] ns.
  by rewrite qperm_nil.
rewrite /= ltnS in ns.
rewrite qperm_cons.
transitivity (
  (do a <- splits t; (let '(ys, zs) := a in liftM2 (fun x y => x ++ h :: y) (perm ys) (perm zs)))%Do : M _
); last first.
  rewrite splits_preserves_subseq !bindA.
  bind_ext => -[a b] /=; rewrite !bindA.
  apply: bind_ext_guard => /and3P[ta tb abt].
  rewrite !bindretf /liftM2.
  rewrite ih; last first.
    by rewrite (leq_trans _ ns)// ltnS; apply: size_subseq.
  rewrite ih; last first.
    by rewrite (leq_trans _ ns)// ltnS; apply: size_subseq.
  by [].
by rewrite perm_cons_splits.
Qed.

Lemma perm_eq_qperm (A : eqType) (a b : seq A) : perm_eq a b -> qperm a = qperm b :> M _.
Proof. by rewrite -!perm_qperm; exact: perm_eq_perm. Qed.

Lemma qperm_preserves (A : eqType) h (t : seq A) : qperm (h :: t) = qperm (rcons t h) :> M _.
Proof. by apply: perm_eq_qperm; rewrite perm_sym perm_rcons perm_refl. Qed.

(* TODO: move *)
Lemma refinR A (a b : M A): a [~] b `>=` a.
Proof. by rewrite /refin altA altmm. Qed.

Lemma insert_ret A h (t : seq A) : (insert h t : M _) `>=` Ret (h :: t).
Proof.
elim: t h => [h|t1 t2 ih h].
  by rewrite insertE; exact: refin_refl.
by rewrite insertE; exact: refinR.
Qed.

Lemma perm_ret A (xs : seq A) : perm xs `>=` (Ret xs : M _).
Proof.
case: (perm_is_alt_ret M xs).
by move=> m H; rewrite H /refin altA altmm.
Qed.

(* NB: postulate return⊑perm in Agda code *)
Lemma refin_qperm_ret (A : eqType) (s : seq A) : qperm s `>=` (Ret s : M _).
Proof. by rewrite -perm_qperm; exact: perm_ret. Qed.

Lemma qperm_refin_rcons (A : eqType) h (t : seq A) :
  qperm (h :: t) `>=` (Ret (rcons t h) : M _).
Proof. by rewrite qperm_preserves; exact: refin_qperm_ret. Qed.

Lemma qperm_refin_cons (A : eqType) h (t : seq A) :
  qperm (rcons t h) `>=` (Ret (h :: t) : M _).
Proof. by rewrite -qperm_preserves; exact: refin_qperm_ret. Qed.

(* TODO: move to fail_lib.v *)
Lemma perm_insertC x y (s : seq E) :
  (do s' <- perm (rcons s x); insert y s')%Do =
  (do s' <- insert y s; perm (rcons s' x))%Do :> M _.
Proof.
have [n ns] := ubnP (size s); elim: n s ns x y => // n ih.
move=> [/= _ x y|h t].
  by rewrite !bindA !bindretf /= bindA bindretf [in RHS]insertE bindretf.
rewrite ltnS /= => tn x y.
rewrite bindA.
rewrite (_ : perm (rcons t x) = perm (x :: t)); last first.
  apply perm_eq_perm.
  by rewrite perm_rcons.
rewrite /=.
rewrite !bindA.
rewrite [in RHS]insertE alt_bindDl bindretf.
rewrite /=.
rewrite bindA.
rewrite (_ : perm (rcons t x) = perm (x :: t)); last first.
  apply perm_eq_perm.
  by rewrite perm_rcons.
rewrite /= bindA.
rewrite bind_fmap.
rewrite /comp /=.
rewrite -[in X in _ [~]X]bindA.
rewrite -ih//.
rewrite bindA.
rewrite (_ : perm (rcons t x) = perm (x :: t)); last first.
  apply perm_eq_perm.
  by rewrite perm_rcons.
rewrite /= !bindA.
rewrite -alt_bindDr.
bind_ext => s'.
rewrite -alt_bindDr.
bind_ext => t'.
rewrite insertC.
by rewrite altmm//.
Qed.

(* NB: postulate perm-snoc in Agda *)
Lemma perm_rcons (s : seq E) x :
  perm (rcons s x) = perm s >>= (fun s' => perm (rcons s' x)) :> M _.
Proof.
have [n ns] := ubnP (size s); elim: n s ns x => // n ih.
case=> [_ x|h t].
  by rewrite !bindretf -cats1 /= bindretf.
rewrite ltnS /= => tn x.
rewrite ih // !bindA.
rewrite {1 3}perm_qperm.
rewrite bind_qperm_guard.
rewrite [in RHS]bind_qperm_guard.
bind_ext => s'.
apply bind_ext_guard => /eqP ts'.
by rewrite perm_insertC.
Qed.

Lemma qperm_rcons (s : seq E) x :
  qperm (rcons s x) = qperm s >>= (fun s' => qperm (rcons s' x)) :> M _.
Proof. by rewrite -!perm_qperm; exact: perm_rcons. Qed.

Lemma permutations_idem : perm >=> perm = perm :> (seq E -> M _).
Proof.
apply: fun_ext_dep => s.
rewrite kleisliE.
elim: s => [|h t ih].
  by rewrite /= bindretf /=.
rewrite /=.
rewrite bindA.
transitivity ((do x <- perm t; do x <- perm x; insert h x)%Do : M _).
  bind_ext.
  elim/last_ind => [|s x _].
    by rewrite insertE /= !bindretf insertE /= bindretf insertE.
  rewrite perm_insertC.
  rewrite insert_rcons alt_bindDl.
  rewrite bind_fmap /= /comp /=.
  under [in RHS]eq_bind do rewrite perm_rcons.
  rewrite bindretf.
  rewrite (@perm_eq_perm _ _ (h :: rcons s x)); last first.
    rewrite -cats1 -cat1s.
    rewrite catA.
    by rewrite perm_catC.
  rewrite /=.
  rewrite perm_insertC -alt_bindDr.
  bind_ext => s'.
  rewrite altmm.
  by rewrite perm_rcons.
by rewrite -bindA ih.
Qed.

(* NB: postulate perm-idempotent in Agda *)
Lemma qperm_involutive : qperm >=> qperm = qperm :> (seq E -> M (seq E)).
Proof. by rewrite -perm_qperm permutations_idem. Qed.

Lemma qperm_slowsort : (qperm >=> (@slowsort M _ _)) = (@slowsort M _ _) :> (seq E -> M (seq E)).
Proof. by rewrite /slowsort -kleisliA qperm_involutive. Qed.

End ssplits.

Section fsplits.
Variable (d : unit) (E : porderType d) (M : plusArrayMonad E Z_eqType).

Fixpoint fsplits (A : eqType) (s : seq A) : seq (seq A * seq A)%type :=
  if s isn't x :: xs then [:: ([::], [::])] else
  let t := fsplits xs in
  flatten (map (fun y => [:: (x :: y.1, y.2); (y.1, x :: y.2)]) t).

Lemma fsplits_subseq (A : eqType) (s : seq A) x :
  x \in fsplits s -> [/\ subseq x.1 s, subseq x.2 s & perm_eq (x.1 ++ x.2) s].
Proof.
elim: s x => /= [x|h t ih /= x /flattenP[/= l]].
  by rewrite inE => /eqP ->.
move=> /mapP[/= [x1 x2]] /ih[/= x1t x2t x1x2t ->{l}].
rewrite !inE => /orP[|] /eqP -> /=.
- rewrite eqxx; split => //.
    destruct x2 as [|x21 x22] => //.
    case: ifPn => // /eqP ?; subst x21.
    exact: cons_subseq x2t.
  by rewrite perm_cons.
split.
- destruct x1 as [|x11 x12] => //.
  case: ifPn => // /eqP ?; subst x11.
  exact: cons_subseq x1t.
- by rewrite eqxx.
- rewrite -cat_rcons -cats1.
  by rewrite perm_catAC perm_catC perm_cons.
Qed.

Lemma subseq_fsplits (A : eqType) (s : seq A) x :
  [/\ subseq x.1 s, subseq x.2 s & perm_eq (x.1 ++ x.2) s] -> x \in fsplits s.
Proof.
elim: s x => /= [x|h t ih /=].
  move=> [/eqP x10 /eqP x20] _.
  by rewrite (surjective_pairing x) inE x10 x20.
move=> [[|a1 a2] [|b1 b2]] //=.
- by move=> [_ _ ] /perm_size/esym/size0nil.
- move=> [_]; case: ifPn => [/eqP -> b2t|].
  + rewrite perm_cons => tb2; have /={}ih := ih ([::], b2).
    apply/flattenP => /=; exists [:: ([:: h], b2); ([::], h :: b2)].
      by apply/mapP => /=; exists ([::], b2) => //; apply: ih; split => //; exact: sub0seq.
    by rewrite !inE /=.
  + move=> b1h b12t b12ht.
    apply/flattenP => /=; eexists. (* must contain ([::], b1 :: b2) *) (* [:: (h :: x.1, x.2); (x.1, h :: x.2)] for some x *)
      apply/mapP => /=.
Abort.

Lemma fsplits_gt0 (A : eqType) (s : seq A) : (0 < size (fsplits s))%nat.
Proof. by elim: s => // h t ih /=; destruct (fsplits t). Qed.

(* NB: not used *)
Lemma splits_fsplits (s : seq E) : splits s = arbitrary ([::], [::]) (fsplits s) :> M _.
Proof.
elim: s => [|h t ih]; first by rewrite /= arbitrary1.
destruct t as [|t1 t2]; first by rewrite /= bindretf /= /arbitrary /= altC.
rewrite [t1 :: t2]lock /= -lock ih alt_bindDr.
have /(arbitrary_perm M ([::], [::])) -> : perm_eq
  (flatten [seq [:: (h :: y.1, y.2); (y.1, h :: y.2)] | y <- fsplits (t1 :: t2)])
  ((flatten [seq [:: (h :: y.1, y.2)] | y <- fsplits (t1 :: t2)]) ++
   (flatten [seq [:: (y.1, h :: y.2)] | y <- fsplits (t1 :: t2)])).
  by rewrite perm_eq_flatten_map.
rewrite arbitrary_cat; last 2 first.
  by apply: gt0_flatten; exact: fsplits_gt0.
  by apply: gt0_flatten; exact: fsplits_gt0.
by congr (_ [~] _); rewrite arbitrary_flatten //; exact: fsplits_gt0.
Qed.

End fsplits.

Section partl.
Variable (d : unit) (E : porderType d) (M : plusArrayMonad E Z_eqType).

Fixpoint partl (p : E) (s : (seq E * seq E)%type) (xs : seq E)
    : (seq E * seq E)%type :=
  match xs with
  | [::] => s
  | x :: xs => if x <= p then partl p (rcons s.1 x, s.2) xs
                         else partl p (s.1, rcons s.2 x) xs
  end.

(* Require Import Recdef.
Function partl' (p : E) (yzxs : (seq E * seq E * seq E)) {struct yzxs}
    : M (seq E * seq E)%type :=
  match yzxs with
  | (ys, zs, [::]) => Ret (ys, zs)
  | (ys, zs, x :: xs) =>
    if x <= p then (@qperm _ _ zs) >>=
                (fun zs' =>
                  partl' p ((ys ++ [:: x]), zs', xs))
              else (@qperm _ _ (zs ++ [:: x])) >>=
                (fun zs' =>
                  partl' p (ys, zs', xs))
  end. *)

Fixpoint partl' (p : E) (ys zs xs : seq E)
    : M (seq E * seq E)%type :=
  match xs with
  | [::] => Ret (ys, zs)
  | x :: xs =>
    if x <= p then (@qperm _ _ zs) >>=
                (fun zs' =>
                  partl' p (rcons ys x) zs' xs)
              else (@qperm _ _ (rcons zs x)) >>=
                (fun zs' =>
                  partl' p ys zs' xs)
  end.

Lemma nondetPlus_sub_qpartl' p (s : seq E) a b : nondetPlus_sub (partl' p a b s).
Proof.
elim: s p a b => [p a b|h t ih p a b].
  by exists (ndRet (a, b)).
rewrite /=; case: ifPn => hp.
  have [syn synE] := nondetPlus_sub_qperm M b.
  exists (ndBind syn (fun zs' => sval (ih p (rcons a h) zs'))) => /=.
  rewrite synE /=.
  bind_ext => zs' /=.
  by case: ih.
have [syn synE] := nondetPlus_sub_qperm M (rcons b h).
exists (ndBind syn (fun zs' => sval (ih p a zs'))) => /=.
rewrite synE /=.
bind_ext => zs' /=.
by case: ih.
Qed.

Definition dispatch (x p : E) '(ys, zs, xs) : M (seq E * seq E * seq E)%type :=
  if x <= p then qperm zs >>= (fun zs' => Ret (rcons ys x, zs', xs))
            else qperm (rcons zs x) >>= (fun zs' => Ret (ys, zs', xs)).

Lemma partl'_dispatch (p x : E) (ys zs xs : seq E) :
  partl' p ys zs (x :: xs) =
  dispatch x p (ys, zs, xs) >>= uncurry3 (partl' p).
Proof.
  rewrite /dispatch {1}/partl'.
  case: ifPn.
  rewrite bindA.
  move=> _.
  bind_ext.
  move=> s.
  by rewrite bindretf.
  rewrite bindA.
  move=> _.
  bind_ext.
  move=> s.
  by rewrite bindretf.
Qed.

(*
Fixpoint ipartl (p : E) (i : Z) (ny nz : nat) (nx : nat) : M (nat * nat)%type :=
  match nx with
  | 0 => Ret (ny, nz)
  | k.+1 => aget ((* i + *) (ny + nz)%:Z) >>= (fun x => (* TODO *)
         if x <= p then swap (i + ny%:Z) (i + ny%:Z + nz%:Z) >> ipartl p i (ny + 1) nz k
                   else ipartl p i ny (nz.+1) k)
  end.

(* Program Fixpoint iqsort (i : Z) (n : nat) : M unit :=
  match n with
  | 0 => Ret tt
  | n.+1 => aget i >>= (fun p =>
         ipartl p (i) 0 0 n >>= (fun '(ny, nz) =>
         swap i (i + ny%:Z) >>
         iqsort i ny >> iqsort (ny%:Z) nz))
  end. *)

(* Lemma lemma12 {i : Z} {xs : seq E} {p : E} :
  writeList i xs >> iqsort i (size xs) `<=` _.
Proof. *)

(* Lemma lemma13 {i : Z} {ys : seq E} {p : E} :
  perm ys >>= (fun ys' => writeList i (ys' ++ [:: p])) `>=`
  writeList i (p :: ys) >> swap i (i + (size ys)%:Z).
Proof. *)

(* Qed. *)

*)

Fixpoint ipartl (p : E) (i : Z) (ny nz : nat) (nx : nat) : M (nat * nat)%type :=
  match nx with
  | 0 => Ret (ny, nz)
  | k.+1 => aget (i + (ny + nz)%:Z)%Z >>= (fun x => (* TODO *)
           if x <= p then
             swap (i + ny%:Z) (i + ny%:Z + nz%:Z) >> ipartl p i ny.+1 nz k
           else
             ipartl p i ny nz.+1 k)
  end.

Lemma ipartl_guard (p : E) (i : Z) ny nz (nx : nat) :
  ipartl p i ny nz nx =
    ipartl p i ny nz nx >>= (fun '(a, b) => (guard ((a <= nx + ny + nz)&&(b <= nx + ny + nz))%nat >> Ret (a, b))) :> M _.
Proof.
elim: nx ny nz => [ny nz|].
  rewrite /= bindretf.
  by rewrite add0n leq_addr leq_addl guardT bindskipf.
move=> n ih ny nz.
rewrite /=.
rewrite !bindA; bind_ext => p1.
case: ifPn => p1p.
  rewrite bindA; bind_ext => P2.
  rewrite bindA; bind_ext => -[].
  rewrite ih.
  rewrite bindA; bind_ext => -[a b] /=.
  rewrite bindA.
  apply: bind_ext_guard => abnk.
  rewrite bindretf.
  by rewrite addSn -addnS abnk guardT bindskipf.
rewrite ih.
rewrite bindA; bind_ext => -[a b] /=.
rewrite bindA.
apply: bind_ext_guard => abnk.
rewrite bindretf.
by rewrite addSnnS addnS addSnnS abnk guardT bindskipf.
Qed.

Definition dipartl (p : E) (i : Z) (y z x : nat) :
  M {n | (fun n => ((n.1 <= x + y + z) && (n.2 <= x + y + z))%nat) n} :=
  ipartl p i y z x >>=
    (dassert (fun n => ((n.1 <= x + y + z) && (n.2 <= x + y + z))%nat)).

Local Open Scope mprog.
Lemma ipartlE (p : E) (i : Z) (n : nat) :
  ipartl p i 0 0 n = fmap (fun x => ((sval x).1, (sval x).2)) (dipartl p i 0 0 n).
Proof.
rewrite fmapE /= /dipartl !bindA.
rewrite ipartl_guard !bindA.
bind_ext => -[a b] /=.
rewrite bindA.
apply: bind_ext_guard => /andP[na nb].
rewrite bindretf /= /dassert /=.
case: Bool.bool_dec => [nanb|].
  by rewrite bindretf.
by rewrite na nb.
Qed.
Local Close Scope mprog.

Lemma write2L_write3L {i : Z} {p : E} {ys zs xs : seq E} :
  (forall ys zs : seq E, (do x <- partl' p ys zs xs; write2L i x)%Do
  `>=` writeList i (ys ++ zs ++ xs) >>
      ipartl p i (size ys) (size zs) (size xs)) ->
  uncurry3 (partl' p) (ys, zs, xs) >>= write2L i
  `>=` write3L i (ys, zs, xs) >>= uncurry3 (ipartl p i).
Proof.
  move=> h.
  rewrite /uncurry3 /write3L.
  apply: refin_trans (h ys zs).
  rewrite bindA bindretf.
  apply refin_refl.
Qed.

Lemma dispatch_write2L_write3L {i : Z} {x p : E} {ys zs xs : seq E} :
  (forall ys zs : seq E, (do x <- partl' p ys zs xs; write2L i x)%Do
  `>=` writeList i (ys ++ zs ++ xs) >>
      ipartl p i (size ys) (size zs) (size xs)) ->
  dispatch x p (ys, zs, xs) >>= uncurry3 (partl' p) >>= write2L i
  `>=` dispatch x p (ys, zs, xs) >>= write3L i >>= uncurry3 (ipartl p i).
Proof.
move=> h.
rewrite 2!bindA.
rewrite /dispatch.
case: ifPn => xp.
  rewrite 2!bindA /refin.
  rewrite refin_bindl => //.
  move=> {}zs.
  rewrite 2!bindretf.
  exact: write2L_write3L h.
(* same *)
rewrite 2!bindA /refin.
rewrite refin_bindl => //.
move=> {}zs.
rewrite 2!bindretf.
exact: write2L_write3L h.
Qed.

Lemma dispatch_writeList_cat {i : Z} {x p : E} {ys zs xs : seq E} :
  dispatch x p (ys, zs, xs) >>= write3L i >>= uncurry3 (ipartl p i) =
  dispatch x p (ys, zs, xs) >>= (fun '(ys', zs', xs) =>
    writeList i (ys' ++ zs') >> writeList (i + (size (ys' ++ zs'))%:Z) xs >>
    ipartl p i (size ys') (size zs') (size xs)).
Proof.
  rewrite bindA.
  bind_ext => [[[ys' zs']] xs'].
  by rewrite /write3L bindA catA writeList_cat bindretf.
Qed.

Lemma commute_writeList_dispatch i p ys zs xs x :
  commute (dispatch x p (ys, zs, xs))
          (writeList (i + (size ys)%:Z + (size zs)%:Z + 1) xs)
          (fun pat _ => let: (ys', zs', xs0) := pat in
            writeList i (ys' ++ zs') >> ipartl p i (size ys') (size zs') (size xs0)).
Proof.
apply commute_plus.
rewrite /dispatch.
case: ifPn => xp.
  have [syn syn_qperm] := nondetPlus_sub_qperm M zs.
  exists (ndBind(*NB: is ndBind a good name?*) syn (fun s => ndRet (rcons ys x, s, xs))).
  by rewrite /= syn_qperm.
have [syn syn_qperm] := nondetPlus_sub_qperm M (rcons zs x).
exists (ndBind syn (fun s => ndRet (ys, s, xs))).
by rewrite /= syn_qperm.
Qed.

Definition snd3 {A B C D} (f : B -> M D) (xyz : A * B * C) : M (A * D * C)%type :=
  f xyz.1.2 >>= (fun y' => Ret (xyz.1.1, y', xyz.2)).

(* NB: this really comes from Mu's code *)
Lemma go a b p xs : (snd3 qperm >=> (fun x => partl' p x.1.1 x.1.2 x.2)) (a, b, xs) `<=` second qperm (partl p (a, b) xs).
Proof.
elim: xs p a b => [/=|h t ih] p a b.
  rewrite /second /=.
  rewrite (_ : (do y' <- qperm b; Ret (a, y'))%Do = (do y' <- qperm b; Ret (a, y', [::]) >>= (fun x => partl' p x.1.1 x.1.2 x.2))%Do); last first.
    by under [in RHS]eq_bind do rewrite bindretf /=.
  rewrite -bindA.
  rewrite /snd3 /= kleisliE /=.
  exact: refin_refl.
rewrite /=.
rewrite -if_arg.
rewrite -fun_if.
rewrite (_ : (if _ then _ else _) =
             (if h <= p then rcons a h else a, if h <= p then b else rcons b h)); last first.
  by case: ifPn.
apply: refin_trans; last first.
  exact: ih.
set lhs := (X in X `>=` _).
set rhs := (X in _ `>=` X).
suff : lhs = rhs by move=> ->; exact: refin_refl.
rewrite {}/lhs {}/rhs.
rewrite (_ : (_, _, t) =
              (if h <= p then (rcons a h, b, t) else (a, rcons b h, t))); last first.
  by case: ifPn.
rewrite fun_if.
rewrite 2![in LHS]kleisliE.
have -> : snd3 qperm (rcons a h, b, t) = qperm b >>= (fun zs' => snd3 qperm (rcons a h, zs', t)).
  by rewrite {1}/snd3 /= -{1}qperm_involutive kleisliE bindA.
have -> : snd3 qperm (a, rcons b h, t) = qperm b >>= (fun zs' => snd3 qperm (a, rcons zs' h, t)).
  rewrite {1}/snd3 /= qperm_rcons bindA.
  by under eq_bind do rewrite -cats1.
rewrite !bindA -bind_if.
transitivity ((do x <- qperm b; (if h <= p
    then snd3 qperm (rcons a h, x, t)
    else snd3 qperm (a, rcons x h, t)) >>= (fun x0 => partl' p x0.1.1 x0.1.2 x0.2)))%Do.
  by bind_ext => xs; case: ifPn.
transitivity (
  (do x <- qperm b;
   if h <= p then snd3 qperm (rcons a h, x, t) >>= uncurry3 (partl' p) else
                 snd3 qperm (a, rcons x h, t) >>= uncurry3 (partl' p))%Do
).
  bind_ext => xs; case: ifPn => hp; (rewrite /uncurry3 /=;
    rewrite !bindA;
    under eq_bind do rewrite !bindretf /=;
    by under [in RHS]eq_bind do rewrite !bindretf /=).
under eq_bind do rewrite !bindA /=.
transitivity (do x0 <- qperm b; partl' p a x0 (h :: t))%Do.
  bind_ext => x0.
  rewrite /=.
  case: ifPn => hp.
    by under eq_bind do rewrite bindretf.
  by under eq_bind do rewrite bindretf.
rewrite kleisliE.
rewrite /snd3.
rewrite bindA.
by under [RHS]eq_bind do rewrite bindretf.
Qed.

End partl.
Arguments ipartl {d E M}.
Arguments dipartl {d E M}.
Arguments partl' {d E M}.
Arguments dispatch {d E M}.

Section iqsort.
Variable (d : unit) (E : porderType d) (M : plusArrayMonad E Z_eqType).

(*Function iqsort (i : Z) (n : nat) {measure n} : M unit :=
  match n with
  | 0 => Ret tt
  | k.+1 => aget i >>= (fun p =>
            ipartl p (i + 1) 0 0 (n-1) >>= (fun '(ny, nz) => swap i (i + ny%:Z) >> iqsort i ny))
  end.*)

Local Obligation Tactic := idtac.

Program Fixpoint iqsort' (ni : (Z * nat))
    (f : forall (n'j : (Z * nat)), (n'j.2 < ni.2)%coq_nat -> M unit) : M unit :=
  match ni.2 with
  | 0 => Ret tt
  | n.+1 =>
(*aget ni.1 >>= (fun p =>
            @ipartl p (ni.1 + 1)%Z 0 0 n >>= (fun '(ny, nz) =>
              swap ni.1 (ni.1 + ny%:Z) >>
              f (ni.1, ny) _ >> f ((ni.1 + ny%:Z + 1)%Z, nz) _))*)
aget ni.1 >>= (fun p =>
            dipartl p (ni.1 + 1)%Z 0 0 n >>= (fun nynz =>
              let ny := (sval nynz).1 in
              let nz := (sval nynz).2 in
              swap ni.1 (ni.1 + ny%:Z) >>
              f (ni.1, ny) _ >> f ((ni.1 + ny%:Z + 1)%Z, nz) _))
  end.
Next Obligation.
(*move => [i [//|n']] /= _ n [<-] p [a b] /= a' _ [-> _] _.*)
move => [i [//|n']] /= _ n [<-] p [[a b] /=] /andP[an _] _.
apply/ssrnat.ltP; rewrite ltnS.
by rewrite 2!addn0 in an.
Qed.
Next Obligation.
move => [i [//|n']] /= _ n [<-] p [[a b] /=] /andP[_ bn] _.
apply/ssrnat.ltP; rewrite ltnS.
by rewrite 2!addn0 in bn.
Qed.

Lemma well_founded_lt2 : well_founded (fun x y : (Z * nat) => (x.2 < y.2)%coq_nat).
Proof.
by apply: (@well_founded_lt_compat _ _) => -[x1 x2] [y1 y2]; exact.
Qed.

Definition iqsort : (Z * nat) -> M unit :=
  Fix well_founded_lt2 (fun _ => M unit) iqsort'.

Lemma iqsort'_Fix (ni : (Z * nat))
  (f g : forall (n'j : (Z * nat)), (n'j.2 < ni.2)%coq_nat -> M unit) :
  (forall (n'j : (Z * nat)) (p : (n'j.2 < ni.2)%coq_nat), f n'j p = g n'j p) ->
  iqsort' f = iqsort' g.
Proof.
  by move=> ?; congr iqsort'; apply fun_ext_dep => ?; rewrite boolp.funeqE.
Qed.

Lemma iqsort_nil {i : Z} : iqsort (i, 0) = Ret tt.
Proof. by rewrite /iqsort Fix_eq //; exact: iqsort'_Fix. Qed.

Lemma iqsort_cons {i : Z} {n : nat}: iqsort (i, n.+1) = aget i >>= (fun p =>
dipartl p (i + 1)%Z 0 0 n
  >>= (fun nynz =>
  let ny := (sval nynz).1 in
  let nz := (sval nynz).2 in
  swap i (i + ny%:Z) >>
  iqsort (i, ny) >> iqsort ((i + ny%:Z + 1)%Z, nz))).
Proof. rewrite [in LHS]/iqsort Fix_eq //=; exact: iqsort'_Fix. Qed.

(* page 11 step 4 *)
(* TODO: rename *)
Lemma qperm_preserves_length (i : Z) (x p : E) (ys zs xs : seq E) :
  dispatch x p (ys, zs, xs) >>= (fun '(ys', zs', xs) =>
    writeList i (ys' ++ zs') >> writeList (i + (size (ys' ++ zs'))%:Z) xs >>
    ipartl p i (size ys') (size zs') (size xs)) =
  writeList (i + (size ys)%:Z + (size zs)%:Z + 1) xs >>
    dispatch x p (ys, zs, xs) >>= (fun '(ys', zs', xs) =>
    writeList i (ys' ++ zs') >> ipartl p i (size ys') (size zs') (size xs)) :> M _.
Proof.
rewrite [in RHS]bindA.
rewrite -commute_writeList_dispatch.
rewrite /dispatch.
(* TODO: simplify this *)
case: ifPn => xp.
  rewrite !bindA.
  under eq_bind do rewrite bindretf.
  under [in RHS]eq_bind do rewrite bindretf.
  under eq_bind do rewrite -writeList_cat.
  under [in RHS]eq_bind do rewrite -bindA.
  under [in RHS]eq_bind do rewrite -2!addZA.
  rewrite [RHS](qperm_preserves_size2 zs (fun a b =>
    (writeList (i + ((size ys)%:Z + (b%:Z + 1))) xs >>
    writeList i ((rcons ys x) ++ a)) >>
    ipartl p i (size (rcons ys x)) (size a) (size xs))).
  bind_ext => zs' /=.
  rewrite (_ : (_ + (_ + 1))%Z = (size (ys ++ x :: zs'))%:Z); last first.
    by rewrite size_cat /= intRD natZS -add1Z (addZC 1%Z).
  rewrite -writeList_writeListC; last first.
    by rewrite -cats1 -catA; exact: leZZ.
  by rewrite writeList_cat -cats1 -catA.
rewrite !bindA.
under eq_bind do rewrite bindretf.
under [in RHS]eq_bind do rewrite bindretf.
under eq_bind do rewrite -writeList_cat.
under [in RHS]eq_bind do rewrite -bindA.
under [in RHS]eq_bind do rewrite -2!addZA.
rewrite -Z_S -(size_rcons zs x).
rewrite [RHS](qperm_preserves_size2 (rcons zs x) (fun a b =>
  (writeList (i + ((size ys)%:Z + b%:Z)) xs >>
  writeList i (ys ++ a)) >> ipartl p i (size ys) (size a) (size xs))).
bind_ext => zs' /=.
rewrite (_ : (_ + (_ + _))%Z = (i + (size (ys ++ zs'))%:Z)%Z); last first.
  by rewrite size_cat /= intRD.
by rewrite -writeList_writeListC ?writeList_cat//; exact: leZZ.
Qed.

(* page11 top derivation *)
Lemma partl'_writeList (p x : E) (ys zs xs : seq E) (i : Z) :
  (forall ys zs : seq E, (do x <- partl' p ys zs xs; write2L i x)%Do
    `>=` @writeList _ _ M i (ys ++ zs ++ xs) >>
        ipartl p i (size ys) (size zs) (size xs)) ->
  partl' p ys zs (x :: xs) >>= write2L i `>=`
  @writeList _ _ M (i + (size ys)%:Z + (size zs)%:Z + 1)%Z xs >>
    if x <= p then qperm zs >>= (fun zs' => writeList i (ys ++ x :: zs') >>
      ipartl p i (size ys + 1) (size zs') (size xs))
    else qperm (rcons zs x) >>= (fun zs' => writeList i (ys ++ zs') >>
      ipartl p i (size ys) (size zs') (size xs)).
Proof.
move=> h; rewrite partl'_dispatch.
apply: refin_trans; last exact: (dispatch_write2L_write3L h).
rewrite dispatch_writeList_cat.
rewrite qperm_preserves_length.
rewrite /dispatch bindA.
apply refin_bindl => -[].
case: ifPn => xp. (* TODO:  *)
- rewrite bindA /refin -alt_bindDr.
  bind_ext => s.
  by rewrite bindretf size_rcons addn1 -cat1s catA cats1 altmm.
- rewrite bindA /refin -alt_bindDr.
  bind_ext => s.
  by rewrite bindretf altmm.
Qed.

(* equation11 *)
Lemma introduce_swap_cons {i : Z} {x : E} (zs : seq E) :
  qperm zs >>= (fun zs' => writeList i (x :: zs')) `>=`
  @writeList _ _ M i (rcons zs x) >> swap i (i + (size zs)%:Z).
Proof.
case: zs i => [/= i|].
rewrite qperm_nil bindmskip bindretf addZ0 swapii bindmskip.
by apply: refin_refl.
move=> h t /= i.
rewrite bindA writeList_rcons.
rewrite -aput_writeList_rcons.
apply: refin_trans; last exact: (refin_bindr _ (qperm_refin_rcons _ _ _)).
by rewrite bindretf; exact: refin_refl.
Qed.

(* See postulate introduce-swap equation13 *)
Lemma introduce_swap_rcons {i : Z} {x : E} (ys : seq E) :
  qperm ys >>= (fun ys' => writeList i (rcons ys' x)) `>=`
  @writeList _ _ M i (x :: ys) >> swap i (i + (size ys)%:Z).
Proof.
elim/last_ind: ys i => [/= i|].
rewrite qperm_nil bindmskip bindretf addZ0 swapii /= bindmskip.
by apply: refin_refl.
move=> t h ih i.
rewrite /= bindA.
apply: refin_trans; last exact: (refin_bindr _ (qperm_refin_cons _ _ _)).
rewrite bindretf -bindA.
rewrite -aput_writeList_cons.
exact: refin_refl.
Qed.

Section lemma10.

(* bottom of the page 11, used in the proof of lemma 10 *)
Lemma first_branch (i : Z) (x : E) (ys zs : seq E) :
  qperm zs >>= (fun zs' => writeList i (ys ++ x :: zs')) `>=`
  @writeList _ _ M i (rcons (ys ++ zs) x) >> swap (i + (size ys)%:Z) (i + (size ys)%:Z + (size zs)%:Z).
Proof.
apply: refin_trans; last first.
  apply: refin_bindl => x0.
  rewrite writeList_cat.
  exact: refin_refl.
have -> : commute (qperm zs) (writeList i ys) (fun s _ => @writeList _ _ M (i + (size ys)%:Z) (x :: s)).
  by apply: commute_plus; exact: nondetPlus_sub_qperm.
apply: (@refin_trans _ _
  (writeList i ys >> writeList (i + (size ys)%:Z) (rcons zs x) >>
    swap (i + (size ys)%:Z) (i + (size ys)%:Z + (size zs)%:Z))); last first.
  rewrite !bindA.
  rewrite /refin -alt_bindDr.
  bind_ext => ?.
  by rewrite introduce_swap_cons.
by rewrite rcons_cat writeList_cat; exact: refin_refl.
Qed.

(* page 12, used in the proof of lemma 10 *)
Lemma writeList_ipartl (p x : E) (i : Z) (ys zs xs : seq E) :
  writeList (i + (size ys + size zs)%:Z + 1) xs >>
  (if x <= p
    then writeList i (rcons (ys ++ zs) x) >>
      swap (i + (size ys)%:Z) (i + (size ys + size zs)%:Z) >>
      ipartl p i (size ys + 1) (size zs) (size xs)
    else writeList i (rcons (ys ++ zs) x) >>
      ipartl p i (size ys) (size zs + 1) (size xs)) =
  writeList i (ys ++ zs ++ (x :: xs)) >>
    aget (i + (size ys + size zs)%:Z)%Z >>= (fun x =>
    (if x <= p
      then swap (i + (size ys)%:Z) (i + (size ys + size zs)%:Z) >>
        ipartl p i (size ys + 1) (size zs) (size xs)
      else ipartl p i (size ys) (size zs + 1) (size xs))) :> M _.
Proof.
transitivity (writeList i (ys ++ zs ++ (x :: xs)) >>
   if x <= p then
     swap (i + (size ys)%:Z) (i + (size ys + size zs)%:Z) >>
     ipartl p i (size ys + 1) (size zs) (size xs)
    else ipartl p i (size ys) (size zs + 1) (size xs) : M _).
  case: ifPn => xp.
  - rewrite catA -cat1s catA writeList_cat.
    rewrite [in RHS]writeList_writeListC; last exact: leZZ.
    rewrite {1}size_cat /= {1}[in RHS]intRD size_cat addZA [in RHS]bindA.
    bind_ext => -[].
    by rewrite cats1 bindA; bind_ext.
  - rewrite -[in RHS]cat1s 2!catA writeList_cat.
    rewrite writeList_writeListC; last exact: leZZ.
    by rewrite {1}size_cat [in RHS]intRD size_cat addZA bindA cats1.
rewrite bindA catA writeList_cat 2!bindA.
rewrite size_cat intRD addZA.
bind_ext => ?.
transitivity (
  writeList (i + (size ys)%:Z + (size zs)%:Z)%Z (x :: xs) >> Ret x >>
  (if x <= p then
    swap (i + (size ys)%:Z) (i + (size ys)%:Z + (size zs)%:Z) >>
    ipartl p i (size ys + 1) (size zs) (size xs)
   else ipartl p i (size ys) (size zs + 1) (size xs)) : M _
).
  by rewrite bindA bindretf.
rewrite (introduce_read_sub x xs (fun x0 => (
   if x0 <= p
     then swap (i + (size ys)%:Z) (i + (size ys)%:Z + (size zs)%:Z) >>
       ipartl p i (size ys + 1) (size zs) (size xs)
     else ipartl p i (size ys) (size zs + 1) (size xs)))).
by rewrite bindA.
Qed.

(* eqn 10, page 10, specification of ipartl *)
(*Lemma lemma10 (p : E) (i : Z) (ys zs xs : seq E) :
  writeList i (ys ++ zs ++ xs) >> ipartl p i (size ys) (size zs) (size xs) `<=`
  partl' p ys zs xs >>= write2L i.
Proof.
  elim: xs ys zs => [|h t ih] ys zs.
  rewrite /= catA cats0 bindretf /=; exact: refin_refl.
  apply: refin_trans; last first.
  apply: (partl'_writeList _ _ _ ih).
  case: ifPn => hp.
  (* rewrite -writeList_writeListC. *)
Admitted.

Lemma qperm_involutive : (qperm >=> qperm) = qperm :> (seq E -> M (seq E)).
elim: xs ys zs => [|h t ih] ys zs.
  by rewrite /= catA cats0 bindretf /=; exact: refin_refl.
apply: refin_trans; last first.
  by apply: (partl'_writeList _ _ _ ih).
case: ifPn => hp.
Abort.*)

(* specification of ipartl, eqn 10 page 10?  *)
Lemma lemma10 (p : E) (i : Z) (xs zs ys : seq E) :
  (do pat <- @partl' _ _ M p ys zs xs; (let '(ys, zs) := pat in write2L i (ys, zs)))%Do
  `>=` (do x <- write3L i (ys, zs, xs); uncurry3 (ipartl p i) x)%Do.
Proof.
elim: xs i p zs ys => [|h t ih] i p zs ys.
  rewrite /= bindretf cats0.
  set lhs := (X in X `>=` _); set rhs := (X in _ `>=` X).
  suff : lhs = rhs by move=> ->; exact: refin_refl.
  rewrite /lhs /rhs.
  by rewrite bindA bindretf.
have Htmp : (forall ys0 zs0,
    (do x <- partl' p ys0 zs0 t; write2L i x)%Do `>=`
    @writeList _ _ M i (ys0 ++ zs0 ++ t) >> ipartl p i (size ys0) (size zs0) (size t)).
  move=> {}ys {}zs.
  apply: refin_trans; last exact: (ih i p).
  rewrite /write3L.
  rewrite bindA.
  rewrite bindretf.
  rewrite /uncurry3.
  exact: refin_refl.
have := @partl'_writeList p h ys zs t i Htmp.
apply: refin_trans.
apply: (@refin_trans _ _ (
  writeList (i + (size ys)%:Z + (size zs)%:Z + 1) t >>
  (if h <= p
   then writeList i (rcons (ys ++ zs) h) >>
        swap (i + (size ys)%:Z) (i + (size ys)%:Z + (size zs)%:Z) >>
        ipartl p i (size ys + 1) (size zs) (size t)
   else writeList i (rcons (ys ++ zs) h) >>
        ipartl p i (size ys) (size zs + 1) (size t) ))); last first.
  case: ifPn => hp; last first.
    apply: (@refin_trans _ _
        (writeList (i + (size ys)%:Z + (size zs)%:Z + 1) t >>
         do zs' <- Ret (rcons zs h);
         writeList i (ys ++ zs') >> ipartl p i (size ys) (size zs') (size t))%Do); last first.
      apply: refin_bindl => -[].
      apply: refin_bindr.
      exact: refin_qperm_ret.
    apply: refin_bindl => -[].
    rewrite bindretf size_rcons addn1 rcons_cat.
    exact: refin_refl.
  apply: refin_bindl => -[].
  rewrite -[X in X `>=` _](qperm_preserves_size2 zs (fun a b =>
    writeList i (ys ++ h :: a) >>
   ipartl p i (size ys + 1) b (size t))).
  rewrite -[in X in X `>=` _]bindA.
  apply: refin_bindr.
  exact: first_branch.
rewrite -2!addZA !(addZA (size ys)%:Z) -intRD addZA.
rewrite -[in X in _ >> X]addZA -intRD writeList_ipartl.
rewrite /write3L.
rewrite bindA.
under eq_bind do rewrite bindretf.
rewrite /uncurry3 /=.
rewrite bindA -addZA -intRD.
rewrite (addn1 (size ys)).
rewrite (addn1 (size zs)).
exact: refin_refl.
Qed.

End lemma10.

(* Lemma ipartlspec (i : Z) (p : E) ys zs xs :
  (*write3L i >=> ipartl p i `<=` partl' p >=> write2L i.*)
  (do x <- write3L i (ys, zs, xs); uncurry3 (ipartl p i) x)%Do `<=`
  uncurry3 (partl' p) (ys, zs, xs) >>= (fun '(ys, zs) => write2L i (ys, zs)).
Proof. Abort. *)

(* not used 2021-09-24 :first equation on page10 *)
(* Lemma ipartl_spec (i : Z) (p : E) (ys zs xs : seq E)
    (ipartl : E -> Z -> (nat * nat * nat)%type -> M (nat * nat)%type) :
  writeList i (ys ++ zs ++ xs) >> ipartl p i (size ys, size zs, size xs)
  `<=` second qperm (partl p (ys, zs) xs) >>= write2L i.
Proof. Abort. *)

Lemma partition_partl a b p xs :
  let x := @partition _ E p xs in (a ++ x.1, b ++ x.2) = partl p (a, b) xs.
Proof.
elim: xs p a b => [|h t ih] /= p a b; first by rewrite !cats0.
by case: ifPn => hp; rewrite -ih /= -cats1 /= -catA.
Qed.

(* partl'-spec *)
Lemma partl_partl' a b p xs : second qperm (@partl _ E p (a, b) xs) `>=` (@partl' _ _ M p a b xs)%Do.
Proof.
apply: refin_trans; last first.
  by apply: go.
rewrite kleisliE /snd3 /=.
rewrite bindA.
apply: (@refin_trans M _ (do x <- Ret b; partl' p a x xs)%Do).
  rewrite bindretf.
  exact: refin_refl.
under [in X in X `>=` _]eq_bind do rewrite bindretf /=.
apply: refin_bindr.
exact: refin_qperm_ret.
Qed.

Lemma lemma12 (i : Z) (xs : seq E) : @total E <=%O ->
  writeList i xs >> iqsort (i, size xs) `<=` slowsort xs >>= writeList i.
Proof.
move=> total_E.
have [n nxs] := ubnP (size xs); elim: n xs i => // n ih xs i in nxs *.
move: xs => [|p xs] in nxs *.
 rewrite /= iqsort_nil slowsort_nil.
 (* NB: lemma? *)
 by rewrite /refin 2!bindretf altmm.
set lhs := (X in X `>=` _).
have step1 : lhs `>=` partl' p [::] [::] xs >>= (fun '(ys, zs) =>
     writeList (i + (size ys)%:Z + 1)%Z zs >>
     qperm ys >>= (fun ys' => writeList i (rcons ys' p) >>
       iqsort (i, size ys) >> iqsort ((i + (size ys)%:Z + 1)%Z, size zs))).
     (* l.342 in IQSOrt.agda *)
  rewrite {}/lhs.
  apply: refin_trans; last by apply: refin_bindr;exact: refin_slowsort.
  rewrite bindretf.
  rewrite -qperm_slowsort.
  move Hpxs : (partition p xs) => pxs; case: pxs => [ys zs] in Hpxs *.
  rewrite 2!kleisliE.
  rewrite !bindA.
  rewrite [X in X `>=` _](_ : _ =
    (do zs'' <- qperm zs; do ys'' <- qperm ys;
     do ys' <- slowsort ys''; do zs' <- slowsort zs'';
     writeList i (ys' ++ p :: zs'))%Do); last first.
    have -> : @commute M _ _ (qperm zs) (qperm ys) _ _.
      by move=> T f; apply: commute_plus; exact: nondetPlus_sub_qperm.
    bind_ext => ys''.
    rewrite !bindA.
    under eq_bind do rewrite !bindA.
    have <- : @commute M _ _ (qperm zs) (slowsort ys'') _ _.
      by move=> T f; apply: commute_plus; exact: nondetPlus_sub_qperm.
    bind_ext => zs''.
    under eq_bind do rewrite bindA.
    bind_ext => ys'.
    bind_ext => zs'.
    by rewrite bindretf.
  move/(congr1 (fun x => x.2)) : (Hpxs) => /= <-.
  have parti_partl : partition p xs = partl p ([::], [::]) xs.
    by rewrite -partition_partl /=; case: partition.
  rewrite parti_partl.
  apply: refin_trans.
    by apply: refin_bindr; apply partl_partl'.
  rewrite /second /=.
  move L : (partl p _ xs) => l.
  case: l L => a' b' L *.
  simpl.
  rewrite bindA.
  move: L; rewrite -parti_partl Hpxs => -[<-{a'} <-{b'}].
  under eq_bind do rewrite bindretf.
  rewrite bind_qperm_guard [in X in _ `>=` X]bind_qperm_guard.
  apply: refin_bindl => zs'.
  apply: bind_refin_guard => /eqP zszs'.
  apply: (@refin_trans _ _ (
    (do ys' <- qperm ys;
        writeList (i + (size ys)%:Z + 1) zs' >>
        (writeList i (rcons ys' p) >> iqsort (i, size ys)) >>
        iqsort ((i + (size ys)%:Z + 1)%Z, size zs'))%Do)).
    rewrite -!bindA.
    have -> : commute (qperm ys) (@writeList _ _ M (i + (size ys)%:Z + 1) zs') _.
      by move=> T f; apply: commute_plus; exact: nondetPlus_sub_qperm.
    rewrite -!bindA.
    exact: refin_refl.
  rewrite (qperm_preserves_size2 ys (fun a b =>
    (writeList (i + b%:Z + 1) zs' >> (writeList i (rcons a p) >> iqsort (i, b))) >>
    iqsort ((i + b%:Z + 1)%Z, size zs'))).
  rewrite bind_qperm_guard (*NB: interesting?*).
  rewrite [in X in X `>=` _]bind_qperm_guard.
  apply: refin_bindl => ys'.
  apply: bind_refin_guard => /eqP sz_ys_ys'.
  rewrite -cats1.
  rewrite writeList_cat writeList_writeListC; last exact: leZZ.
  rewrite (bindA _ _ (fun _ => iqsort (i, size ys'))).
  apply: (@refin_trans _ _ (
      (writeList (i + (size ys')%:Z + 1) zs' >>
      (writeList (i + (size ys')%:Z) [:: p] >>
      ((do x <- slowsort ys'; writeList i x)%Do))) >>
      iqsort ((i + (size ys')%:Z + 1)%Z, size zs'))).
    rewrite !bindA.
    apply: refin_bindl => -[].
    apply: refin_bindl => -[].
    rewrite !bindretf.
    rewrite -!bindA.
    apply: refin_bindr.
    apply: ih.
    rewrite -sz_ys_ys'.
    move: nxs.
    rewrite /= ltnS.
    apply: leq_trans.
    rewrite ltnS.
    by rewrite -(size_partition p xs) Hpxs /= leq_addr.
  rewrite -[in X in _ `>=` X](_ : commute (slowsort ys') _ _); last first.
    by apply: commute_plus; exact: nondetPlus_sub_slowsort.
  rewrite !bindA.
  rewrite -[in X in _ `>=` X](_ : commute (slowsort ys') _ _); last first.
    by apply: commute_plus; exact: nondetPlus_sub_slowsort.
  rewrite (slowsort_preserves_size2 _ (fun a b => writeList (i + b%:Z + 1) zs' >> ((writeList (i + b%:Z) [:: p] >> writeList i a >> iqsort ((i + b%:Z + 1)%Z, size zs')))%Do)).
  rewrite bind_slowsort_guard [in X in X `>=` _]bind_slowsort_guard.
  apply: refin_bindl => ys''.
  apply: bind_refin_guard => /eqP ys'ys''.
  rewrite -bindA.
  rewrite -(@writeList_writeListC _ _ M _ _ ys''); last first.
    exact: leZZ.
  under [in X in X `>=` _]eq_bind do rewrite -cat_rcons.
  under [in X in X `>=` _]eq_bind do rewrite writeList_cat.
  rewrite (_ : commute (slowsort zs') _ _); last first.
    apply: commute_plus.
    exact: nondetPlus_sub_slowsort.
  rewrite -(writeList_cat i ys'' [:: p]).
  rewrite -(@writeList_writeListC _ _ M _ _ _ zs'); last first.
    by rewrite size_cat /= intRD addZA; exact: leZZ.
  rewrite cats1 bindA.
  apply: refin_bindl => -[].
  rewrite size_rcons -addZA natZS.
  rewrite Z.add_1_r.
  apply: ih.
  rewrite -zszs'.
  rewrite /= ltnS in nxs.
  rewrite (leq_trans _ nxs) // ltnS.
  by rewrite -(size_partition p xs) Hpxs /= leq_addl.
apply: (refin_trans _ step1) => {step1} {lhs}.
set lhs := (X in X `>=` _).
have step2 : lhs `>=`
  (do pat <- partl' p [::] [::] xs;
   (let
    '(ys, zs) := pat in
     writeList (i + (size ys)%:Z + 1) zs >>
     (writeList i (p :: ys) >> swap i (i + (size ys)%:Z)) >>
     (iqsort (i, size ys)) >> iqsort ((i + (size ys)%:Z + 1)%Z, size zs)))%Do.
  rewrite {}/lhs.
  apply: refin_bindl => -[ys sz].
  rewrite 4!bindA.
  apply: refin_bindl => -[].
  rewrite -2![in X in X `>=` _]bindA.
  rewrite [in X in X `>=` _](bindA _ (fun _ => iqsort _) (fun _ => iqsort _)).
  rewrite -2![in X in _ `>=` X]bindA.
  rewrite (bindA _ (fun _ => iqsort _) (fun _ => iqsort _)).
  apply: refin_bindr.
  exact: introduce_swap_rcons.
apply: (refin_trans _ step2) => {step2} {lhs}.
set lhs := (X in X `>=` _).
have step3 : lhs `>=`
  (do pat <- partl' p [::] [::] xs;
   (let
    '(ys, zs) := pat in
     aput i p >> writeList (i + 1)%Z (ys ++ zs) >>
     (swap i (i + (size ys)%:Z)) >>
     (iqsort (i, size ys)) >> iqsort ((i + (size ys)%:Z + 1)%Z, size zs)))%Do.
  rewrite {}/lhs.
  apply: refin_bindl => -[ys zs].
  rewrite -bindA.
  do 3 apply: refin_bindr.
  rewrite -writeList_writeListC; last first.
    by rewrite -addZA /= Z.add_1_r natZS; exact: leZZ.
  rewrite /= bindA.
  apply: refin_bindl => -[].
  rewrite writeList_cat -addZA (addZC 1%Z) addZA.
  exact: refin_refl.
apply: (refin_trans _ step3) => {step3} {lhs}.
set lhs := (X in X `>=` _).
have step4 : lhs `>=`
  (aput i p >>
   partl' p [::] [::] xs >>= (fun '(ys, zs) =>
   ( writeList (i + 1)%Z (ys ++ zs) >>
     (swap i (i + (size ys)%:Z)) >>
     (iqsort (i, size ys)) >> iqsort ((i + (size ys)%:Z + 1)%Z, size zs))))%Do.
  rewrite {}/lhs.
  rewrite bindA -[in X in _ `>=` X](_ : commute (partl' p [::] [::] xs) (aput i p) _); last first.
    by apply: commute_plus; exact: nondetPlus_sub_qpartl'.
  apply: refin_bindl => -[a b].
  rewrite !bindA.
  exact: refin_refl.
apply: (refin_trans _ step4) => {step4} {lhs}.
set lhs := (X in X `>=` _).
have step5 : lhs `>=`
  ((aput i p >>
   partl' p [::] [::] xs >>= (fun '(ys, zs) =>
    write2L (i + 1)%Z (ys, zs)) >>= (fun '(sys, szs) =>
     (swap i (i + (sys)%:Z)) >>
     (iqsort (i, sys)) >> iqsort ((i + (sys)%:Z + 1)%Z, szs))))%Do.
  rewrite {}/lhs.
  rewrite !bindA.
  apply: refin_bindl => -[].
  apply: refin_bindl => -[a b].
  rewrite 2!bindA.
  rewrite [in X in _ `>=` X]bindA.
  apply: refin_bindl => -[].
  rewrite bindretf.
  rewrite bindA.
  exact: refin_refl.
apply: (refin_trans _ step5) => {step5} {lhs}.
set lhs := (X in X `>=` _).
have step6 : lhs `>=`
  (((aput i p >>
   (write3L (i + 1)%Z ([::], [::], xs) >>= uncurry3 (ipartl p (i + 1)%Z))) >>=
   (fun '(sys, szs) =>
     (swap i (i + (sys)%:Z)) >>
     (iqsort (i, sys)) >> iqsort ((i + (sys)%:Z + 1)%Z, szs))))%Do.
  rewrite {}/lhs.
  apply: refin_bindr.
  rewrite bindA.
  apply: refin_bindl => -[].
  exact: lemma10.
apply: (refin_trans _ step6) => {step6} {lhs}.
set lhs := (X in X `>=` _).
have step7 : lhs `>=`
  ((writeList i (p :: xs) >> Ret p) >>= (fun p =>
   (ipartl p (i + 1)%Z) 0 0 (size xs) >>=
   (fun '(sys, szs) =>
     (swap i (i + (sys)%:Z)) >>
     (iqsort (i, sys)) >> iqsort ((i + (sys)%:Z + 1)%Z, szs))))%Do.
  rewrite {}/lhs.
  rewrite [in X in _ `>=` X]/=.
  rewrite 2![in X in _ `>=` X]bindA.
  rewrite bindA.
  apply: refin_bindl => -[].
  rewrite bindA /= bindA.
  apply: refin_bindl => -[].
  rewrite 2!bindretf /uncurry3.
  exact: refin_refl.
apply: (refin_trans _ step7) => {step7} {lhs}.
set lhs := (X in X `>=` _).
have step8 : lhs `>=`
  ((writeList i (p :: xs) >> aget i) >>= (fun p =>
   (ipartl p (i + 1)%Z) 0 0 (size xs) >>=
   (fun '(sys, szs) =>
     (swap i (i + (sys)%:Z)) >>
     (iqsort (i, sys)) >> iqsort ((i + (sys)%:Z + 1)%Z, szs))))%Do.
  rewrite {}/lhs.
  apply: refin_bindr.
  rewrite introduce_read.
  by apply: refin_refl.
apply: (refin_trans _ step8) => {step8} {lhs}.
rewrite bindA.
apply: refin_bindl => -[].
rewrite /=.
rewrite iqsort_cons.
apply: refin_bindl => x.
clear nxs.
rewrite ipartlE // fmapE bindA.
under [in X in X `>=` _]eq_bind do rewrite bindretf.
exact: refin_refl.
Qed.

Lemma qperm_preserves_guard B (p : pred E) (a : seq E) (f : seq E -> M B) :
  (* guard (all p a) >>= (fun _ => qperm a >>= f) = *)
  qperm a >>= (fun x => guard (all p a) >> f x) =
  qperm a >>= (fun x => guard (all p x) >> f x).
Proof.
  rewrite -guard_qperm_eq -bindA.
  rewrite (@guardsC M (@bindmfail M) _) bindA.
  bind_ext => ?.
  rewrite /assert; unlock.
  by rewrite bindA bindretf.
Qed.

End iqsort.
