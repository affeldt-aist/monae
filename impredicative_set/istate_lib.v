(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2020 monae authors, license: LGPL-2.1-or-later               *)
From mathcomp Require Import all_ssreflect.
Require Import imonae_lib.
From HB Require Import structures.
Require Import ihierarchy imonad_lib ifail_lib.

(******************************************************************************)
(*              Definitions and lemmas about state monads                     *)
(*                                                                            *)
(*          overwrite s a := put s >> Ret s                                   *)
(*              protect n := get >>= (fun x => n >>= overwrite x)             *)
(*                 scanlM == see section 4.1, mu2019tr3                       *)
(*        scanlM_of_scanl == see theorem 4.1, mu2019tr3                       *)
(*              theorem44 == see mu2019tr3                                    *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.

Lemma putgetput (S : UU0) {M : stateMonad S} x {B} (k : _ -> M B) :
  put x >> get >>= (fun x' => k x') = put x >> k x :> M _.
Proof. by rewrite putget bindA bindretf. Qed.

Definition overwrite {A S} {M : stateMonad S} s a : M A :=
  put s >> Ret a.

Definition protect {A S} {M : stateMonad S} (n : M A) :=
  get >>= (fun ini => n >>= overwrite ini).

Lemma protect_put_ret {A S : UU0} {M : stateMonad S} (s : S) (a : A) :
  protect (put s >> Ret a) = Ret a :> M _.
Proof.
rewrite /protect.
under eq_bind do rewrite bindA bindretf.
rewrite /overwrite.
under eq_bind do rewrite -bindA putput.
by rewrite -bindA getputskip bindskipf.
Qed.

Example test_nonce0 (M : stateMonad nat) : M nat :=
  get >>= (fun s => put s.+1 >> Ret s).
(*Reset test_nonce0.
Fail Check test_nonce0.*)

Section stateloop_examples.
Variable (M : loopStateMonad nat).
Let example min max : M unit := foreach max min (fun i : nat => get >> Ret tt).
Let sum n : M unit := foreach n O
  (fun i : nat => get >>= (fun z => put (z + i))).

Lemma sum_test n :
  sum n = get >>= (fun m => put (m + sumn (iota 0 n))).
Proof.
elim: n => [|n ih].
  rewrite /sum.
  rewrite loop0.
  rewrite (_ : sumn (iota 0 0) = 0) //.
  rewrite -[LHS]bindskipf.
  rewrite -getputskip.
  rewrite bindA.
  bind_ext => a.
  rewrite addn0.
  rewrite -[RHS]bindmret.
  bind_ext.
  by case.
rewrite {1}/sum -add1n loop1 bindA; bind_ext => m.
rewrite -/(sum n) {}ih -bindA putget bindA bindretf putput.
congr put.
by rewrite add0n (addnC 1) iotaD /= sumn_cat /= add0n addn0 /= addnAC addnA.
Qed.
End stateloop_examples.

Lemma getput_prepend (S : UU0) (M : nondetStateMonad S) A (m : M A) :
  m = get >>= (fun x => put x >> m).
Proof. by rewrite -{2}(bindskipf m) -bindA getputskip 2!bindskipf. Qed.


Section loop.
Variables (A S : UU0) (M : stateMonad S) (op : S -> A -> S).
Local Open Scope mprog.

Definition opmul x m : M _ :=
  get >>= fun st => let st' := op st x in fmap (cons st') (put st' >> m).

Definition scanlM s xs : M (seq S) :=
  let mul x m := opmul x m in put s >> foldr mul (Ret [::]) xs.

Lemma scanlM_nil s : scanlM s [::] = put s >> Ret [::].
Proof. by []. Qed.

Let scanlM_of_scanl_helper s
  (ms : M S) (mu mu' : M unit) (m : M (seq S)) (f : S -> M unit) :
  (do x <- ms; mu >> (do xs <- fmap (cons s) (mu' >> m); f x >> Ret xs) =
   fmap (cons s) (do x <- ms; mu >> mu' >> (do xs <- m; f x >> Ret xs)))%Do.
Proof.
rewrite [in RHS]fmapE !bindA.
under [RHS]eq_bind do rewrite bindA.
bind_ext => s'.
rewrite !bindA; bind_ext; case.
rewrite bind_fmap bindA; bind_ext; case.
by under [RHS]eq_bind do rewrite bindA bindretf.
Qed.

Lemma scanlM_of_scanl s xs : Ret (scanl op s xs) = protect (scanlM s xs).
Proof.
elim: xs s => [/=|x xs IH] s.
  by rewrite scanlM_nil protect_put_ret.
rewrite /scanlM [in RHS]/=.
set mul := fun (a : A) m => _.
under [RHS]eq_bind do rewrite -!bindA.
(* TODO(rei): tactic for nested function bodies? *)
transitivity (do y <- get; (put s >> get) >>= fun z =>
  do a <- fmap (cons (op z x)) (put (op z x) >> foldr mul (Ret [::]) xs);
  put y >> Ret a)%Do; last first.
  by under [LHS]eq_bind do rewrite -!bindA.
under eq_bind do rewrite putget bindA bindretf.
rewrite scanlM_of_scanl_helper.
transitivity (fmap (cons (op s x)) (do y <- get; put (op s x) >>
  (do a <- foldr mul (Ret [::]) xs; put y >> Ret a)))%Do; last first.
  by congr (fmap _ _); under [RHS]eq_bind do rewrite putput.
transitivity (fmap (cons (op s x)) (protect (scanlM (op s x) xs))); last first.
  by congr (fmap _ _); under eq_bind do rewrite -bindA.
by rewrite -IH fmapE bindretf.
Qed.

End loop.
Arguments scanlM {A S M}.

Section section43.

Variables (S : UU0) (M : nondetStateMonad S).
Variables (A : UU0) (op : S -> A -> S) (ok : pred S).

Lemma assert_all_scanl s (xs : seq A) :
  assert (all ok \o scanl op s) xs =
  protect (scanlM op s xs >>=
    (fun ys => guard (all ok ys) >> Ret xs)) :> M _.
Proof.
rewrite assertE guardsC; last exact: bindmfail.
transitivity (protect (scanlM op s xs) >>=
    (fun ys => guard (all ok ys) >> Ret xs) : M _).
  by rewrite -!bindA -scanlM_of_scanl bindA !bindretf assertE.
rewrite bindA [in RHS]/protect.
bind_ext => st.
rewrite 2!bindA; bind_ext => xs'.
rewrite [in RHS]bindA [in RHS]guardsC; last exact: bindmfail.
rewrite bindA bindretf.
rewrite /overwrite bindA bindretf bindA; bind_ext; case.
by rewrite bindretf assertE.
Qed.

Local Open Scope mprog.

Lemma put_foldr st x xs :
  put (op st x) >> (do x1 <- foldr (opmul op) (Ret [::]) xs;
    guard (all ok x1) >> guard (ok (op st x)))%Do =
  guard (ok (op st x)) >> (put (op st x) >>
    (do ys <- foldr (opmul op) (Ret [::]) xs; guard (all ok ys))%Do) :> M _.
Proof.
elim: xs x => [x|h t _ x].
  rewrite /= bindretf /= guardT /= bindskipf /= bindretf.
  rewrite (_ : guard (_ _ [::]) = skip) //= ?guardT //.
  rewrite bindmskip; case: guardPn => H.
  - by rewrite bindskipf bindmskip.
  - by rewrite bindmfail bindfailf.
rewrite /= !bindA.
transitivity (put (op st x) >>
  (do x0 <- get; do x1 <- let st' := op x0 h in
    fmap (cons st') (put st' >> foldr (opmul op) (Ret [::]) t);
    guard (ok (op st x)) >> guard (all ok x1))%Do : M _).
  bind_ext; case.
  bind_ext => st'.
  bind_ext => s.
  by rewrite -guard_and andbC guard_and.
rewrite guardsC; last exact: bindmfail.
rewrite !bindA.
bind_ext; case.
bind_ext => st'.
rewrite !bindA.
bind_ext => s.
rewrite guardsC //; exact: bindmfail.
Qed.

Let B := A.
Let res := @cons A.

Definition opdot (a : A) (m : M (seq B)) : M (seq B) :=
  get >>= (fun st => guard (ok (op st a)) >> put (op st a) >> fmap (res a) m).

Lemma theorem44 (xs : seq A) :
  foldr (opmul op) (Ret [::]) xs >>=
    (fun ys => guard (all ok ys) >> Ret xs) = foldr opdot (Ret [::]) xs.
Proof.
elim: xs => [|x xs IH]; first by rewrite /= bindretf /= guardT bindskipf.
rewrite [in LHS]/=.
rewrite {1}/opmul.
rewrite {1}bindA.
transitivity (get >>= (fun x0 =>
  put (op x0 x) >> foldr (opmul op) (Ret [::]) xs >>= (fun ys =>
  guard (all ok (op x0 x :: ys))) >> Ret (x :: xs)) : M _).
  bind_ext => st.
  by rewrite bind_fmap !bindA.
transitivity (get >>= (fun x0 =>
  put (op x0 x) >> foldr (opmul op) (Ret [::]) xs >>= (fun ys =>
  guard (all ok ys) >> guard (ok (op x0 x))) >> Ret (x :: xs)) : M _).
  bind_ext => st.
  rewrite !bindA.
  bind_ext; case.
  bind_ext => ys.
  rewrite -guard_and.
  congr (guard _ >> _).
  by rewrite -cat1s all_cat andbC all_seq1.
transitivity (get >>= (fun st => guard (ok (op st x)) >>
  put (op st x) >> foldr (opmul op) (Ret [::]) xs >>= (fun ys =>
   guard (all ok ys)) >> Ret (x :: xs)) : M _).
  bind_ext => st.
  rewrite -!bindA.
  congr (_ >> _).
  rewrite !bindA.
  by rewrite put_foldr.
transitivity (get >>= (fun st => guard (ok (op st x)) >>
  put (op st x) >>
    fmap (cons x) (foldr (opmul op) (Ret [::]) xs >>= (fun ys =>
   guard (all ok ys)) >> Ret xs)) : M _).
  bind_ext => st.
  rewrite !bindA.
  bind_ext; case.
  bind_ext; case.
  rewrite !fmap_bind.
  bind_ext => s.
  rewrite fcompE fmap_bind /=.
  bind_ext; case.
  by rewrite fcompE fmapE bindretf.
by rewrite [in RHS]/= -IH /opdot !bindA.
Qed.

End section43.

Definition promotable (A : UU0) (p : pred (seq A)) (q : pred (seq A * seq A)) :=
  forall s t, p s -> p t -> p (s ++ t) = q (s, t).

Lemma segment_closed_suffix (A : UU0) (p : segment_closed.t A) s :
  ~~ p s -> forall t, ~~ p (s ++ t).
Proof. move=> ps t; apply: contra ps; by case/segment_closed.H. Qed.

Lemma segment_closed_prefix (A : UU0) (p : segment_closed.t A) s :
  ~~ p s -> forall t, ~~ p (t ++ s).
Proof. move=> ps t; apply: contra ps; by case/segment_closed.H. Qed.

(* assert p distributes over concatenation *)
Local Open Scope mprog.
Definition promote_assert (M : failMonad) (A : UU0)
  (p : pred (seq A)) (q : pred (seq A * seq A)) :=
  (bassert p) \o (fmap ucat) \o mpair =
  (fmap ucat) \o (bassert q) \o mpair \o (bassert p)^`2 :> (_ -> M _).
Local Close Scope mprog.

Lemma promote_assert_sufficient_condition (M : failMonad) (A : UU0) :
  BindLaws.right_zero (@bind M) (@fail _) ->
  forall (p : segment_closed.t A) q, promotable p q ->
  promote_assert M p q.
Proof.
move=> right_z p q promotable_pq.
rewrite /promote_assert; apply: funext => -[x1 x2].
rewrite 3![in RHS]compE [in RHS]fmapE.
rewrite 2![in LHS]compE {1}/bassert [in LHS]bind_fmap !bindA.
bind_ext => s.
rewrite bindA; under eq_bind do rewrite bindretf.
case: assertPn => ps; last first.
  rewrite bindfailf.
  With (idtac) Open (X in _ >>= X).
    rewrite /assert; unlock => /=.
    rewrite (negbTE (segment_closed_suffix ps x)) guardF bindfailf.
    reflexivity.
  by rewrite right_z.
rewrite bindretf bindA /=.
under [RHS]eq_bind do rewrite bindretf.
rewrite bindA.
bind_ext => t.
case: (assertPn _ _ t) => pt; last first.
  rewrite bindfailf assertE (negbTE (segment_closed_prefix pt s)) guardF.
  by rewrite bindfailf.
by rewrite bindretf /=  2!assertE promotable_pq //= bindA bindretf.
Qed.

Section examples_promotable_segment_closed.

(* is a contiguous segment of the enumeration *)
(* TODO(rei): generalize to any enumeration *)
Definition is_iota : pred (seq nat) := [pred x | x == iota (head O x) (size x) ].

Lemma is_iota_head_last s : is_iota s -> 0 < size s -> head 0 s + size s = (last 0 s).+1.
elim: s => //= a [_ /=|c d IH].
  by rewrite addn1.
rewrite /is_iota /= => /eqP[] ?; subst c => Hd _.
rewrite /= in IH.
by rewrite -IH // -?addSnnS // /is_iota /= -Hd.
Qed.

(* predicate "are adjacent segments" *)
Definition are_adjacent : pred (seq nat * seq nat)%type :=
  [pred xy | [|| xy.1 == [::] , xy.2 == [::] | (last O xy.1).+1 == head O xy.2]].

Lemma promotable_enum : promotable is_iota are_adjacent.
Proof.
move=> s t Hs Ht.
rewrite /is_iota /= size_cat iotaD.
case/boolP : (nilp s) => [/nilP ->{Hs s} /=|s0]; first by rewrite addn0 /are_adjacent.
rewrite /nilp -lt0n in s0.
have -> : head 0 (s ++ t) = head 0 s by rewrite -nth0 nth_cat sub0n s0.
rewrite -(eqP Hs) /are_adjacent /= -size_eq0 -(negbK (size s == _)) -lt0n s0 /=.
rewrite eqseq_cat // eqxx /=.
case/boolP : (nilp t) => [/nilP {Ht} ->{t} //|t0].
rewrite /nilp -lt0n in t0.
rewrite -(size_eq0 t) -(negbK (size t == _)) -lt0n t0 /=.
case: t Ht t0 => // a b Hab _.
rewrite [head _ (_ :: _)]/=.
rewrite is_iota_head_last //= eqseq_cons eq_sym andb_idr // => /eqP Ha.
move: Hab.
by rewrite /is_iota /= => /eqP[] {1}->; rewrite -Ha.
Qed.

Local Obligation Tactic := idtac.
Program Definition is_iota_is_segment_closed : segment_closed.t nat :=
  @segment_closed.mk _ is_iota _.
Next Obligation.
move=> a b.
rewrite /is_iota /= /= size_cat => /eqP Hab.
apply/andP; rewrite -eqseq_cat ?size_iota //; apply/eqP.
case/boolP : (nilp a) => [/nilP a0|a0]; first by move: Hab; rewrite a0.
case/boolP : (nilp b) => [/nilP b0|b0].
  by move: Hab; rewrite b0 /= !cats0 addn0.
have -> : head 0 b = head 0 a + size a.
  move/(congr1 (fun x => nth 0 x (size a))) : Hab.
  rewrite nth_cat ltnn subnn nth0 => ->; rewrite -nth0 nth_cat lt0n.
  by rewrite a0 nth0 nth_iota // -{1}(addn0 (size a)) ltn_add2l lt0n.
suff <- : head 0 (a ++ b) = head 0 a by rewrite -iotaD.
by rewrite -nth0 nth_cat lt0n a0.
Qed.

End examples_promotable_segment_closed.

Section properties_of_Symbols.
Variables (A : UU0) (M : failFreshMonad A).

Lemma symbolsE : symbols = (fun n => sequence (nseq n fresh)) :> (_ -> M _).
Proof. by case: M => m [? ? []]. Qed.

Lemma symbols0 : symbols 0 = Ret [::] :> M _.
Proof. by rewrite symbolsE. Qed.

Lemma symbolsS n : symbols n.+1 =
  (do x <- fresh ; do xs <- symbols n : M _; Ret (x :: xs))%Do.
Proof. by rewrite symbolsE. Qed.

Lemma symbols_prop1 :
  symbols \o const 1 = (M # wrap) \o const fresh :> (A -> M _).
Proof.
apply: funext => n.
transitivity (@symbols _ M 1) => //.
rewrite symbolsE sequence_cons sequence_nil.
under eq_bind do rewrite bindretf.
by rewrite compE [in RHS]fmapE.
Qed.

Local Open Scope mprog.

Lemma symbols_prop2 :
  symbols \o uaddn = (fmap ucat) \o mpair \o (symbols : _ -> M _)^`2.
Proof.
apply: funext => -[n1 n2].
elim: n1 => [|n1 IH].
  rewrite [in LHS]compE uaddnE add0n.
  rewrite compE [in X in _ = _ X]/= squaringE symbols0.
  rewrite compE [in RHS]fmapE bindA bindretf.
  rewrite -fmapE fmap_bind.
  Open (X in _ >>= X).
    rewrite fcompE fmapE bindretf /=; reflexivity.
  by rewrite bindmret.
rewrite compE uaddnE addSn symbolsS -uaddnE -(compE symbols) {}IH.
rewrite [in RHS]compE [in X in _ = _ X]/= squaringE symbolsS.
rewrite [in RHS]compE -/(fmap _ _) fmap_bind bindA; bind_ext => a.
rewrite 2![in LHS]compE [in LHS]fmap_bind [in LHS]bindA [in RHS]bindA.
bind_ext => s.
rewrite [in RHS]bindretf [in RHS]fcompE [in RHS]fmap_bind.
rewrite [in LHS]fcompE [in LHS]bind_fmap [in LHS]bindA.
under eq_bind do rewrite bindretf.
by under [RHS]eq_bind do rewrite fcompE fmapE bindretf.
Qed.

End properties_of_Symbols.

Definition swap {S : UU0} {I : eqType} {M : arrayMonad S I} (i j : I) : M unit :=
  (do x <- aget i ;
   do y <- aget j ;
   aput i y >>
   aput j x)%Do.

Section tick_fusion.
Context {M : stateMonad nat}.

Definition tick : M unit := get >>= (put \o succn).

Lemma tick_fusion n : rep n tick = get >>= (put \o addn n).
Proof.
elim: n => [|n ih]; first by rewrite /= -getputskip.
rewrite /= /tick ih.
rewrite bindA.
bind_ext => m.
rewrite -bindA.
rewrite putget.
rewrite bindA.
rewrite bindretf.
rewrite putput.
by rewrite /= addSnnS.
Qed.

End tick_fusion.
