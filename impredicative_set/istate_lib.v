Require Import ZArith.
From mathcomp Require Import all_ssreflect.
From infotheo Require Import ssrZ.
Require Import imonae_lib ihierarchy imonad_lib ifail_lib.

(******************************************************************************)
(*              Definitions and lemmas about state monads                     *)
(*                                                                            *)
(* putpermsC                                                                  *)
(*   perms is independent of the state and so commutes with put               *)
(* commute (ref: definition 4.2, mu2019tr3)                                   *)
(* Section loop (ref: section 4.1, mu2019tr3)                                 *)
(*   scanlM                                                                   *)
(*   scanlM_of_scanl (ref: theorem 4.1, mu2019tr3)                            *)
(* Section section43.                                                         *)
(*   ref: mu2019tr3                                                           *)
(*   theorem44                                                                *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Univ.
Local Open Scope monae_scope.

Lemma putgetput (S : UU0) {M : stateMonad S} x {B} (k : _ -> M B) :
  Put x >> Get >>= (fun x' => k x') = Put x >> k x :> M _.
Proof. by rewrite putget bindA bindretf. Qed.

Definition overwrite {A S} {M : stateMonad S} s a : M A :=
  Put s >> Ret a.

Definition protect {A S} {M : stateMonad S} (n : M A) :=
  Get >>= (fun ini => n >>= overwrite ini).

Lemma protect_put_ret {A S : UU0} {M : stateMonad S} (s : S) (a : A) :
  protect (Put s >> Ret a) = Ret a :> M _.
Proof.
rewrite /protect.
rewrite_ bindA.
rewrite_ bindretf.
rewrite /overwrite.
Inf rewrite -bindA.
rewrite_ putput.
by rewrite -bindA getputskip bindskipf.
Qed.

Example test_nonce0 (M : stateMonad nat) : M nat :=
  Get >>= (fun s => Put s.+1 >> Ret s).
(*Reset test_nonce0.
Fail Check test_nonce0.*)

Section stateloop_examples.
Variable (M : loopStateMonad nat).
Let example min max : M unit := Foreach max min (fun i : nat => (Get >> Ret tt : M _)).
Let sum n : M unit := Foreach n O
  (fun i : nat => (Get >>= (fun z => Put (z + i)) : M _)).

Lemma sum_test n :
  sum n = Get >>= (fun m => Put (m + sumn (iota 0 n))).
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
congr Put.
rewrite add0n (addnC 1).
rewrite iota_add /= sumn_cat /=.
by rewrite add0n addn0 /= addnAC addnA.
Qed.
End stateloop_examples.

Lemma getput_prepend (S : UU0) (M : nondetStateMonad S) A (m : M A) :
  m = Get >>= (fun x => Put x >> m).
Proof. by rewrite -{2}(bindskipf m) -bindA getputskip 2!bindskipf. Qed.

Section loop.
Variables (A S : UU0) (M : stateMonad S) (op : S -> A -> S).
Local Open Scope mprog.

Definition opmul x m : M _ :=
  Get >>= fun st => let st' := op st x in fmap (cons st') (Put st' >> m).

Definition scanlM s xs : M (seq S) :=
  let mul x m := opmul x m in Put s >> foldr mul (Ret [::]) xs.

Lemma scanlM_nil s : scanlM s [::] = Put s >> Ret [::].
Proof. by []. Qed.

Let scanlM_of_scanl_helper s
  (ms : M S) (mu mu' : M unit) (m : M (seq S)) (f : S -> M unit) :
  (do x <- ms; mu >> (do xs <- fmap (cons s) (mu' >> m); f x >> Ret xs) =
   fmap (cons s) (do x <- ms; mu >> mu' >> (do xs <- m; f x >> Ret xs)))%Do.
Proof.
rewrite [in RHS]fmapE !bindA.
rewrite_ bindA.
bind_ext => s'.
rewrite !bindA; bind_ext; case.
rewrite bind_fmap bindA; bind_ext; case.
rewrite_ bindA.
by rewrite_ bindretf.
Qed.

Lemma scanlM_of_scanl s xs : Ret (scanl op s xs) = protect (scanlM s xs).
Proof.
elim: xs s => [/=|x xs IH] s.
  by rewrite scanlM_nil protect_put_ret.
rewrite /scanlM [in RHS]/=.
set mul := fun (a : A) m => _.
Inf rewrite !bindA.
(* TODO(rei): tactic for nested function bodies? *)
transitivity (do y <- Get; (Put s >> Get) >>= fun z =>
  do a <- fmap (cons (op z x)) (Put (op z x) >> foldr mul (Ret [::]) xs);
  Put y >> Ret a)%Do; last by Inf rewrite !bindA.
rewrite_ putget.
rewrite_ bindA.
rewrite_ bindretf.
rewrite scanlM_of_scanl_helper.
transitivity (fmap (cons (op s x)) (do y <- Get; Put (op s x) >>
  (do a <- foldr mul (Ret [::]) xs; Put y >> Ret a)))%Do; last first.
  congr (fmap _ _); by rewrite_ putput.
transitivity (fmap (cons (op s x)) (protect (scanlM (op s x) xs))); last first.
  congr (fmap _ _); by Inf rewrite -bindA.
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
  Put (op st x) >> (do x1 <- foldr (opmul op) (Ret [::]) xs;
    guard (all ok x1) >> guard (ok (op st x)))%Do =
  guard (ok (op st x)) >> (Put (op st x) >>
    (do ys <- foldr (opmul op) (Ret [::]) xs; guard (all ok ys))%Do) :> M _.
Proof.
elim: xs x => [x|h t _ x].
  rewrite /= bindretf /= guardT /= bindskipf /= bindretf.
  rewrite (_ : guard (_ _ [::]) = skip) //= ?guardT //.
  rewrite bindmskip; case: guardPn => H.
  - by rewrite bindskipf bindmskip.
  - by rewrite bindmfail bindfailf.
rewrite /= !bindA.
transitivity (Put (op st x) >>
  (do x0 <- Get; do x1 <- let st' := op x0 h in
    fmap (cons st') (Put st' >> foldr (opmul op) (Ret [::]) t);
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
  Get >>= (fun st => guard (ok (op st a)) >> Put (op st a) >> fmap (res a) m).

Lemma theorem44 (xs : seq A) :
  foldr (opmul op) (Ret [::]) xs >>=
    (fun ys => guard (all ok ys) >> Ret xs) = foldr opdot (Ret [::]) xs.
Proof.
elim: xs => [|x xs IH]; first by rewrite /= bindretf /= guardT bindskipf.
rewrite [in LHS]/=.
rewrite {1}/opmul.
rewrite {1}bindA.
transitivity (Get >>= (fun x0 =>
  Put (op x0 x) >> foldr (opmul op) (Ret [::]) xs >>= (fun ys =>
  guard (all ok (op x0 x :: ys))) >> Ret (x :: xs)) : M _).
  bind_ext => st.
  by rewrite bind_fmap !bindA.
transitivity (Get >>= (fun x0 =>
  Put (op x0 x) >> foldr (opmul op) (Ret [::]) xs >>= (fun ys =>
  guard (all ok ys) >> guard (ok (op x0 x))) >> Ret (x :: xs)) : M _).
  bind_ext => st.
  rewrite !bindA.
  bind_ext; case.
  bind_ext => ys.
  rewrite -guard_and.
  congr (guard _ >> _).
  by rewrite -cat1s all_cat andbC all_seq1.
transitivity (Get >>= (fun st => guard (ok (op st x)) >>
  Put (op st x) >> foldr (opmul op) (Ret [::]) xs >>= (fun ys =>
   guard (all ok ys)) >> Ret (x :: xs)) : M _).
  bind_ext => st.
  rewrite -!bindA.
  congr (_ >> _).
  rewrite !bindA.
  by rewrite put_foldr.
transitivity (Get >>= (fun st => guard (ok (op st x)) >>
  Put (op st x) >>
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
