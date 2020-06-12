Require Import ZArith.
From mathcomp Require Import all_ssreflect.
From mathcomp Require boolp.
From infotheo Require Import ssrZ.
Require Import monae_lib hierarchy monad_lib fail_lib.

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

Local Open Scope monae_scope.

Lemma putgetput (S : Type) {M : stateMonad S} x {B} (k : _ -> M B) :
  Put x >> Get >>= (fun x' => k x') = Put x >> k x :> M _.
Proof. by rewrite putget bindA bindretf. Qed.

Definition overwrite {A S} {M : stateMonad S} s a : M A :=
  Put s >> Ret a.

Definition protect {A S} {M : stateMonad S} (n : M A) :=
  Get >>= (fun ini => n >>= overwrite ini).

Lemma protect_put_ret {A S} {M : stateMonad S} (s : S) (a : A) :
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

Lemma getput_prepend (S : Type) (M : nondetStateMonad S) A (m : M A) :
  m = Get >>= (fun x => Put x >> m).
Proof. by rewrite -{2}(bindskipf m) -bindA getputskip 2!bindskipf. Qed.

Section state_commute.

Variables (S : Type) (M : nondetStateMonad S).

Lemma puttselectC (x : S) A (s : seq A) B (f : _ -> M B) :
  Put x >> (tselect s >>= f) = tselect s >>= (fun rs => Put x >> f rs).
Proof.
elim: s f => [|h t IH] f.
  by rewrite tselect_nil 2!bindfailf bindmfail.
  case: t IH f => [|h' t] IH f.
  by rewrite tselect1 !bindretf.
rewrite tselect_cons // => H.
rewrite [in LHS]alt_bindDl [in RHS]alt_bindDl alt_bindDr.
congr (_ [~] _); first by rewrite 2!bindretf.
rewrite 2!bindA IH; bind_ext => y; by rewrite !bindretf.
Qed.

Lemma putselectC (x : S) A (s : seq A) B (f : A * (seq A) -> M B) :
  Put x >> (select s >>= f) = select s >>= (fun rs => Put x >> f rs).
Proof.
rewrite selectE {1}fmapE.
rewrite_ bindA.
rewrite puttselectC [in RHS]fmapE bindA.
bind_ext => x0; by rewrite 2!bindretf.
Qed.

Lemma gettselectC A (s : seq A) B (f : _ -> _ -> M B) :
  (do ini <- Get; do rs <- tselect s; f rs ini =
   do rs <- tselect s; do ini <- Get; f rs ini)%Do.
Proof.
elim: s f => [|h t IH] f.
  rewrite tselect_nil bindfailf; rewrite_ bindfailf; by rewrite bindmfail.
case: t IH f => [|h' t] IH f.
  rewrite tselect1 bindretf; by rewrite_ bindretf.
rewrite tselect_cons // => H.
rewrite [tselect _]lock.
rewrite_ alt_bindDl.
rewrite [in RHS]alt_bindDl alt_bindDr.
congr (_ [~] _).
  rewrite bindretf; bind_ext => ?; by rewrite bindretf.
rewrite -lock.
transitivity (do x0 <- tselect (h' :: t); do x <- Get;
   f (x0.1, Tuple (fail_lib.tselect_cons_statement_obligation_2 h H x0)) x)%Do.
 rewrite -IH; bind_ext => x.
 rewrite bindA;by rewrite_ bindretf.
rewrite bindA; bind_ext => y; by rewrite bindretf.
Qed.

Lemma putpermsC (x : S) A (s : seq A) B (f : _ -> M B) :
  Put x >> (perms s >>= f) = perms s >>= (fun rs => Put x >> f rs).
Proof.
move Hn : (size s) => n.
elim: n s Hn x f => [|n IH] s Hn x f.
  by case: s Hn => // _; rewrite permsE 2!bindretf.
case: s Hn => // h t [Hn].
rewrite tpermsE 2!bindA puttselectC; bind_ext; case=> a b.
rewrite 2!bindA.
have bn : size b = n by rewrite size_tuple.
rewrite IH //.
by do 2! rewrite_ bindretf.
Qed.

Lemma getpermsC A (s : seq A) B (f : _ -> _ -> M B) :
  (Get >>= (fun ini => perms s >>=  f^~ ini) =
   perms s >>= (fun rs => Get >>= f rs))%Do.
Proof.
move Hn : (size s) => n.
elim: n s Hn f => [|n IH] s Hn f.
  case: s Hn => // _; rewrite permsE.
  by rewrite bindretf; rewrite_ bindretf.
case: s Hn => // h t [Hn].
rewrite tpermsE bindA.
transitivity (do x <- tselect (h :: t); do ini <- Get; do rs <- perms x.2;
  f (x.1 :: rs) ini)%Do; last first.
  bind_ext => x.
  rewrite IH ?size_tuple // bindA.
  by rewrite_ bindretf.
rewrite -gettselectC.
bind_ext => x.
rewrite bindA; bind_ext => rs.
rewrite bindA.
by rewrite_ bindretf.
Qed.

End state_commute.

Definition nondetState_sub S (M : nondetStateMonad S) A (n : M A) :=
  {m | ndDenote m = n}.

Lemma select_is_nondetState S (M : nondetStateMonad S) A (s : seq A) :
  nondetState_sub (select s : M _).
Proof.
elim: s => [/= | u v [x /= <-]]; first by exists (@ndFail _).
by exists (ndAlt (ndRet (u, v)) (ndBind x (fun x => ndRet (x.1, u :: x.2)))).
Qed.

Lemma unfoldM_is_nondetState S (M : nondetStateMonad S) A B
  (f : seq B -> M (A * seq B)%type) :
  (forall s, nondetState_sub (f s)) -> bassert_size f ->
  forall s, nondetState_sub (unfoldM (@well_founded_size B) (@nilp _) f s).
Proof.
move=> Hf size_f s.
apply/boolp.constructive_indefinite_description.
move: s; apply: (well_founded_induction (@well_founded_size _)) => s IH.
have {}IH : forall x, size x < size s ->
  { m | ndDenote m = unfoldM (@well_founded_size B) (@nilp _) f x}.
  move=> x xs; exact/boolp.constructive_indefinite_description/IH.
case: s IH => [|h t] IH.
  rewrite unfoldME //=; by exists (ndRet [::]).
rewrite unfoldME //.
rewrite (_ : nilp _ = false) //.
case: (Hf (h :: t)) => x Hx.
rewrite -Hx.
set g := fun y => match Bool.bool_dec (size y < size (h :: t)) true with
               | left H => let: exist x _ := IH _ H in x
               | _ => ndRet [::]
               end.
refine (ex_intro _ (ndBind x (fun x => ndBind (g x.2) (@ndRet _ \o cons x.1 ))) _).
rewrite [in LHS]/=.
rewrite Hx size_f /bassert !bindA.
bind_ext => -[x1 x2].
case: assertPn; rewrite ltnS => b1b2; last by rewrite !bindfailf.
rewrite !bindretf /g.
case: Bool.bool_dec => // x2t.
case: (IH x2) => // x0 <-; by rewrite fmapE.
Qed.

Definition commute {M : monad} A B (m : M A) (n : M B) C (f : A -> B -> M C) : Prop :=
  m >>= (fun x => n >>= (fun y => f x y)) = n >>= (fun y => m >>= (fun x => f x y)) :> M _.

Lemma commute_nondetState S (M : nondetStateMonad S)
  A (m : M A) B (n : M B) C (f : A -> B -> M C) :
  nondetState_sub m -> commute m n f.
Proof.
case => x.
elim: x m n f => [{}A a m n f <-| B0 {}A n0 H0 n1 H1 m n2 f <- |
  A0 m n f <- | A0 n0 H0 n1 H1 m n2 f <-].
- rewrite /commute bindretf.
  by rewrite_ bindretf.
- rewrite /commute /= !bindA.
  transitivity (do x <- ndDenote n0; do y <- n2; ndDenote (n1 x) >>= f^~ y)%Do.
    bind_ext => s.
    by rewrite (H1 s).
  rewrite H0 //.
  bind_ext => b.
  by rewrite bindA.
- rewrite /commute /= bindfailf.
  transitivity (n >> Fail : M C); first by rewrite bindmfail.
  bind_ext => b.
  by rewrite bindfailf.
- rewrite /commute /= alt_bindDl.
  transitivity (do y <- n2; ndDenote n0 >>= f^~ y [~]
                           ndDenote n1 >>= f^~ y)%Do; last first.
    bind_ext => a.
    by rewrite alt_bindDl.
  by rewrite alt_bindDr H0 // H1.
Qed.

Section loop.
Variables (A S : Type) (M : stateMonad S) (op : S -> A -> S).
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

Variables (S : Type) (M : nondetStateMonad S).
Variables (A : Type) (op : S -> A -> S) (ok : pred S).

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

(* TODO: move? *)
Definition intersect {A : eqType} (s t : seq A) : seq A := filter (mem s) t.

Lemma nilp_intersect (A : eqType) (s t : seq A) :
  nilp (intersect s t) = ~~ has (mem s) t.
Proof. by rewrite /intersect /nilp size_filter has_count lt0n negbK. Qed.

Definition seq_disjoint {A : eqType} : pred [eqType of (seq A)`2] :=
  (@nilp _) \o uncurry intersect.

Lemma intersect0s (A : eqType) (s : seq A) : intersect [::] s = [::].
Proof. by elim: s. Qed.

Definition promotable A (p : pred (seq A)) (q : pred (seq A * seq A)) :=
  forall s t, p s -> p t -> p (s ++ t) = q (s, t).

Lemma segment_closed_suffix A (p : segment_closed.t A) s :
  ~~ p s -> forall t, ~~ p (s ++ t).
Proof. move=> ps t; apply: contra ps; by case/segment_closed.H. Qed.

Lemma segment_closed_prefix A (p : segment_closed.t A) s :
  ~~ p s -> forall t, ~~ p (t ++ s).
Proof. move=> ps t; apply: contra ps; by case/segment_closed.H. Qed.

(* assert p distributes over concatenation *)
Local Open Scope mprog.
Definition promote_assert (M : failMonad) A
  (p : pred (seq A)) (q : pred (seq A * seq A)) :=
  (bassert p) \o (fmap ucat) \o mpair =
  (fmap ucat) \o (bassert q) \o mpair \o (bassert p)^`2 :> (_ -> M _).
Local Close Scope mprog.

Lemma promote_assert_sufficient_condition (M : failMonad) A :
  BindLaws.right_zero (@Bind M) (@Fail _) ->
  forall (p : segment_closed.t A) q, promotable p q ->
  promote_assert M p q.
Proof.
move=> right_z p q promotable_pq.
rewrite /promote_assert boolp.funeqE => -[x1 x2].
rewrite 3![in RHS]compE [in RHS]fmapE.
rewrite 2![in LHS]compE {1}/bassert [in LHS]bind_fmap !bindA.
bind_ext => s.
rewrite bindA; rewrite_ bindretf.
case: assertPn => ps; last first.
  rewrite bindfailf.
  With (idtac) Open (X in _ >>= X).
    rewrite /assert; unlock => /=.
    rewrite (negbTE (segment_closed_suffix ps x)) guardF bindfailf.
    reflexivity.
  by rewrite right_z.
rewrite bindretf bindA /=.
rewrite_ bindretf.
rewrite bindA.
bind_ext => t.
case: (assertPn _ _ t) => pt; last first.
  rewrite bindfailf assertE (negbTE (segment_closed_prefix pt s)) guardF.
  by rewrite bindfailf.
by rewrite bindretf /=  2!assertE promotable_pq //= bindA bindretf.
Qed.

Section examples_promotable_segment_closed.

Lemma promotable_uniq_seq_disjoint A : promotable (@uniq A) seq_disjoint.
Proof.
move=> s t ps pt.
by rewrite cat_uniq ps pt /= andbT -nilp_intersect.
Qed.

Local Obligation Tactic := idtac.
Program Definition uniq_is_segment_closed (A : eqType) : segment_closed.t A :=
  @segment_closed.mk _ (@uniq A) _.
Next Obligation. by move=> A a b; rewrite cat_uniq => /and3P[]. Qed.

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
rewrite /is_iota /= size_cat iota_add.
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
suff <- : head 0 (a ++ b) = head 0 a by rewrite -iota_add.
by rewrite -nth0 nth_cat lt0n a0.
Qed.

End examples_promotable_segment_closed.

Section properties_of_Symbols.
Variables (A : eqType) (M : failFreshMonad A).

Lemma SymbolsE : Symbols = (fun n => sequence (nseq n Fresh)) :> (_ -> M _).
Proof. by case: M => m [? ? [? ? ? ?]]. Qed.

Lemma Symbols0 : Symbols 0 = Ret [::] :> M _.
Proof. by rewrite SymbolsE. Qed.

Lemma SymbolsS n : Symbols n.+1 =
  (do x <- Fresh ; do xs <- Symbols n : M _; Ret (x :: xs))%Do.
Proof. by rewrite SymbolsE. Qed.

Lemma Symbols_prop1 :
  Symbols \o const 1 = (M # wrap) \o const Fresh :> (A -> M _).
Proof.
rewrite boolp.funeqE => n.
transitivity (@Symbols _ M 1) => //.
rewrite SymbolsE sequence_cons sequence_nil.
rewrite_ bindretf.
by rewrite compE [in RHS]fmapE.
Qed.

Local Open Scope mprog.

Lemma Symbols_prop2 :
  Symbols \o uaddn = (fmap ucat) \o mpair \o (Symbols : _ -> M _)^`2.
Proof.
rewrite boolp.funeqE => -[n1 n2].
elim: n1 => [|n1 IH].
  rewrite [in LHS]compE uaddnE add0n.
  rewrite compE [in X in _ = _ X]/= squaringE Symbols0.
  rewrite compE [in RHS]fmapE bindA bindretf.
  rewrite -fmapE fmap_bind.
  Open (X in _ >>= X).
    rewrite fcompE fmapE bindretf /=; reflexivity.
  by rewrite bindmret.
rewrite compE uaddnE addSn SymbolsS -uaddnE -(compE Symbols) {}IH.
rewrite [in RHS]compE [in X in _ = _ X]/= squaringE SymbolsS.
rewrite [in RHS]compE -/(fmap _ _) fmap_bind bindA; bind_ext => a.
rewrite 2![in LHS]compE [in LHS]fmap_bind [in LHS]bindA [in RHS]bindA.
(* TODO(rei): bind_ext? *)
congr Bind; rewrite boolp.funeqE => s.
rewrite [in RHS]bindretf [in RHS]fcompE [in RHS]fmap_bind.
rewrite [in LHS]fcompE [in LHS]bind_fmap [in LHS]bindA.
rewrite_ bindretf.
rewrite_ fcompE.
rewrite_ fmapE.
by rewrite_ bindretf.
Qed.

End properties_of_Symbols.

Section monadarray_example.
Local Open Scope do_notation.

Variables (M : arrayMonad nat bool_eqType).

Definition swap : M unit :=
  do x <- aGet false ;
  do y <- aGet true ;
  aPut false y >>
  aPut true x.

Definition does_swap (m : M unit) :=
  (do x <- aGet false ;
   do y <- aGet true ;
   m >>
   do x' <- aGet false ;
   do y' <- aGet true ;
   Ret ((x == y') && (y == x'))).

Lemma swapP (m : M unit) :
  does_swap swap = swap >> Ret true.
Proof.
rewrite /swap /does_swap.
transitivity (
  do x <- aGet false;
  do y <- aGet true;
  do x0 <- aGet false;
  (do y0 <- aGet true; aPut false y0 >> aPut true x0) >>
  (do x' <- aGet false; do y' <- aGet true; Ret ((x == y') && (y == x'))) : M _).
  bind_ext => x; by rewrite_ bindA. (* TODO: should be shorter *)
rewrite agetC.
rewrite_ agetget.
transitivity (
  do x <- aGet true;
  do s <- aGet false;
  do y0 <- aGet true; (aPut false y0 >> aPut true s) >>
  (do x' <- aGet false; do y' <- aGet true; Ret ((s == y') && (x == x'))) : M _).
  bind_ext => x; by rewrite_ bindA. (* TODO: should be shorter *)
rewrite agetC.
rewrite_ agetget.
transitivity (
  do x <- aGet false;
  do s <- aGet true;
  (aPut false s >> (aPut true x >>
  do y' <- aGet true; do x' <- aGet false; Ret ((x == y') && (s == x')))) : M _).
  bind_ext => x. bind_ext => y. rewrite bindA. bind_ext; case. by rewrite_ agetC.
transitivity (
  do x <- aGet false;
  do s <- aGet true;
  (aPut false s >> (aPut true x >>
  do x' <- aGet false; Ret ((x == x) && (s == x')))) : M _).
  bind_ext => x.
  bind_ext => y.
  bind_ext; case.
  by rewrite -bindA aputget.
transitivity (
  do x <- aGet false;
  do s <- aGet true;
  (aPut true x >> aPut false s >> (do x' <- aGet false; Ret ((x == x) && (s == x')))) : M _).
  bind_ext => x.
  bind_ext => y.
  rewrite -bindA aputC //=; by left.
transitivity (
  do x <- aGet false;
  do s <- aGet true;
  (aPut true x >> aPut false s) >> Ret ((x == x) && (s == s)) : M _).
  bind_ext => x.
  bind_ext => y.
  rewrite 2!bindA.
  bind_ext; case.
  by rewrite -bindA aputget.
transitivity (
  do x <- aGet false;
  do s <- aGet true;
  (aPut true x >> aPut false s) >> Ret true : M _).
  bind_ext => x.
  bind_ext => y.
  by rewrite 2!eqxx.
rewrite bindA.
bind_ext => x.
rewrite bindA.
bind_ext => y.
rewrite aputC //; by left.
Qed.

End monadarray_example.
