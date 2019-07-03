Require Import ZArith ssreflect ssrmatching ssrfun ssrbool.
From mathcomp Require Import eqtype ssrnat seq choice fintype tuple.
From mathcomp Require Import boolp.
From infotheo Require Import ssrZ.
Require Import monad.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Contents:
- Module MonadState.
- Module MonadStateRun.
- Module MonadNondetState.
- Module MonadFresh.
- Module MonadFailFresh.
- Module MonadArray.
*)

Module MonadState.
Record mixin_of S (M : monad) : Type := Mixin {
  get : M S ;
  put : S -> M unit ;
  _ : forall s s', put s >> put s' = put s' ;
  _ : forall s, put s >> get = put s >> Ret s ;
  _ : get >>= put = skip ;
  _ : forall (A : Type) (k : S -> S -> M A),
    get >>= (fun s => get >>= k s) = get >>= fun s => k s s
}.
Record class_of S (m : Type -> Type) := Class {
  base : Monad.class_of m ; mixin : mixin_of S (Monad.Pack base) }.
Structure t S : Type := Pack { m : Type -> Type ; class : class_of S m }.
(* inheritance *)
Definition baseType S (M : t S) := Monad.Pack (base (class M)).
Module Exports.
Definition Get S (M : t S) : m M S :=
  let: Pack _ (Class _ (Mixin x _ _ _ _ _)) := M return m M S in x.
Arguments Get {S M} : simpl never.
Definition Put S (M : t S) : S -> m M unit :=
  let: Pack _ (Class _ (Mixin _ x _ _ _ _)) := M return S -> m M unit in x.
Arguments Put {S M} : simpl never.
Notation stateMonad := t.
Coercion baseType : stateMonad >-> monad.
Canonical baseType.
End Exports.
End MonadState.
Export MonadState.Exports.

Section state_lemmas.
Variables (S : Type) (M : stateMonad S).
Lemma putput s s' : Put s >> Put s' = Put s' :> M _.
Proof. by case: M => m [[[? ? ? ? []]]]. Qed.
Lemma putget s : Put s >> Get = Put s >> Ret s :> M _.
Proof. by case: M => m [[[? ? ? ? []]]]. Qed.
Lemma getputskip : Get >>= Put = skip :> M _.
Proof. by case: M => m [[[? ? ? ? []]]]. Qed.
Lemma getget (k : S -> S -> M S) :
 (Get >>= (fun s => Get >>= k s)) = (Get >>= fun s => k s s).
Proof. by case: M k => m [[[? ? ? ? []]]]. Qed.
End state_lemmas.

Lemma putgetput S {M : stateMonad S} x {B} (k : _ -> M B) :
  Put x >> Get >>= (fun x' => k x') = Put x >> k x :> M _.
Proof. by rewrite putget bindA bindretf. Qed.

Definition overwrite {A S} {M : stateMonad S} s a : M A :=
  Put s >> Ret a.

Example test_nonce0 (M : stateMonad nat) : M nat :=
  Get >>= (fun s => Put s.+1 >> Ret s).
(*Reset test_nonce0.
Fail Check test_nonce0.*)

Module MonadRun.
Record mixin_of S (M : monad) : Type := Mixin {
  run : forall A, M A -> S -> A * S ;
  _ : forall A (a : A) s, run (Ret a) s = (a, s) ;
  _ : forall A B (m : M A) (f : A -> M B) s,
      run (do a <- m ; f a) s =
      let: (a', s') := run m s in run (f a') s'
}.
Record class_of S (m : Type -> Type) := Class {
  base : Monad.class_of m ;
  mixin : mixin_of S (Monad.Pack base)
}.
Structure t S : Type := Pack { m : Type -> Type ;
  class : class_of S m }.
Definition baseType S (M : t S) := Monad.Pack (base (class M)).
Module Exports.
Definition Run S (M : t S) : forall A, m M A -> S -> A * S :=
  let: Pack _ (Class _ (Mixin x _ _)) := M
  return forall A, m M A -> S -> A * S in x.
Arguments Run {S M A} : simpl never.
Notation runMonad := t.
Coercion baseType : runMonad >-> monad.
Canonical baseType.
End Exports.
End MonadRun.
Export MonadRun.Exports.

Section run_lemmas.
Variables (S : Type) (M : runMonad S).
Lemma runret : forall A (a : A) s, Run (Ret a : M _) s = (a, s).
Proof. by case: M => m [? []]. Qed.
Lemma runbind : forall A B (ma : M A) (f : A -> M B) s,
  Run (do a <- ma ; f a) s = let: (a', s') := Run ma s in Run (f a') s'.
Proof. by case: M => m [? []]. Qed.
End run_lemmas.

Module MonadStateRun.
Record mixin_of S (M : runMonad S) (get : M S) (put : S -> M unit) : Type := Mixin {
  _ : forall s, Run get s = (s, s) ;
  _ : forall s s', Run (put s') s = (tt, s') ;
}.
Record class_of S (m : Type -> Type) := Class {
  base : MonadState.class_of S m ;
  base2 : MonadRun.mixin_of S (Monad.Pack (MonadState.base base)) ;
  mixin : @mixin_of S (MonadRun.Pack (MonadRun.Class base2)) (@Get _ (MonadState.Pack base)) (@Put _ (MonadState.Pack base)) ;
}.
Structure t S : Type := Pack { m : Type -> Type ;
  class : class_of S m }.
Definition baseType S (M : t S) := MonadState.Pack (base (class M)).
Module Exports.
Notation stateRunMonad := t.
Coercion baseType : stateRunMonad >-> stateMonad.
Canonical baseType.
Definition state_of_run S (M : stateRunMonad S) : runMonad S :=
  MonadRun.Pack (MonadRun.Class (base2 (class M))).
Canonical state_of_run.
End Exports.
End MonadStateRun.
Export MonadStateRun.Exports.

Section staterun_lemmas.
Variables (S : Type) (M : stateRunMonad S).
Lemma runget : forall s, Run (Get : M _) s = (s, s).
Proof. by case: M => m [? ? []]. Qed.
Lemma runput : forall s s', Run (Put s' : M _) s = (tt, s').
Proof. by case: M => m [? ? []]. Qed.
End staterun_lemmas.

Module MonadNondetState.
Record mixin_of (M : nondetMonad) : Type := Mixin {
  (* backtrackable state *)
  _ : BindLaws.right_zero (@Bind M) (@Fail _) ;
  (* composition distributes rightwards over choice *)
  _ : BindLaws.right_distributive (@Bind M) [~p]
}.
Record class_of S (m : Type -> Type) : Type := Class {
  base : MonadNondet.class_of m ;
  base2 : MonadState.mixin_of S (MonadFail.baseType (MonadNondet.baseType (MonadNondet.Pack base))) ;
  mixin : mixin_of (MonadNondet.Pack base)
}.
Structure t S : Type := Pack { m : Type -> Type ; class : class_of S m }.
Definition baseType S (M : t S) := MonadNondet.Pack (base (class M)).
Module Exports.
Notation nondetStateMonad := t.
Coercion baseType : nondetStateMonad >-> nondetMonad.
Canonical baseType.
Definition state_of_nondetstate S (M : nondetStateMonad S) :=
  MonadState.Pack (MonadState.Class (base2 (class M))).
Canonical state_of_nondetstate.
End Exports.
End MonadNondetState.
Export MonadNondetState.Exports.

Section nondetstate_lemmas.
Variables (S : Type) (M : nondetStateMonad S).
Lemma bindmfail : BindLaws.right_zero (@Bind M) (@Fail _).
Proof. by case: M => m [? ? [? ?]]. Qed.
Lemma alt_bindDr : BindLaws.right_distributive (@Bind M) (@Alt _).
Proof. by case: M => m [? ? []]. Qed.
End nondetstate_lemmas.

Lemma getput_prepend S (M : nondetStateMonad S) A (m : M A) :
  m = do x <- Get; (Put x >> m).
Proof. by rewrite -{2}(bindskipf m) -bindA getputskip 2!bindskipf. Qed.

Section state_commute.

Variables (S : Type) (M : nondetStateMonad S).

Lemma puttselectC (x : S) A (s : seq A) B (f : _ -> M B) :
  Put x >> (do rs <- tselect s; f rs) =
  do rs <- tselect s; Put x >> f rs.
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
  Put x >> (do rs <- select s; f rs) = do rs <- select s; Put x >> f rs.
Proof.
rewrite selectE {1}fmapE.
rewrite_ bindA.
rewrite puttselectC [in RHS]fmapE bindA.
bind_ext => x0; by rewrite 2!bindretf.
Qed.

Lemma gettselectC A (s : seq A) B (f : _ -> _ -> M B) :
  do ini <- Get; do rs <- tselect s; f rs ini =
  do rs <- tselect s; do ini <- Get; f rs ini.
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
transitivity (
  do x0 <- tselect (h' :: t);
  do x <- Get; f (x0.1, Tuple (monad.tselect_cons_statement_obligation_2 h H x0)) x).
 rewrite -IH; bind_ext => x.
 rewrite bindA;by rewrite_ bindretf.
rewrite bindA; bind_ext => y; by rewrite bindretf.
Qed.

(* perms is independent of the state and so commutes with put *)
Lemma putpermsC (x : S) A (s : seq A) B (f : _ -> M B) :
  Put x >> (do rs <- perms s; f rs) =
  do rs <- perms s; Put x >> f rs.
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
  do ini <- Get; (do rs <- perms s; f rs ini) =
  do rs <- perms s; do ini <- Get; f rs ini.
Proof.
move Hn : (size s) => n.
elim: n s Hn f => [|n IH] s Hn f.
  case: s Hn => // _; rewrite permsE.
  by rewrite bindretf; rewrite_ bindretf.
case: s Hn => // h t [Hn].
rewrite tpermsE bindA.
transitivity (do x <- tselect (h :: t); do ini <- Get; do rs <- perms x.2;
  f (x.1 :: rs) ini); last first.
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
apply/constructive_indefinite_description.
move: s; apply: (well_founded_induction (@well_founded_size _)) => s IH.
have {IH}IH : forall x, size x < size s ->
  { m | ndDenote m = unfoldM (@well_founded_size B) (@nilp _) f x}.
  move=> x xs; exact/constructive_indefinite_description/IH.
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
rewrite /assert /guard ltnS.
case: ifPn => b1b2; last by rewrite !bindfailf.
rewrite !bindskipf !bindretf /g.
case: Bool.bool_dec => // x2t.
case: (IH x2) => // x0 <-; by rewrite fmapE.
Qed.

(* definition 5.1, mu2017 *)
Definition commute {M : monad} A B (m : M A) (n : M B) C (f : A -> B -> M C) : Prop :=
  m >>= (fun x => n >>= (fun y => f x y)) = n >>= (fun y => m >>= (fun x => f x y)) :> M _.

(* theorem 5.2, mu2017 *)
Lemma commute_nondetState S (M : nondetStateMonad S)
  A (m : M A) B (n : M B) C (f : A -> B -> M C) :
  nondetState_sub m -> commute m n f.
Proof.
case => x.
elim: x m n f => [{A}A a m n f <-| B0 {A}A n0 H0 n1 H1 m n2 f <- |
  A0 m n f <- | A0 n0 H0 n1 H1 m n2 f <-].
- rewrite /commute bindretf.
  by rewrite_ bindretf.
- rewrite /commute /= !bindA.
  transitivity (do x <- ndDenote n0; do y <- n2; do x0 <- ndDenote (n1 x);
    f x0 y).
    bind_ext => s.
    by rewrite (H1 s).
  rewrite H0 //.
  bind_ext => b.
  by rewrite bindA.
- rewrite /commute /= bindfailf.
  transitivity (do y <- n; Fail : M C); first by rewrite bindmfail.
  bind_ext => b.
  by rewrite bindfailf.
- rewrite /commute /= alt_bindDl.
  transitivity (do y <- n2; (do x <- ndDenote n0 ; f x y) [~]
                           (do x <- ndDenote n1; f x y)); last first.
    bind_ext => a.
    by rewrite alt_bindDl.
  by rewrite alt_bindDr H0 // H1.
Qed.

(* section 4.2, mu2017 *)
Section loop.

Variables (A S : Type) (M : stateMonad S) (op : S -> A -> S).

Local Open Scope mu_scope.

Definition opmul x m : M _ :=
  Get >>= fun st => let st' := op st x in fmap (cons st') (Put st' >> m).

Definition loopp s xs : M (seq S) :=
  let mul x m := opmul x m in Put s >> foldr mul (Ret [::]) xs.

Lemma loopp_nil s : loopp s [::] = Put s >> Ret [::].
Proof. by []. Qed.

Lemma loopp_of_scanl_helper s
  (ms : M S) (mu mu' : M unit) (m : M (seq S)) (f : S -> M unit) :
  do x <- ms; mu >> (do xs <- fmap (cons s) (mu' >> m); f x >> Ret xs) =
  fmap (cons s) (do x <- ms; mu >> mu' >> (do xs <- m; f x >> Ret xs)).
Proof.
rewrite [in RHS]fmapE !bindA.
rewrite_ bindA.
bind_ext => s'.
rewrite !bindA; bind_ext; case.
rewrite bind_fmap bindA; bind_ext; case.
rewrite_ bindA.
by rewrite_ bindretf.
Qed.

(* theorem 4.1, mu2017 *)
Lemma loopp_of_scanl s xs :
  Ret (scanl op s xs) = do ini <- Get; loopp s xs >>= overwrite ini.
Proof.
elim: xs s => [/=|x xs IH] s.
  rewrite loopp_nil.
  rewrite_ bindA.
  rewrite_ bindretf.
  rewrite /overwrite.
  Inf rewrite -bindA.
  rewrite_ putput.
  by rewrite -bindA getputskip bindskipf.
rewrite /loopp /overwrite [in RHS]/=.
set mul := fun (a : A) m => _.
Inf rewrite !bindA.
(* TODO(rei): tactic for nested function bodies? *)
transitivity (do y <- Get; (Put s >> Get) >>= fun z =>
  do a <- fmap (cons (op z x)) (Put (op z x) >> foldr mul (Ret [::]) xs);
  Put y >> Ret a); last by Inf rewrite !bindA.
rewrite_ putget.
rewrite_ bindA.
rewrite_ bindretf.
rewrite loopp_of_scanl_helper.
transitivity (fmap (cons (op s x)) (do y <- Get; Put (op s x) >>
  (do a <- foldr mul (Ret [::]) xs; Put y >> Ret a))); last first.
  congr (fmap _ _); by rewrite_ putput.
transitivity (fmap (cons (op s x))
  (do y <- Get; loopp (op s x) xs >>= overwrite y)); last first.
  congr (fmap _ _); by Inf rewrite -bindA.
by rewrite -IH fmapE bindretf.
Qed.

End loop.

Section section_51. (* mu2017 *)

Variables (S : Type) (M : nondetStateMonad S).
Variables (A : Type) (op : S -> A -> S) (ok : pred S).

Lemma assert_all_scanl s (xs : seq A) :
  assert (all ok \o scanl op s) xs =
  Get >>= (fun ini => loopp _ op s xs >>=
    (fun ys => guard (all ok ys) >> Ret xs >>= overwrite ini)) :> M _.
Proof.
rewrite /assert.
rewrite guardsC; last exact: bindmfail.
transitivity (Get >>= (fun ini => loopp _ op s xs >>= overwrite ini >>=
    (fun ys => guard (all ok ys) >> Ret xs) : M _)).
  by rewrite -!bindA -loopp_of_scanl bindA !bindretf.
bind_ext => st.
rewrite bindA; bind_ext => xs'.
rewrite [in RHS]bindA [in RHS]guardsC; last exact: bindmfail.
rewrite bindA bindretf.
rewrite /overwrite 2!bindA; bind_ext; case.
by rewrite 2!bindretf.
Qed.

Local Open Scope mu_scope.

Lemma put_foldr st x xs :
  Put (op st x) >> (do x1 <- foldr (opmul op) (Ret [::]) xs;
    guard (all ok x1) >> guard (ok (op st x))) =
  guard (ok (op st x)) >> (Put (op st x) >>
    (do ys <- foldr (opmul op) (Ret [::]) xs; guard (all ok ys))) :> M _.
Proof.
elim: xs x => [x|h t _ x].
  rewrite /= bindretf /= bindskipf /= bindretf (_ : guard (_ _ [::]) = skip) //.
  rewrite bindmskip /guard; case: ifPn => H.
  - by rewrite bindskipf bindmskip.
  - by rewrite bindmfail bindfailf.
rewrite /= !bindA.
transitivity (Put (op st x) >>
  (do x0 <- Get; do x1 <- let st' := op x0 h in
    fmap (cons st') (Put st' >> foldr (opmul op) (Ret [::]) t);
    guard (ok (op st x)) >> guard (all ok x1)) : M _).
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

(* mu2017 *)
Lemma theorem_53 (xs : seq A) :
  foldr (opmul op) (Ret [::]) xs >>=
    (fun ys => guard (all ok ys) >> Ret xs) = foldr opdot (Ret [::]) xs.
Proof.
elim: xs => [|x xs IH]; first by rewrite /= bindretf /= bindskipf.
rewrite [in LHS]/=.
rewrite {1}/opmul.
rewrite {1}bindA.
transitivity (do x0 <- Get;
  Put (op x0 x) >> foldr (opmul op) (Ret [::]) xs >>= (fun ys =>
  guard (all ok (op x0 x :: ys))) >> Ret (x :: xs) : M _).
  bind_ext => st.
  by rewrite bind_fmap !bindA.
transitivity (do x0 <- Get;
  Put (op x0 x) >> foldr (opmul op) (Ret [::]) xs >>= (fun ys =>
  guard (all ok ys) >> guard (ok (op x0 x))) >> Ret (x :: xs) : M _).
  bind_ext => st.
  rewrite !bindA.
  bind_ext; case.
  bind_ext => ys.
  rewrite -guard_and.
  congr (guard _ >> _).
  by rewrite -cat1s all_cat andbC all_seq1.
transitivity (do st <- Get; guard (ok (op st x)) >>
  Put (op st x) >> foldr (opmul op) (Ret [::]) xs >>= (fun ys =>
   guard (all ok ys)) >> Ret (x :: xs) : M _).
  bind_ext => st.
  rewrite -!bindA.
  congr (_ >> _).
  rewrite !bindA.
  by rewrite put_foldr.
transitivity (do st <- Get; guard (ok (op st x)) >>
  Put (op st x) >>
    fmap (cons x) (foldr (opmul op) (Ret [::]) xs >>= (fun ys =>
   guard (all ok ys)) >> Ret xs) : M _).
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

End section_51.

(* TODO: move? *)
Definition intersect {A : eqType} (s t : seq A) : seq A := filter (mem s) t.

Lemma nilp_intersect (A : eqType) (s t : seq A) :
  nilp (intersect s t) = ~~ has (mem s) t.
Proof. by rewrite /intersect /nilp size_filter has_count lt0n negbK. Qed.

Definition seq_disjoint {A : eqType} : pred [eqType of (seq A)`2] :=
  (@nilp _) \o uncurry intersect.

Lemma intersect0s (A : eqType) (s : seq A) : intersect [::] s = [::].
Proof. by elim: s. Qed.

Module MonadFresh.
Record mixin_of (S : eqType) (m : Type -> Type) : Type := Mixin {
  fresh : m S }.
Record class_of S (m : Type -> Type) : Type := Class {
  base : Monad.class_of m ;
  mixin : mixin_of S m }.
Structure t S := Pack { m : Type -> Type ; class : class_of S m }.
Definition baseType S (M : t S) := Monad.Pack (base (class M)).
Module Exports.
Definition Fresh S (M : t S) : m M S :=
  let: Pack _ (Class _ (Mixin x)) := M return m M S in x.
Arguments Fresh {S M} : simpl never.
Notation freshMonad := t.
Coercion baseType : freshMonad >-> monad.
Canonical baseType.
End Exports.
End MonadFresh.
Export MonadFresh.Exports.

Definition promotable A (p : pred (seq A)) (q : pred (seq A * seq A)) :=
  forall s t, p s -> p t -> p (s ++ t) = q (s, t).

Module segment_closed.
Record t A := mk {
  p : pred (seq A) ;
  H : forall a b, p (a ++ b) -> p a /\ p b }.
End segment_closed.
Definition segment_closed_p A := @segment_closed.p A.
Coercion segment_closed_p : segment_closed.t >-> pred.

Lemma segment_closed_suffix A (p : segment_closed.t A) s :
  ~~ p s -> forall t, ~~ p (s ++ t).
Proof. move=> ps t; apply: contra ps; by case/segment_closed.H. Qed.

Lemma segment_closed_prefix A (p : segment_closed.t A) s :
  ~~ p s -> forall t, ~~ p (t ++ s).
Proof. move=> ps t; apply: contra ps; by case/segment_closed.H. Qed.

(* assert p distributes over concatenation *)
Definition promote_assert (M : failMonad) A
  (p : pred (seq A)) (q : pred (seq A * seq A)) :=
  (bassert p) \o (M # ucat) \o mpair =
  (M # ucat) \o (bassert q) \o mpair \o (bassert p)^`2 :> (_ -> M _).

Lemma promote_assert_sufficient_condition (M : failMonad) A :
  BindLaws.right_zero (@Bind M) (@Fail _) ->
  forall (p : segment_closed.t A) q, promotable p q ->
  promote_assert M p q.
Proof.
move=> right_z p q promotable_pq.
rewrite /promote_assert funeqE => -[x1 x2].
rewrite 3![in RHS]compE -/(fmap _ _) [in RHS]fmapE.
rewrite 2![in LHS]compE {1}/bassert [in LHS]bind_fmap !bindA.
bind_ext => s.
rewrite 2!bindA bindretf 2!bindA.
rewrite {1}[in RHS]/guard.
case: ifPn => ps; last first.
  rewrite bindfailf.
  rewrite_ bindretf.
  With (idtac) Open (X in _ >>= X).
    rewrite /assert /guard /= (negbTE (segment_closed_suffix ps x)) bindfailf.
    reflexivity.
  by rewrite right_z.
rewrite bindskipf; bind_ext => t.
rewrite bindretf.
rewrite_ bindretf.
rewrite bindA {1}[in RHS]/guard.
case: ifPn => pt; last first.
  by rewrite bindfailf /assert /guard /= (negbTE (segment_closed_prefix pt s)) bindfailf.
by rewrite bindskipf bindretf bindA bindretf /= /assert promotable_pq.
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

Module MonadFailFresh.
Record mixin_of S (M : failMonad) (fresh : M S) : Type := Mixin {
  symbols := fun n => sequence (nseq n fresh);
  (* generated symbols are indeed fresh (specification of fresh) *)
  distinct : segment_closed.t S ;
  _ : bassert distinct \o symbols = symbols ;
  (* failure is a right zero of composition (backtracking interpretation) *)
  _ : BindLaws.right_zero (@Bind M) (@Fail _)
}.
Record class_of S (m : Type -> Type) := Class {
  base : MonadFail.class_of m ;
  mixin : MonadFresh.mixin_of S m ;
  ext : @mixin_of S (MonadFail.Pack base) (MonadFresh.fresh mixin)
}.
Structure t S : Type := Pack { m : Type -> Type ; class : class_of S m }.
Definition baseType S (M : t S) := MonadFail.Pack (base (class M)).
Module Exports.
Definition Symbols S (M : t S) :=
  let: Pack _ (Class _ _ (Mixin x _ _ _)) := M return nat -> m M (seq S) in x.
Arguments Symbols {S M} : simpl never.
Definition Distinct S (M : t S) :=
  let: Pack _ (Class _ _ (Mixin _ x _ _)) := M return segment_closed.t S in x.
Arguments Distinct {S} M : simpl never.
Notation failFreshMonad := t.
Coercion baseType : failFreshMonad >-> failMonad.
Canonical baseType.
Definition fresh_of_failfresh S (M : failFreshMonad S) : MonadFresh.t S :=
  @MonadFresh.Pack _ (MonadFailFresh.m M)
  (MonadFresh.Class (Monad.class (MonadFail.baseType (baseType M)))
                    (mixin (class M))).
Canonical fresh_of_failfresh.
End Exports.
End MonadFailFresh.
Export MonadFailFresh.Exports.

Section failfresh_lemmas.
Variables (S : eqType) (M : failFreshMonad S).
Lemma failfresh_bindmfail : BindLaws.right_zero (@Bind M) (@Fail _).
Proof. by case: M => m [? ? []]. Qed.
Lemma bassert_symbols : bassert (Distinct M) \o Symbols = Symbols :> (nat -> M _).
Proof. by case: M => m [? ? []]. Qed.
End failfresh_lemmas.

Section properties_of_Symbols.
Variables (A : eqType) (M : failFreshMonad A).

Lemma SymbolsE : Symbols = (fun n => sequence (nseq n Fresh)) :> (_ -> M _).
Proof. by case: M => m [? ? [? ? ? ?]]. Qed.

Lemma Symbols0 : Symbols 0 = Ret [::] :> M _.
Proof. by rewrite SymbolsE. Qed.

Lemma SymbolsS n : Symbols n.+1 =
  do x <- Fresh ; do xs <- Symbols n : M _; Ret (x :: xs).
Proof. by rewrite SymbolsE. Qed.

Lemma Symbols_prop1 :
  Symbols \o const 1 = (M # wrap) \o const Fresh :> (A -> M _).
Proof.
rewrite funeqE => n.
transitivity (@Symbols _ M 1) => //.
rewrite SymbolsE sequence_cons sequence_nil.
rewrite_ bindretf.
by rewrite compE -/(fmap _ _) [in RHS]fmapE.
Qed.

Lemma Symbols_prop2 :
  Symbols \o uaddn = (M # ucat) \o mpair \o (Symbols : _ -> M _)^`2.
Proof.
rewrite funeqE => -[n1 n2].
elim: n1 => [|n1 IH].
  rewrite [in LHS]compE uaddnE add0n.
  rewrite compE [in X in _ = _ X]/= squaringE Symbols0.
  rewrite compE -/(fmap _ _) [in RHS]fmapE bindA bindretf.
  rewrite -fmapE fmap_bind.
  Open (X in _ >>= X).
    rewrite fcompE fmapE bindretf /=; reflexivity.
  by rewrite bindmret.
rewrite compE uaddnE addSn SymbolsS -uaddnE -(compE Symbols) {}IH.
rewrite [in RHS]compE [in X in _ = _ X]/= squaringE SymbolsS.
rewrite [in RHS]compE -/(fmap _ _) fmap_bind bindA; bind_ext => a.
rewrite 2![in LHS]compE -/(fmap _ _) [in LHS]fmap_bind [in LHS]bindA [in RHS]bindA.
(* TODO(rei): bind_ext? *)
congr Bind; rewrite funeqE => s.
rewrite [in RHS]bindretf [in RHS]fcompE [in RHS]fmap_bind.
rewrite [in LHS]fcompE [in LHS]bind_fmap [in LHS]bindA.
rewrite_ bindretf.
rewrite_ fcompE.
rewrite_ fmapE.
by rewrite_ bindretf.
Qed.

End properties_of_Symbols.

Module MonadArray.
Record mixin_of S (I : eqType) (M : monad) : Type := Mixin {
  get : I -> M S ;
  put : I -> S -> M unit ;
  _ : forall i s s', put i s >> put i s' = put i s' ;
  _ : forall i s (A : Type) (k : S -> M A), put i s >> get i >>= k =
      put i s >> k s ;
  _ : forall i, get i >>= put i = skip ;
  _ : forall i (A : Type) (k : S -> S -> M A),
    get i >>= (fun s => get i >>= k s) = get i >>= fun s => k s s ;
  _ : forall i j (A : Type) (k : S -> S -> M A),
    get i >>= (fun u => get j >>= (fun v => k u v)) =
    get j >>= (fun v => get i >>= (fun u => k u v)) ;
  _ : forall i j u v, (i != j) \/ (u = v) ->
    put i u >> put j v = put j v >> put i u ;
  _ : forall i j u (A : Type) (k : S -> M A), i != j ->
    put i u >> get j >>= k =
    get j >>= (fun v => put i u >> k v)
}.
Record class_of S (I : eqType) (m : Type -> Type) := Class {
  base : Monad.class_of m ; mixin : mixin_of S I (Monad.Pack base) }.
Structure t S (I : eqType) : Type :=
  Pack { m : Type -> Type ; class : class_of S I m }.
(* inheritance *)
Definition baseType S I (M : t S I) := Monad.Pack (base (class M)).
Module Exports.
Definition aGet S I (M : t S I) : I -> m M S :=
  let: Pack _ (Class _ (Mixin x _ _ _ _ _ _ _ _)) := M return I -> m M S in x.
Arguments aGet {S I M} : simpl never.
Definition aPut S I (M : t S I) : I -> S -> m M unit :=
  let: Pack _ (Class _ (Mixin _ x _ _ _ _ _ _ _ )) := M
    return I -> S -> m M unit in x.
Arguments aPut {S I M} : simpl never.
Notation arrayMonad := t.
Coercion baseType : arrayMonad >-> monad.
Canonical baseType.
End Exports.
End MonadArray.
Export MonadArray.Exports.

Section monadarray_lemmas.
Variables (S : Type) (I : eqType) (M : arrayMonad S I).
Lemma aputput i s s' : aPut i s >> aPut i s' = aPut i s' :> M _.
Proof. by case: M => ? [? []]. Qed.
Lemma aputget i s A (k : S -> M A) : aPut i s >> aGet i >>= k =
    aPut i s >> k s :> M _.
Proof. by case: M k => ? [? []]. Qed.
Lemma agetputskip i : aGet i >>= aPut i = skip :> M _.
Proof. by case: M => ? [? []]. Qed.
Lemma agetget i A (k : S -> S -> M A) :
  aGet i >>= (fun s => aGet i >>= k s) = aGet i >>= fun s => k s s.
Proof. by case: M k => ? [? []]. Qed.
Lemma agetC i j A (k : S -> S -> M A) :
  aGet i >>= (fun u => aGet j >>= (fun v => k u v)) =
  aGet j >>= (fun v => aGet i >>= (fun u => k u v)).
Proof. by case: M k => ? [? []]. Qed.
Lemma aputC i j u v : i != j \/ u = v ->
  aPut i u >> aPut j v = aPut j v >> aPut i u :> M _.
Proof. by case: M i j u v => ? [? []]. Qed.
Lemma aputgetC i j u A (k : S -> M A) : i != j ->
  aPut i u >> aGet j >>= (fun v => k v) =
  aGet j >>= (fun v => aPut i u >> k v).
Proof. by case: M i j u A k => ? [? []]. Qed.
End monadarray_lemmas.

Section monadarray_example.

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
