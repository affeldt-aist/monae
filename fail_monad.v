From mathcomp Require Import all_ssreflect.
From mathcomp Require boolp.
Require Import monae_lib monad.

(* Contents:
- Module MonadFail.
    definition of guard
- Module MonadAlt.
    non-deterministic choice
  Section subsequences_of_a_list.
  Section permutation_and_insertion.
    examples of non-deterministic programs
- Module MonadAltCI.
- Module MonadNondet
  Section permutations.
- Section nondet_insert.
- Module MonadCINondet.
- Module MonadExcept.
    example of the fast product

wip (to go to another file):
- Module MonadContinuation.
- Module MonadShiftReset.
- Module MonadJump.
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.

Module MonadFail.
Record mixin_of (M : monad) : Type := Mixin {
  fail : forall A, M A ;
  (* exceptions are left-zeros of sequential composition *)
  _ : BindLaws.left_zero (@Bind M) fail (* fail A >>= f = fail B *)
}.
Record class_of (m : Type -> Type) := Class {
  base : Monad.class_of m ; mixin : mixin_of (Monad.Pack base) }.
Structure t := Pack { m : Type -> Type ; class : class_of m }.
Definition baseType (M : t) := Monad.Pack (base (class M)).
Module Exports.
Definition Fail (M : t) : forall A, m M A :=
  let: Pack _ (Class _ (Mixin x _)) := M return forall A, m M A in x.
Arguments Fail {M A} : simpl never.
Notation failMonad := t.
Coercion baseType : failMonad >-> monad.
Canonical baseType.
End Exports.
End MonadFail.
Export MonadFail.Exports.

Section fail_lemmas.
Variable (M : failMonad).
Lemma bindfailf : BindLaws.left_zero (@Bind M) (@Fail _).
Proof. by case : M => m [? []]. Qed.
End fail_lemmas.

Lemma fmap_fail {A B} (M : failMonad) (f : A -> B) : (M # f) Fail = Fail.
Proof. by rewrite fmapE bindfailf. Qed.

Section guard_assert.

Variable M : failMonad.

Definition guard (b : bool) : M unit := locked (if b then skip else Fail).

Lemma guardPn (b : bool) : if_spec b skip Fail (~~ b) b (guard b).
Proof. by rewrite /guard; unlock; case: ifPn => ?; constructor. Qed.

Lemma guardT : guard true = skip. Proof. by rewrite /guard; unlock. Qed.

Lemma guardF : guard false = Fail. Proof. by rewrite /guard; unlock. Qed.

(* guard distributes over conjunction *)
Lemma guard_and a b : guard (a && b) = guard a >> guard b.
Proof.
move: a b => -[|] b /=; by [rewrite guardT bindskipf | rewrite guardF bindfailf].
Qed.

Definition assert {A} (p : pred A) (a : A) : M A :=
  locked (guard (p a) >> Ret a).

Lemma assertE {A} (p : pred A) (a : A) : assert p a = guard (p a) >> Ret a.
Proof. by rewrite /assert; unlock. Qed.

Lemma assertT {A} (a : A) : assert xpredT a = Ret a :> M _.
Proof. by rewrite assertE guardT bindskipf. Qed.

Lemma assertF {A} (a : A) : assert xpred0 a = Fail :> M _.
Proof. by rewrite assertE guardF bindfailf. Qed.

Lemma assertPn {A} (p : pred A) (a : A) :
  if_spec (p a) (Ret a) Fail (~~ (p a)) (p a) (assert p a).
Proof.
rewrite assertE; case: guardPn => pa;
  by [rewrite bindskipf; constructor | rewrite bindfailf; constructor].
Qed.

Definition bassert {A} (p : pred A) (m : M A) : M A := m >>= assert p.

(* follows from guards commuting with anything *)
Lemma commutativity_of_assertions A q :
  Join \o (M # (bassert q)) = bassert q \o Join :> (_ -> M A).
Proof.
by rewrite boolp.funeqE => x; rewrite !compE join_fmap /bassert joinE bindA.
Qed.

(* guards commute with anything *)
Lemma guardsC (HM : BindLaws.right_zero (@Bind M) (@Fail _)) b B (m : M B) :
  guard b >> m = m >>= assert (fun=> b).
Proof.
case: guardPn => Hb.
  rewrite bindskipf.
  rewrite /assert; unlock; rewrite guardT.
  rewrite_ bindskipf.
  by rewrite bindmret.
rewrite /assert; unlock; rewrite guardF.
rewrite_ bindfailf.
by rewrite bindfailf HM.
Qed.

End guard_assert.
Arguments assert {M} {A}.
Arguments guard {M}.

Lemma well_founded_size A : well_founded (fun x y : seq A => size x < size y).
Proof. by apply: (@Wf_nat.well_founded_lt_compat _ size) => ? ? /ltP. Qed.

Definition bassert_hylo {M : failMonad} A B
  (f : B -> M (A * B)%type) (p : pred B) (r : forall p f, B -> B -> bool) :=
  forall b, f b = bassert (fun z => r p f z.2 b) (f b).

Definition bassert_size {M : failMonad} A B
  (f : seq B -> M (A * seq B)%type) :=
  @bassert_hylo M _ _ f predT (fun _ _ x y => size x < size y).

Section foldM.
Variables (M : monad) (T R : Type) (f : R -> T -> M R).
Fixpoint foldM z s : M _ := if s is x :: s' then f z x >>= (fun y => foldM y s') else (Ret z).
End foldM.

Section unfoldM.

Local Open Scope mprog.

Section unfoldM_monad.
Variables (M : monad) (A B : Type).
Variable (r : B -> B -> bool).
Hypothesis wfr : well_founded r.
Variables (p : pred B) (f : B -> M (A * B)%type).

Definition unfoldM' (y : B) (g : forall y' : B, r y' y -> M (seq A)) : M (seq A) :=
  if p y then Ret [::] else f y >>=
    (fun xz => match Bool.bool_dec (r xz.2 y) true with
            | left H => fmap (cons xz.1) (g xz.2 H)
            | right H => Ret [::]
            end).
(* superfluous match to define the "recursive" call,
   to be removed by unfoldME under hypo. *)

Definition unfoldM := Fix wfr (fun _ => _ _) unfoldM'.

End unfoldM_monad.

Section unfoldM_failMonad.
Variables (M : failMonad) (A B' : Type).
Let B := seq B'.
Notation unfoldM := (@unfoldM M A _ _ (@well_founded_size B')).
Variables (p : pred B) (f : B -> M (A * B)%type).

Hypothesis decr_size : bassert_size f.

Lemma unfoldME y : unfoldM p f y =
  if p y then Ret [::]
  else f y >>= (fun xz => fmap (cons xz.1) (unfoldM p f xz.2)).
Proof.
rewrite /unfoldM Fix_eq; last first.
  move => b g g' H; rewrite /unfoldM'; case: ifPn => // pb.
  bind_ext => -[a' b'] /=.
  destruct Bool.bool_dec => //; by rewrite H.
rewrite /unfoldM'; case: ifPn => // py.
rewrite decr_size /bassert 2!bindA; bind_ext => -[a' b'].
case: assertPn => b'y; last by rewrite 2!bindfailf.
by rewrite 2!bindretf /= b'y.
Qed.

End unfoldM_failMonad.

End unfoldM.
Arguments unfoldM : simpl never.

(* section 5.1, mu2019tr3 *)
Section hyloM.
Variables (M : failMonad) (A B C : Type).
Variables (op : A -> M C -> M C) (e : C) (p : pred B) (f : B -> M (A * B)%type).
Variable seed : forall (p : pred B) (f : B -> M (A * B)%type), B -> B -> bool.

Definition hyloM' (y : B) (g : forall y', seed p f y' y -> M C) : M C :=
  if p y then Ret e else f y >>=
    (fun xz => match Bool.bool_dec (seed p f xz.2 y) true with
            | left H => op xz.1 (g xz.2 H)
            | right H => Ret e
            end).

Hypothesis well_founded_seed : well_founded (seed p f).

Definition hyloM := Fix well_founded_seed (fun _ => M _) hyloM'.

Hypothesis Hdecr_seed : bassert_hylo f p seed.

Lemma hyloME y : hyloM y = if p y then
                             Ret e
                           else
                             f y >>= (fun xz => op xz.1 (hyloM xz.2)).
Proof.
rewrite /hyloM Fix_eq; last first.
  move => b g g' K; rewrite /hyloM'; case: ifPn => // pb.
  bind_ext => -[a' b'] /=.
  destruct Bool.bool_dec => //.
  by rewrite K.
rewrite {1}/hyloM'; case: ifPn => // py.
rewrite Hdecr_seed /bassert !bindA.
bind_ext => -[b' a'].
case: assertPn => Hseed; last by rewrite 2!bindfailf.
by rewrite 2!bindretf Hseed.
Qed.

End hyloM.
Arguments hyloM {M} {A} {B} {C} _ _ _ _ _.

Module MonadAlt.
Record mixin_of (M : monad) : Type := Mixin {
  alt : forall A, M A -> M A -> M A ;
  _ : forall A, associative (@alt A) ;
  (* composition distributes leftwards over choice *)
  _ : BindLaws.left_distributive (@Bind M) alt
  (* in general, composition does not distribute rightwards over choice *)
  (* NB: no bindDr to accommodate both angelic and demonic interpretations of nondeterminism *)
}.
Record class_of (m : Type -> Type) : Type := Class {
  base : Monad.class_of m ; mixin : mixin_of (Monad.Pack base) }.
Structure t := Pack { m : Type -> Type ; class : class_of m }.
Definition baseType (M : t) := Monad.Pack (base (class M)).
Module Exports.
Definition Alt M : forall A, m M A -> m M A -> m M A :=
  let: Pack _ (Class _ (Mixin x _ _)) := M
  return forall A, m M A -> m M A -> m M A in x.
Arguments Alt {M A} : simpl never.
Notation "'[~p]'" := (@Alt _). (* prefix notation *)
Notation "x '[~]' y" := (Alt x y). (* infix notation *)
Notation altMonad := t.
Coercion baseType : altMonad >-> monad.
Canonical baseType.
End Exports.
End MonadAlt.
Export MonadAlt.Exports.

Section monadalt_lemmas.
Variable (M : altMonad).
Lemma alt_bindDl : BindLaws.left_distributive (@Bind M) [~p].
Proof. by case: M => m [? []]. Qed.
Lemma altA : forall A, associative (@Alt M A).
Proof. by case: M => m [? []]. Qed.

(* TODO: name ok? *)
Lemma naturality_nondeter A B (f : A -> B) (p q : M _):
  (M # f) (p [~] q) = (M # f) p [~] (M # f) q.
Proof. by rewrite 3!fmapE alt_bindDl. Qed.

Lemma alt_fmapDl A B (f : A -> B) (m1 m2 : M A) :
  (M # f) (m1 [~] m2) = (M # f) m1 [~] (M # f) m2.
Proof. by rewrite 3!fmapE alt_bindDl. Qed.

End monadalt_lemmas.

Section arbitrary.

Variables (M : altMonad) (A : Type) (def : A).

Definition arbitrary : seq A -> M A :=
  foldr1 (Ret def) (fun x y => x [~] y) \o map Ret.

End arbitrary.
Arguments arbitrary {M} {A}.

(* Sect. 3.1, gibbons2012utp *)
Section subsequences_of_a_list.
Local Open Scope mprog.

Variables (M : altMonad) (A : Type).

Fixpoint subs (s : seq A) : M (seq A) :=
  if s isn't h :: t then Ret [::] else
  let t' := subs t in
  fmap (cons h) t' [~] t'.

Fixpoint SUBS (s : seq A) : Functor.m (Monad.baseType (MonadAlt.baseType M)) _ :=
  if s isn't h :: t then Ret [::] else
  let t' : Functor.m (Monad.baseType (MonadAlt.baseType M)) _ := SUBS t in
  Alt (((MonadAlt.baseType M) # (cons h)) t') t'.

Goal subs = SUBS. by []. Abort.

Lemma subs_cons x (xs : seq A) :
  subs (x :: xs) = let t' := subs xs in fmap (cons x) t' [~] t'.
Proof. by []. Qed.

Lemma subs_cat (xs ys : seq A) :
  (subs (xs ++ ys) = do us <- subs xs; do vs <- subs ys; Ret (us ++ vs))%Do.
Proof.
elim: xs ys => [ys |x xs IH ys].
  by rewrite cat0s /= bindretf bindmret.
rewrite {1}[in RHS]/subs fmapE -/(subs _) alt_bindDl bindA.
Open (X in subs xs >>= X).
  rewrite bindretf.
  rewrite_ cat_cons.
  reflexivity.
rewrite [X in _ = X [~] _](_ : _ = fmap (cons x) (do x0 <- subs xs; do x1 <- subs ys; Ret (x0 ++ x1)))%Do; last first.
  rewrite fmapE bindA.
  bind_ext => x0.
  rewrite bindA.
  by rewrite_ bindretf.
by rewrite -IH cat_cons subs_cons.
Qed.

End subsequences_of_a_list.

(* mu2019tr2, Sect. 3 *)
Section permutation_and_insertion.
Variable M : altMonad.
Local Open Scope mprog.

Fixpoint insert {A} (a : A) (s : seq A) : M (seq A) :=
  if s isn't h :: t then Ret [:: a] else
  Ret (a :: h :: t) [~] fmap (cons h) (insert a t).
Arguments insert : simpl never.

Lemma insertE A (a : A) s :
  insert a s = if s isn't h :: t then Ret [:: a] else
  Ret (a :: h :: t) [~] fmap (cons h) (insert a t).
Proof. by case: s. Qed.

Fixpoint perm {A} (s : seq A) : M (seq A) :=
  if s isn't h :: t then Ret [::] else perm t >>= insert h.

(* see also netys2017 *)
Lemma insert_map A B (f : A -> B) (a : A) :
  insert (f a) \o map f = map f (o) insert a :> (_ -> M _).
Proof.
rewrite boolp.funeqE; elim => [|y xs IH].
  by rewrite fcompE insertE -(compE (fmap (map f))) (natural RET) compE insertE.
apply/esym.
rewrite fcompE insertE alt_fmapDl.
(* first branch *)
rewrite -(compE (fmap (map f))) (natural RET) FIdf [ in X in X [~] _ ]/=.
(* second branch *)
rewrite -fmap_oE (_ : map f \o cons y = cons (f y) \o map f) //.
by rewrite fmap_oE -(fcompE (map f)) -IH [RHS]/= insertE.
Qed.

(* lemma 3.3 in mu2019tr2 *)
Lemma perm_o_map A B (f : A -> B) :
  perm \o map f = map f (o) perm :> (seq A -> M (seq B)).
Proof.
rewrite boolp.funeqE; elim => [/=|x xs IH].
  by rewrite fcompE [perm _]/= -[in RHS]compE (natural RET).
by rewrite fcompE [in perm _]/= fmap_bind -insert_map -bind_fmap -fcompE -IH.
Qed.

End permutation_and_insertion.
Arguments insert {M} {A} : simpl never.
Arguments perm {M} {A}.

Section perm_filter.
Variable M : altMonad.
Hypothesis altmm : forall A, idempotent (@Alt _ A : M A -> M A -> M A).

Local Open Scope mprog.

Variables (A : Type) (p : pred A).

Lemma filter_insertN a : ~~ p a ->
  forall s, (filter p (o) insert a) s = Ret (filter p s) :> M _.
Proof.
move=> pa; elim => [|h t IH].
  by rewrite fcompE insertE -(compE (fmap _)) (natural RET) FIdf /= (negbTE pa).
rewrite fcompE insertE alt_fmapDl.
rewrite -(compE (fmap _)) (natural RET) FIdf [in X in X [~] _]/= (negbTE pa).
case: ifPn => ph.
- rewrite -fmap_oE (_ : filter p \o cons h = cons h \o filter p); last first.
    rewrite boolp.funeqE => x /=; by rewrite ph.
  rewrite fmap_oE.
  move: (IH); rewrite fcompE => ->.
  by rewrite fmapE /= ph bindretf /= altmm.
- rewrite -fmap_oE (_ : filter p \o cons h = filter p); last first.
    rewrite boolp.funeqE => x /=; by rewrite (negbTE ph).
  move: (IH); rewrite fcompE => -> /=; by rewrite (negbTE ph) altmm.
Qed.

Lemma filter_insertT a : p a ->
  filter p (o) insert a = insert a \o filter p :> (_ -> M _).
Proof.
move=> pa; rewrite boolp.funeqE; elim => [|h t IH].
  by rewrite fcompE !insertE fmapE bindretf /= pa.
rewrite fcompE [in RHS]/=; case: ifPn => ph.
- rewrite [in RHS]insertE.
  move: (IH); rewrite [in X in X -> _]/= => <-.
  rewrite [in LHS]insertE alt_fmapDl; congr (_ [~] _).
    by rewrite fmapE bindretf /= pa ph.
  rewrite !fmapE /= fcompE bind_fmap bindA.
  rewrite_ bindretf.
  by rewrite /= ph.
- rewrite [in LHS]insertE alt_fmapDl.
  rewrite -[in X in _ [~] X = _]fmap_oE.
  rewrite (_ : (filter p \o cons h) = filter p); last first.
    by rewrite boolp.funeqE => x /=; rewrite (negbTE ph).
  move: (IH); rewrite fcompE => ->.
  rewrite fmapE bindretf /= pa (negbTE ph) [in RHS]insertE; case: (filter _ _) => [|h' t'].
    by rewrite insertE altmm.
  by rewrite !insertE altA altmm.
Qed.

(* netys2017 *)
Lemma perm_filter : perm \o filter p = filter p (o) perm :> (_ -> M _).
Proof.
rewrite boolp.funeqE; elim => [|h t /= IH].
  by rewrite fcompE fmapE bindretf.
case: ifPn => ph.
  rewrite [in LHS]/= IH [in LHS]fcomp_def compE [in LHS]bind_fmap.
  rewrite [in RHS]fcomp_def compE -/(fmap _ _) [in RHS]fmap_bind; bind_ext => s.
  by rewrite filter_insertT.
rewrite fcompE fmap_bind IH fcompE fmapE; bind_ext => s.
by rewrite filter_insertN.
Qed.

End perm_filter.

Module MonadAltCI.
Record mixin_of (M : Type -> Type) (op : forall A, M A -> M A -> M A) : Type := Mixin {
  _ : forall A, idempotent (op A) ;
  _ : forall A, commutative (op A)
}.
Record class_of (m : Type -> Type) : Type := Class {
  base : MonadAlt.class_of m ;
  mixin : mixin_of (@Alt (MonadAlt.Pack base)) }.
Structure t := Pack { m : Type -> Type ; class : class_of m }.
Definition baseType (M : t) := MonadAlt.Pack (base (class M)).
Module Exports.
Notation altCIMonad := t.
Coercion baseType : altCIMonad >-> altMonad.
Canonical baseType.
End Exports.
End MonadAltCI.
Export MonadAltCI.Exports.

Section altci_lemmas.
Variable (M : altCIMonad).
Lemma altmm : forall A, idempotent (@Alt _ A : M A -> M A -> M A).
Proof. by case: M => m [? []]. Qed.
Lemma altC : forall A, commutative (@Alt _ A : M A -> M A -> M A).
Proof. by case: M => m [? []]. Qed.
Lemma altCA A : @left_commutative (M A) (M A) (fun x y => x [~] y).
Proof. move=> x y z. by rewrite altA altC altA altC (altC z). Qed.
Lemma altAC A : @right_commutative (M A) (M A) (fun x y => x [~] y).
Proof. move=> x y z; by rewrite altC altA (altC x). Qed.
Lemma altACA A : @interchange (M A) (fun x y => x [~] y) (fun x y => x [~] y).
Proof. move=> x y z t; rewrite !altA; congr (_ [~] _); by rewrite altAC. Qed.
End altci_lemmas.

(* mu2019tr2, Sect. 3, see also netsys2017 *)
Section altci_insert.
Variables (M : altCIMonad) (A : Type) (a : A).
Local Open Scope mprog.

Lemma insert_rcons a' s :
  insert a (rcons s a') =
    Ret (s ++ [:: a'; a]) [~] fmap (rcons^~ a') (insert a s) :> M _.
Proof.
elim: s a' => [a'|s1 s2 IH a'].
  rewrite cat0s fmapE bindretf insertE altC; congr (_ [~] _).
  by rewrite insertE fmapE bindretf.
rewrite [in LHS]/= insertE IH.
rewrite naturality_nondeter [in X in _ [~] X = _]fmapE bindretf.
rewrite naturality_nondeter [in X in _ = _ [~] X]fmapE bindretf.
by rewrite -!fmap_oE altCA.
Qed.

Lemma rev_insert : rev (o) insert a = insert a \o rev :> (_ -> M _).
Proof.
rewrite boolp.funeqE; elim => [|h t IH].
  by rewrite fcompE insertE fmapE bindretf.
rewrite fcompE insertE compE alt_fmapDl fmapE bindretf compE [in RHS]rev_cons insert_rcons.
rewrite rev_cons -cats1 rev_cons -cats1 -catA; congr (_ [~] _).
move: IH; rewrite fcompE [X in X -> _]/= => <-.
rewrite -!fmap_oE; congr (fmap _ (insert a t)).
by rewrite boolp.funeqE => s; rewrite /= -rev_cons.
Qed.

End altci_insert.

Module MonadNondet.
Record mixin_of (M : failMonad) (a : forall A, M A -> M A -> M A) : Type :=
  Mixin { _ : @BindLaws.left_id M (@Fail M) a ;
          _ : @BindLaws.right_id M (@Fail M) a
}.
Record class_of (m : Type -> Type) : Type := Class {
  base : MonadFail.class_of m ;
  base2 : MonadAlt.mixin_of (Monad.Pack (MonadFail.base base)) ;
  mixin : @mixin_of (MonadFail.Pack base) (MonadAlt.alt base2)
}.
Structure t : Type := Pack { m : Type -> Type ; class : class_of m }.
Definition baseType (M : t) := MonadFail.Pack (base (class M)).
Module Exports.
Notation nondetMonad := t.
Coercion baseType : nondetMonad >-> failMonad.
Canonical baseType.
Definition alt_of_nondet (M : nondetMonad) : altMonad :=
  MonadAlt.Pack (MonadAlt.Class (base2 (class M))).
Canonical alt_of_nondet.
End Exports.
End MonadNondet.
Export MonadNondet.Exports.

Section nondet_lemmas.
Variable (M : nondetMonad).
Lemma altmfail : @BindLaws.right_id M (@Fail M) [~p].
Proof. by case: M => m [[? ?] [? ? ?] [? ?]]. Qed.
Lemma altfailm : @BindLaws.left_id M (@Fail M) [~p]. (* NB: not used? *)
Proof. by case: M => m [[? ?] [? ? ?] [? ?]]. Qed.
End nondet_lemmas.

Lemma test_canonical (M : nondetMonad) A (a : M A) (b : A -> M A) :
  a [~] (Fail >>= b) = a [~] Fail.
Proof.
Set Printing All.
Unset Printing All.
by rewrite bindfailf.
Abort.

Section nondet_insert.
Variables (M : nondetMonad) (A : Type).
Implicit Types s : seq A.

Lemma insert_Ret a s : exists m, insert a s = Ret (a :: s) [~] m :> M _.
Proof.
elim: s => [|h t [m ih]] /=; last by eexists; rewrite insertE; reflexivity.
by rewrite insertE; exists Fail; rewrite altmfail.
Qed.

Lemma perm_is_alt_ret s : exists m, perm s = Ret s [~] m :> M _.
Proof.
elim: s => [|h t [m ih] /=]; first by exists Fail; rewrite altmfail.
case: (insert_Ret h t) => n Hn.
by eexists; rewrite ih alt_bindDl bindretf Hn -altA.
Qed.

End nondet_insert.

Module MonadCINondet.
Record class_of (m : Type -> Type) : Type := Class {
  base : MonadNondet.class_of m ;
  mixin : MonadAltCI.mixin_of (@Alt (MonadAlt.Pack (MonadAlt.Class (MonadNondet.base2 base))))
}.
Structure t : Type := Pack { m : Type -> Type ; class : class_of m }.
Definition baseType (M : t) := MonadNondet.Pack (base (class M)).
Module Exports.
Notation nondetCIMonad := t.
Coercion baseType : nondetCIMonad >-> nondetMonad.
Canonical baseType.
Definition altCI_of_nondet (M : nondetCIMonad) : altCIMonad :=
  MonadAltCI.Pack (MonadAltCI.Class (mixin (class M))).
Canonical altCI_of_nondet.
End Exports.
End MonadCINondet.
Export MonadCINondet.Exports.

Section nondet_big.
Variables (M : nondetMonad) (A : Type).
Canonical alt_monoid :=
  Monoid.Law (@altA (alt_of_nondet M) A) (@altfailm _ _) (@altmfail _ _).

Lemma test_bigop n : \big[Alt/Fail]_(i < n) (Fail : M A) = Fail.
Proof.
elim: n => [|n IH]; first by rewrite big_ord0.
by rewrite big_ord_recr /= IH altmfail.
Qed.

End nondet_big.

(* gibbons2011icfp, Sect. 4.4 *)

Section select.
Variables (M : nondetMonad) (A : Type).
Implicit Types s : seq A.

Fixpoint select s : M (A * seq A)%type :=
  if s isn't h :: t then Fail else
  (Ret (h, t) [~] select t >>= (fun x => Ret (x.1, h :: x.2))).

Local Obligation Tactic := idtac.
(* variant of select that keeps track of the length, useful to write perms *)
Program Fixpoint tselect s : M (A * (size s).-1.-tuple A)%type :=
  if s isn't h :: t then Fail else
  Ret (h, @Tuple (size t) A t _) [~]
  tselect t >>= (fun x => Ret (x.1, @Tuple (size t) A _ _ (* h :: x.2 *))).
Next Obligation. by []. Defined.
Next Obligation.
move=> s h [|h' t] hts [x1 x2]; [exact: [::] | exact: (h :: x2)].
Defined.
Next Obligation.
move=> s h [|h' t] hts [x1 x2] //=; by rewrite size_tuple.
Defined.
Next Obligation. by []. Defined.

Lemma tselect_nil : tselect [::] = Fail. Proof. by []. Qed.

Lemma tselect1 a : tselect [:: a] = Ret (a, [tuple]).
Proof.
rewrite /= bindfailf altmfail /tselect_obligation_1 /= tupleE /nil_tuple.
by do 3 f_equal; apply eq_irrelevance.
Qed.

Program Definition tselect_cons_statement a t (_ : t <> nil) :=
  tselect (a :: t) = Ret (a, @Tuple _ _ t _) [~]
                    tselect t >>= (fun x => Ret (x.1, @Tuple _ _ (a :: x.2) _)).
Next Obligation. by []. Defined.
Next Obligation.
move=> a t t0 [x1 x2].
rewrite /= size_tuple prednK //; by destruct t.
Defined.

Program Lemma tselect_cons a t (Ht : t <> nil) : tselect_cons_statement a Ht.
Proof.
rewrite /tselect_cons_statement [in LHS]/=; congr (_ [~] _).
bind_ext; case=> x1 x2 /=.
do 2 f_equal; apply val_inj => /=; by destruct t.
Qed.

Local Open Scope mprog.

Lemma selectE s : select s = fmap (fun xy => (xy.1, tval xy.2)) (tselect s).
Proof.
elim: s => [|h [|h' t] IH].
- by rewrite fmapE bindfailf.
- by rewrite tselect1 fmapE bindretf /= bindfailf altmfail.
- rewrite {1}/select -/(select (h' :: t)) IH [in RHS]alt_fmapDl.
  rewrite [in X in _ = X [~] _]fmapE bindretf; congr (_ [~] _).
  rewrite bind_fmap fmap_bind; bind_ext => -[x1 x2].
  by rewrite fcompE fmapE bindretf.
Qed.

Lemma decr_size_select : bassert_size select.
Proof.
case => [|h t]; first by rewrite !selectE fmap_fail /bassert bindfailf.
rewrite /bassert selectE bind_fmap fmapE; bind_ext => -[x y] /=.
by case: assertPn => //=; rewrite size_tuple /= ltnS leqnn.
Qed.

End select.
Arguments select {M} {A}.
Arguments tselect {M} {A}.

Section permutations.
Variables (M : nondetMonad) (A : Type).
Implicit Types s : seq A.

Local Obligation Tactic := idtac.
Program Definition perms' s
  (f : forall s', size s' < size s -> M (seq A)) : M (seq A) :=
  (if s isn't h :: t then Ret [::] else
    do x <- tselect (h :: t); do y <- f x.2 _; Ret (x.1 :: y))%Do.
Next Obligation.
move=> s H h t hts [y ys]; by rewrite size_tuple -hts ltnS leqnn.
Qed.
Next Obligation. by []. Qed.

Definition perms : seq A -> M (seq A) :=
  Fix (@well_founded_size _) (fun _ => M _) perms'.

Lemma tpermsE s : (perms s = if s isn't h :: t then Ret [::] else
  do x <- tselect (h :: t); do y <- perms x.2; Ret (x.1 :: y))%Do.
Proof.
rewrite {1}/perms Fix_eq //; [by case: s|move=> s' f g H].
by rewrite /perms'; destruct s' => //; bind_ext=> x; rewrite H.
Qed.

Lemma permsE s : (perms s = if s isn't h :: t then Ret [::] else
  do x <- select (h :: t); do y <- perms x.2; Ret (x.1 :: y))%Do.
Proof.
rewrite tpermsE; case: s => // h t.
by rewrite selectE bind_fmap.
Qed.

End permutations.
Arguments perms {M} {A}.

(* from section 4.3 of mu2017, definition of perms using unfoldM *)
Section mu_perm.
Variables (A : Type) (M : nondetMonad).

Definition mu_perm : seq A -> M (seq A) :=
  unfoldM (@well_founded_size _) (@nilp _) select.

Lemma mu_permE s : (mu_perm s = if s isn't h :: t then Ret [::]
  else do a <- select (h :: t) ; do b <- mu_perm a.2; Ret (a.1 :: b))%Do.
Proof.
rewrite /mu_perm unfoldME; last exact: decr_size_select.
case: s => // h t; rewrite (_ : nilp _ = false) //.
by bind_ext => -[x1 x2] ; rewrite fmapE.
Qed.

Lemma perms_mu_perm s : perms s = mu_perm s.
Proof.
move Hn : (size s) => n.
elim: n s Hn => [|n IH [//|h t] /= [tn]].
  case => //; by rewrite permsE mu_permE.
rewrite tpermsE mu_permE selectE bind_fmap; bind_ext => -[a b].
by rewrite IH // size_tuple.
Qed.

End mu_perm.
Arguments mu_perm {A} {M}.

Module SyntaxNondet.

Inductive t : Type -> Type :=
| ret : forall A, A -> t A
| bind : forall B A, t B -> (B -> t A) -> t A
| fail : forall A, t A
| alt : forall A, t A -> t A -> t A.

Fixpoint denote {M : nondetMonad} {A} (m : t A) : M A :=
  match m with
  | ret A a => Ret a
  | bind A B m f => denote m >>= (fun x => denote (f x))
  | fail A => Fail
  | alt A m1 m2 => denote m1 [~] denote m2
  end.

Module Exports.
Notation nondetSyntax := t.
Notation ndAlt := alt.
Notation ndRet := ret.
Notation ndBind := bind.
Notation ndFail := fail.
Notation ndDenote := denote.
End Exports.
End SyntaxNondet.
Export SyntaxNondet.Exports.

Module MonadExcept.
Record mixin_of (M : failMonad) : Type := Mixin {
  catch : forall A, M A -> M A -> M A ;
  (* monoid *)
  _ : forall A, right_id Fail (@catch A) ;
  _ : forall A, left_id Fail (@catch A) ;
  _ : forall A, associative (@catch A) ;
  (* unexceptional bodies need no handler *)
  _ : forall A x, @left_zero (M A) (M A) (Ret x) (@catch A)
  (* NB: left-zero of sequential composition inherited from failMonad *)
}.
Record class_of (m : Type -> Type) := Class {
  base : MonadFail.class_of m ;
  mixin : mixin_of (MonadFail.Pack base) }.
Record t : Type := Pack { m : Type -> Type ; class : class_of m }.
Definition baseType M := MonadFail.Pack (base (class M)).
Definition monadType M := Monad.Pack (MonadFail.base (base (class M))).
Module Exports.
Definition Catch (M : t) : forall A, m M A -> m M A -> m M A :=
  let: Pack _ (Class _ (Mixin x _ _ _ _)) := M
  return forall A, m M A -> m M A -> m M A in x.
Arguments Catch {M A} : simpl never.
Notation exceptMonad := t.
Coercion baseType : exceptMonad >-> failMonad.
Canonical baseType.
(* NB: ignore the warning *)
Canonical monadType.
End Exports.
End MonadExcept.
Export MonadExcept.Exports.

Section except_lemmas.
Variables (M : exceptMonad).
Lemma catchfailm : forall A, left_id Fail (@Catch M A).
Proof. by case: M => m [? []]. Qed.
Lemma catchmfail : forall A, right_id Fail (@Catch M A). (* NB: not used? *)
Proof. by case: M => m [? []]. Qed.
Lemma catchret : forall A x, left_zero (Ret x) (@Catch M A).
Proof. by case: M => m [? []]. Qed.
Lemma catchA : forall A, associative (@Catch M A). (* NB: not used? *)
Proof. by case: M => m [? []]. Qed.
End except_lemmas.

Section fastproduct.

Definition product := foldr muln 1.

Lemma product0 s : O \in s -> product s = O.
Proof.
elim: s => //= h t ih; rewrite inE => /orP[/eqP <-|/ih ->];
  by rewrite ?muln0 ?mul0n.
Qed.

Section work.
Variable M : failMonad.
Local Open Scope mprog.

Definition work s : M nat :=
  if O \in s then Fail else Ret (product s).

Let Work s := if O \in s then @Fail M nat
              else Ret (product s).

(* work refined to eliminate multiple traversals *)
Lemma workE :
  let next := fun n (mx : M _) => if n == 0 then Fail else fmap (muln n) mx in
  work = foldr next (Ret 1).
Proof.
apply foldr_universal => // h t; case: ifPn => [/eqP -> //| h0].
by rewrite /work inE eq_sym (negbTE h0) [_ || _]/= fmap_if fmap_fail.
Qed.

End work.
Arguments work {M}.

Variable M : exceptMonad.

Definition fastprod s : M _ := Catch (work s) (Ret O).

Let Fastprod (s : seq nat) :=
  @Catch M nat (@work (MonadExcept.baseType M) s) (Ret O).

(* fastprod is pure, never throwing an unhandled exception *)
Lemma fastprodE s : fastprod s = Ret (product s).
Proof.
rewrite /fastprod /work fun_if if_arg catchfailm.
by rewrite catchret; case: ifPn => // /product0 <-.
Qed.

End fastproduct.

Module MonadContinuation.
Record mixin_of (M : monad) : Type := Mixin {
   callcc : forall A B, ((A -> M B) -> M A) -> M A;
   _ : forall A B (g : (A -> M B) -> M A) (k : B -> M B),
       callcc (fun f => g (fun x => f x >>= k)) = callcc g;
   _ : forall A B (m : M B), callcc (fun _ : B -> M A => m) = m ;
   _ : forall A B C (m : M A) x (k : A -> B -> M C),
       callcc (fun f : _ -> M _ => m >>= (fun a => f x >>= (fun b => k a b))) =
       callcc (fun f : _ -> M _ => m >> f x) ;
   _ : forall A B (m : M A) b,
       callcc (fun f : B -> M B => m >> f b) =
       callcc (fun _ : B -> M B => m >> Ret b) }.
Record class_of (m : Type -> Type) := Class {
  base : Monad.class_of m ; mixin : mixin_of (Monad.Pack base) }.
Structure t : Type := Pack { m : Type -> Type ; class : class_of m }.
Definition baseType (M : t) := Monad.Pack (base (class M)).
Module Exports.
Definition Callcc (M : t) : forall A B, ((A -> m M B) -> m M A) -> m M A :=
  let: Pack _ (Class _ (Mixin x _ _ _ _)) :=
    M return forall A B, ((A -> m M B) -> m M A) -> m M A in x.
Notation contMonad := t.
Coercion baseType : contMonad >-> monad.
Canonical baseType.
End Exports.
End MonadContinuation.
Export MonadContinuation.Exports.

Section continuation_lemmas.
Variables (M : contMonad).
Lemma callcc0 A B (g : (A -> M B) -> M A) (k : B -> M B) :
  Callcc (fun f => g (fun x => f x >>= k)) = Callcc g.
Proof. by case: M A B g k => m [? []]. Qed. (* NB Schrijvers *)
Lemma callcc1 A B p : Callcc (fun _ : B -> M A => p) = p.
Proof. by case: M A B p => m [? []]. Qed. (* NB Wadler callcc_elim *)
Lemma callcc2 A B C (m : M A) x (k : A -> B -> M C) :
  (Callcc (fun f : _ -> M _ => do a <- m; do b <- f x; k a b) =
   Callcc (fun f : _ -> M _ => m >> f x))%Do.
Proof. by case: M A B C m x k => m [? []]. Qed.
Lemma callcc3 A B (m : M A) b :
  Callcc (fun f : B -> M B => m >> f b) = Callcc (fun _ : B -> M B => m >> Ret b).
Proof. by case: M A B m b => m [? []]. Qed.
End continuation_lemmas.

Definition addM (M : monad) (a b : M nat) : M nat :=
  a >>= (fun x => b >>= (fun y => Ret (x + y))).
Notation "a +m b" := (addM a b) (at level 50, format "a  +m  b").

Section continuation_example.
Variable M : contMonad.
Let wadler_example : Ret 1 +m Callcc (fun f => Ret 10 +m f 100) = Ret (1 + 100) :> M _.
Proof.
rewrite {1}/addM bindretf.
rewrite (_ : Callcc _ = Ret 100) ?bindretf //.
transitivity (Callcc (fun _ : nat -> M nat => Ret 100)); last by rewrite callcc1.
transitivity (Callcc (fun f : nat -> M nat => Ret 10 >>= (fun a => f 100))); first by rewrite callcc2.
rewrite callcc3 //; congr Callcc.
rewrite boolp.funeqE => g.
by rewrite bindretf.
Qed.

End continuation_example.

Module MonadShiftReset.
Record mixin_of (M : contMonad) U : Type := Mixin {
  shift : forall A, ((A -> M U) -> M U) -> M A ;
  reset : M U -> M U ;
  _ : forall A (m : M A), shift (fun k => m >>= k) = m ; (* NB Wadler *)
  _ : forall A B (h : (A -> M B) -> M A),
    Callcc h = shift (fun k' => h (fun x => shift (fun k'' => k' x)) >>= k') (* NB Wadler *) ;
  _ : forall A (c : A) (c': U) (k : A -> U -> _),
    (reset (do x <- Ret c; do y <- shift (fun _ => Ret c'); k x y) = Ret c >> Ret c')%Do ;
  _ : forall (c c' : U) (k : U -> U -> _),
    (reset (do x <- Ret c; do y <- shift (fun f => do v <- f c'; f v); Ret (k x y)) =
     reset (do x <- Ret c; do y <- shift (fun f => f c'); Ret (k x (k x y))))%Do ;
  _ : forall (c : U) k,
    (reset (do y <- shift (@^~ c); Ret (k y)) = Ret (k c))%Do
}.
Record class_of (m : Type -> Type) B := Class {
  base : MonadContinuation.class_of m ; mixin : mixin_of (MonadContinuation.Pack base) B }.
Structure t B : Type := Pack { m : Type -> Type ; class : class_of m B }.
Definition baseType B (M : t B) := MonadContinuation.Pack (base (class M)).
Module Exports.
Definition Shift B (M : t B) : forall A, ((A -> m M B) -> m M B) -> m M A :=
  let: Pack _ (Class _ (Mixin x _ _ _ _ _ _)) := M return forall A, ((A -> m M B) -> m M B) -> m M A in x.
Definition Reset B (M : t B) : m M B -> m M B :=
  let: Pack _ (Class _ (Mixin _ x _ _ _ _ _)) := M return m M B -> m M B in x.
Notation shiftresetMonad := t.
Coercion baseType : shiftresetMonad >-> contMonad.
Canonical baseType.
End Exports.
End MonadShiftReset.
Export MonadShiftReset.Exports.

Section shiftreset_lemmas.
Variables (U : Type) (M : shiftresetMonad U).
Lemma shiftreset0 A (m : M A) : Shift (fun k => m >>= k) = m.
Proof. by case: M A m => m [? []]. Qed.
Lemma shiftreset1 A B (h : (A -> M B) -> M A) :
  Callcc h = Shift (fun k' => h (fun x => Shift (fun k'' => k' x)) >>= k').
Proof. by case: M A B h => m [? []]. Qed.
Lemma shiftreset2 A c c' (k : A -> U -> _):
  Reset (do x <- Ret c; do y <- (Shift (fun _ => @RET M U c') : M U); k x y)%Do = (Ret c >> Ret c') :> M _ .
Proof. by case: M c c' k => m [? []]. Qed.
Lemma shiftreset3 c c' (k : U -> U -> _) :
  (Reset (do x <- Ret c; do y <- (Shift (fun f : U -> M U => do v <- f c'; f v) : M U); Ret (k x y)) =
  Reset (do x <- Ret c; do y <- (Shift (fun f : U -> M U => f c') : M U); Ret (k x (k x y))))%Do.
Proof. by case: M c c' k => m [? []]. Qed.
Lemma shiftreset4 c k:
  Reset ((Shift (@^~ c) : M U) >>= (fun y => Ret (k y))) = Ret (k c) :> M U.
Proof. by case: M c => m [? []]. Qed.
End shiftreset_lemmas.

Section shiftreset_examples.
Variable (M : shiftresetMonad nat).
Let wadler_example2 :
  Ret 1 +m (Reset (Ret 10 +m (Shift (fun f : _ -> M nat => Ret 100 : M _) : M _)) : M _) =
  Ret (1 + 100).
Proof.
rewrite /addM.
rewrite bindretf.
transitivity (Ret 100 >>= (fun y => Ret (1 + y)) : M _); last first.
  by rewrite bindretf.
congr (Bind _ _). (* TODO : bind_ext casse *)
rewrite (shiftreset2 _ _).
by rewrite bindretf.
Qed.

Let wadler_example1 :
  Ret 1 +m (Reset (Ret 10 +m (Shift (fun f : _ -> M nat => f (100) >>= f) : M _)) : M _) =
  Ret (1 + (10 + (10 + 100))).
Proof.
rewrite /addM.
rewrite bindretf.
transitivity ((Ret (10 + (10 + 100))) >>= (fun y => Ret (1 + y)) : M _); last first.
  by rewrite bindretf.
congr (Bind _ _).
rewrite shiftreset3.
rewrite (_ : do x <- Ret 10; _ = do y <- Shift (@^~ 100) : M _; Ret (10 + (10 + y)))%Do; last first.
  by rewrite bindretf.
by rewrite shiftreset4.
Qed.

End shiftreset_examples.

(* NB: wip, no model *)
Module MonadJump.
(* Monad Transformers and Modular Algebraic Eﬀects: What Binds Them Together
   Tom Schrijvers & al. Report CW699, September 2016
   $8.2 p10 *)
Record mixin_of ref (M : monad) : Type := Mixin {
   jump : forall A B, ref A -> A -> M B;
   sub : forall A B, (ref A -> M B) -> (A -> M B) -> M B;
   _ : forall A B k x, sub (fun r => @jump A B r x) k = k x;
   _ : forall A B p k, @sub A B (fun _ => p) k = p;
   _ : forall A B p r', sub p (@jump A B r') = p r';
   _ : forall A B (p : ref A -> ref B -> M B) (k1 : A -> M B) k2,
       sub (fun r1 : ref A => sub (fun r2 => p r1 r2) (k2 r1)) k1 =
       sub (fun r2 : ref B => sub (fun r1 => p r1 r2) k1) (fun x => sub (k2^~x) k1);
   _ : forall A B r x k, (@jump A B r x) >>= k = @jump A B r x;
   _ : forall A B p q k, @sub A B p q >>= k = @sub A B (p >=> k) (q >=> k)
}.
Record class_of ref (m : Type -> Type) := Class {
  base : Monad.class_of m ; mixin : mixin_of ref (Monad.Pack base) }.
Structure t ref : Type := Pack { m : Type -> Type ; class : class_of ref m }.
Definition baseType ref (M : t ref) := Monad.Pack (base (class M)).
Module Exports.
Definition Jump ref (M : t ref) : forall A B, ref A -> A -> m M B :=
  let: Pack _ (Class _ (Mixin x _ _ _ _ _ _ _)) :=
    M return forall A B, ref A -> A -> m M B in x.
Arguments Jump {ref M A B} : simpl never.
Definition Sub ref (M : t ref) : forall A B, (ref A -> m M B) -> (A -> m M B) -> m M B :=
  let: Pack _ (Class _ (Mixin _ x _ _ _ _ _ _)) :=
    M return forall A B, (ref A -> m M B) -> (A -> m M B) -> m M B in x.
Arguments Sub {ref M A B} : simpl never.
Notation jumpMonad := t.
Coercion baseType : jumpMonad >-> monad.
Canonical baseType.
End Exports.
End MonadJump.
Export MonadJump.Exports.
