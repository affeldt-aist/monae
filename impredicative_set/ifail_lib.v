From mathcomp Require Import all_ssreflect.
Require Import imonae_lib ihierarchy imonad_lib.

(******************************************************************************)
(*     Definitions and lemmas using failure and nondeterministic monads       *)
(*                                                                            *)
(*                arb == arbitrary nondeterministic choice between booleans   *)
(*      foldM/unfoldM                                                         *)
(*              hyloM                                                         *)
(*    arbitrary def s == nondeterministic choice of an element in the list s, *)
(*                       def if the list is empty                             *)
(*             subs s == subsequence of a list                                *)
(*                       (ref: Sect. 3.1, gibbons2012utp)                     *)
(*         insert a s == insertion                                            *)
(*      permutation s == permutation                                          *)
(*                       (ref: Sect. 3, mu2019tr2)                            *)
(*             select == (ref: Sect. 4.4, gibbons2011icfp)                    *)
(*              perms == type seq A -> M (seq A)                              *)
(*            mu_perm == definition of perms using unfoldM                    *)
(*                       (ref: Sect 4.3, mu2017)                              *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.

Import Univ.

Definition arb {M : altMonad} : M bool := Ret true [~] Ret false.

Section monadalt_lemmas.
Variable (M : altMonad).

(* TODO: name ok? *)
Lemma naturality_nondeter (A B : UU0) (f : A -> B) (p q : M _):
  (M # f) (p [~] q) = (M # f) p [~] (M # f) q.
Proof. by rewrite 3!fmapE alt_bindDl. Qed.

Lemma alt_fmapDl (A B : UU0) (f : A -> B) (m1 m2 : M A) :
  (M # f) (m1 [~] m2) = (M # f) m1 [~] (M # f) m2.
Proof. by rewrite 3!fmapE alt_bindDl. Qed.

End monadalt_lemmas.

Lemma fmap_fail {A B : UU0} (M : failMonad) (f : A -> B) : (M # f) Fail = Fail.
Proof. by rewrite fmapE bindfailf. Qed.

Lemma well_founded_size A : well_founded (fun x y : seq A => size x < size y).
Proof. by apply: (@Wf_nat.well_founded_lt_compat _ size) => ? ? /ltP. Qed.

Definition bassert_hylo {M : failMonad} (A B : UU0)
  (f : B -> M (A * B)%type) (p : pred B) (r : forall p f, B -> B -> bool) :=
  forall b, f b = bassert (fun z => r p f z.2 b) (f b).

Definition bassert_size {M : failMonad} (A B : UU0)
  (f : seq B -> M (A * seq B)%type) :=
  @bassert_hylo M _ _ f predT (fun _ _ x y => size x < size y).

Section foldM.
Variables (M : monad) (T R : UU0) (f : R -> T -> M R).
Fixpoint foldM z s : M _ := if s is x :: s' then f z x >>= (fun y => foldM y s') else (Ret z).
End foldM.

Section unfoldM.

Local Open Scope mprog.

Section unfoldM_monad.
Variables (M : monad) (A B : UU0).
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
Variables (M : failMonad) (A B' : UU0).
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
Variables (M : failMonad) (A B C : UU0).
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

Section arbitrary.

Variables (M : altMonad) (A : UU0) (def : A).

Definition arbitrary : seq A -> M A :=
  foldr1 (Ret def) (fun x y => x [~] y) \o map Ret.

End arbitrary.
Arguments arbitrary {M} {A}.

Lemma arbitrary1 (N : altMonad) (T : UU0) (def : T) h :
  arbitrary def [:: h] = Ret h :> N T.
Proof. by []. Qed.

Section arbitrary_lemmas.
Variables (M : altCIMonad).

Lemma arbitrary2 (T : UU0) (def : T) h t :
  arbitrary def [:: h; t] = Ret h [~] Ret t :> M _.
Proof. by rewrite /arbitrary /= altC. Qed.

Lemma arbitrary_cons (T :UU0) (def : T) h t : 0 < size t ->
  arbitrary def (h :: t) = Ret h [~] arbitrary def t :> M _.
Proof.
move: def h; elim: t => // a [//|b [|c t]] ih def h _.
- by rewrite arbitrary2.
- by rewrite /arbitrary /= altA altC (altC (Ret b)).
- move: (ih a h erefl); rewrite /arbitrary /= => ->.
  move: (ih h a erefl); rewrite /arbitrary /= => ->.
  by rewrite altCA.
Qed.

Lemma arbitrary_naturality (T U : UU0) (a : T) (b : U) (f : T -> U) :
  forall x, 0 < size x -> (M # f \o arbitrary a) x = (arbitrary b \o map f) x.
Proof.
elim=> // x [_ _ | x' xs /(_ isT)].
  by rewrite [in LHS]compE fmapE bindretf.
rewrite [in X in X -> _]/= fmapE => ih _.
rewrite [in RHS]compE [in RHS]/= [in RHS](arbitrary_cons b) // [in LHS]compE.
by rewrite [in LHS]arbitrary_cons // fmapE /= alt_bindDl bindretf /= ih.
Qed.

Lemma mpair_arbitrary_base_case (T : UU0) a x (y : seq T) :
  (0 < size y)%nat ->
  arbitrary (a, a) (cp [:: x] y) = mpair (arbitrary a [:: x], arbitrary a y) :> M _.
Proof.
move=> y0; rewrite cp1.
transitivity (arbitrary a y >>= (fun y' => Ret (x, y')) : M _).
  by rewrite -(compE (arbitrary _)) -(arbitrary_naturality a) // compE fmapE.
transitivity (do z <- Ret x; do y' <- arbitrary a y; Ret (z, y') : M _)%Do.
  by rewrite bindretf.
by [].
Qed.

Lemma arbitrary_cat (T : UU0) (a : T) s t :
  let m := size s in let n := size t in
  0 < m -> 0 < n ->
  arbitrary a (s ++ t) = arbitrary a s [~] arbitrary a t :> M _.
Proof.
elim: s t => [//|s1 s2 IH].
elim/last_ind => // t1 t2 _ m n m0 n0 //.
rewrite cat_cons [in LHS]arbitrary_cons; last first.
  by rewrite size_cat size_rcons addnS.
destruct s2 as [|s2 s3] => //.
rewrite IH // altA; congr (_ [~] _).
by rewrite [in RHS]arbitrary_cons.
Qed.

Lemma mpair_arbitrary (T : UU0) a (x y : seq T) :
  0 < size x -> 0 < size y ->
  mpair (arbitrary a x, arbitrary a y) = arbitrary (a, a) (cp x y) :> M (T * T)%type.
Proof.
elim: x y => // x; case=> [_ y _ size_y|x' xs IH y _ size_y]; apply/esym.
  exact/mpair_arbitrary_base_case.
set xxs := x' :: xs.
rewrite /cp -cat1s allpairs_cat -/(cp _ _) cp1 /= arbitrary_cat; last 2 first.
  by rewrite size_map.
  by rewrite size_cat size_map addn_gt0 size_y.
pose n := size y.
pose l := size (cp xxs y).
rewrite -IH //.
rewrite -/xxs.
move: (mpair_arbitrary_base_case a x size_y).
rewrite {1}/cp [in X in arbitrary _ X]/= cats0 => ->.
rewrite -alt_bindDl.
by rewrite -arbitrary_cat.
Qed.

Lemma arbitrary_inde (T : UU0) a (s : seq T) {U} (m : M U) :
  0 < size s -> arbitrary a s >> m = m.
Proof.
elim: s a m => // h [_ a m _|h' t ih a m _].
  by rewrite arbitrary1 bindretf.
by rewrite arbitrary_cons // alt_bindDl ih // bindretf altmm.
Qed.

End arbitrary_lemmas.
Arguments arbitrary_naturality {M T U}.

Section subsequences_of_a_list.
Local Open Scope mprog.

Variables (M : altMonad) (A : UU0).

Fixpoint subs (s : seq A) : M (seq A) :=
  if s isn't h :: t then Ret [::] else
  let t' := subs t in
  fmap (cons h) t' [~] t'.

Fixpoint SUBS (s : seq A) : Functor.acto (Monad.baseType (MonadAlt.baseType M)) _ :=
  if s isn't h :: t then Ret [::] else
  let t' : Functor.acto (Monad.baseType (MonadAlt.baseType M)) _ := SUBS t in
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

Section permutation_and_insertion.
Variable M : altMonad.
Local Open Scope mprog.

Fixpoint insert {A : UU0} (a : A) (s : seq A) : M (seq A) :=
  if s isn't h :: t then Ret [:: a] else
  Ret (a :: h :: t) [~] fmap (cons h) (insert a t).
Arguments insert : simpl never.

Lemma insertE (A : UU0) (a : A) s :
  insert a s = if s isn't h :: t then Ret [:: a] else
  Ret (a :: h :: t) [~] fmap (cons h) (insert a t).
Proof. by case: s. Qed.

Fixpoint perm {A : UU0} (s : seq A) : M (seq A) :=
  if s isn't h :: t then Ret [::] else perm t >>= insert h.

(* see also netys2017 *)
Lemma insert_map (A B : UU0) (f : A -> B) (a : A) :
  insert (f a) \o map f = map f (o) insert a :> (_ -> M _).
Proof.
apply fun_ext; elim => [|y xs IH].
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
Lemma perm_o_map (A B : UU0) (f : A -> B) :
  perm \o map f = map f (o) perm :> (seq A -> M (seq B)).
Proof.
apply fun_ext; elim => [/=|x xs IH].
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

Variables (A : UU0) (p : pred A).

Lemma filter_insertN a : ~~ p a ->
  forall s, (filter p (o) insert a) s = Ret (filter p s) :> M _.
Proof.
move=> pa; elim => [|h t IH].
  by rewrite fcompE insertE -(compE (fmap _)) (natural RET) FIdf /= (negbTE pa).
rewrite fcompE insertE alt_fmapDl.
rewrite -(compE (fmap _)) (natural RET) FIdf [in X in X [~] _]/= (negbTE pa).
case: ifPn => ph.
- rewrite -fmap_oE (_ : filter p \o cons h = cons h \o filter p); last first.
    apply fun_ext => x /=; by rewrite ph.
  rewrite fmap_oE.
  move: (IH); rewrite fcompE => ->.
  by rewrite fmapE /= ph bindretf /= altmm.
- rewrite -fmap_oE (_ : filter p \o cons h = filter p); last first.
    apply fun_ext => x /=; by rewrite (negbTE ph).
  move: (IH); rewrite fcompE => -> /=; by rewrite (negbTE ph) altmm.
Qed.

Lemma filter_insertT a : p a ->
  filter p (o) insert a = insert a \o filter p :> (_ -> M _).
Proof.
move=> pa; apply fun_ext; elim => [|h t IH].
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
    by apply fun_ext => x /=; rewrite (negbTE ph).
  move: (IH); rewrite fcompE => ->.
  rewrite fmapE bindretf /= pa (negbTE ph) [in RHS]insertE; case: (filter _ _) => [|h' t'].
    by rewrite insertE altmm.
  by rewrite !insertE altA altmm.
Qed.

(* netys2017 *)
Lemma perm_filter : perm \o filter p = filter p (o) perm :> (_ -> M _).
Proof.
apply fun_ext; elim => [|h t /= IH].
  by rewrite fcompE fmapE bindretf.
case: ifPn => ph.
  rewrite [in LHS]/= IH [in LHS]fcomp_def compE [in LHS]bind_fmap.
  rewrite [in RHS]fcomp_def compE -/(fmap _ _) [in RHS]fmap_bind; bind_ext => s.
  by rewrite filter_insertT.
rewrite fcompE fmap_bind IH fcompE fmapE; bind_ext => s.
by rewrite filter_insertN.
Qed.

End perm_filter.

(* mu2019tr2, Sect. 3, see also netsys2017 *)
Section altci_insert.
Variables (M : altCIMonad) (A : UU0) (a : A).
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
apply fun_ext; elim => [|h t IH].
  by rewrite fcompE insertE fmapE bindretf.
rewrite fcompE insertE compE alt_fmapDl fmapE bindretf compE [in RHS]rev_cons insert_rcons.
rewrite rev_cons -cats1 rev_cons -cats1 -catA; congr (_ [~] _).
move: IH; rewrite fcompE [X in X -> _]/= => <-.
rewrite -!fmap_oE. congr (fmap _ (insert a t)).
by apply fun_ext => s; rewrite /= -rev_cons.
Qed.

End altci_insert.

Lemma test_canonical (M : nondetMonad) A (a : M A) (b : A -> M A) :
  a [~] (Fail >>= b) = a [~] Fail.
Proof.
Set Printing All.
Unset Printing All.
by rewrite bindfailf.
Abort.

Section nondet_insert.
Variables (M : nondetMonad) (A : UU0).
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

Definition addM (M : monad) (a b : M nat) : M nat :=
  a >>= (fun x => b >>= (fun y => Ret (x + y))).
Notation "a +m b" := (addM a b) (at level 50, format "a  +m  b").

Definition mulM (M : monad) (a b : M nat) : M nat :=
  a >>= (fun x => b >>= (fun y => Ret (x * y))).
Notation "a *m b" := (mulM a b) (at level 50, format "a  *m  b").

(* TODO: examples below are about control monads and should maybe be moved to a
new file; reference: Wadler, P. Monads and composable continuations. LISP and
Symbolic Computation 7, 39–55 (1994) *)

Section continuation_example.
Variable M : contMonad.

Let wadler94_sect31 : Ret 1 +m Callcc (fun f => Ret 10 +m f 100) = Ret (1 + 100) :> M _.
Proof.
rewrite {1}/addM bindretf.
rewrite (_ : Callcc _ = Ret 100) ?bindretf //.
transitivity (Callcc (fun _ : nat -> M nat => Ret 100)); last by rewrite callcc1.
transitivity (Callcc (fun f : nat -> M nat => Ret 10 >>= (fun a => f 100))); first by rewrite callcc2.
rewrite callcc3 //; congr Callcc.
apply fun_ext => g.
by rewrite bindretf.
Qed.

End continuation_example.

Section shiftreset_examples.
Variable (M : shiftresetMonad nat).

Let wadler94_sect32_1 :
  Ret 1 +m (Reset (Ret 10 +m (Shift (fun f : _ -> M nat => f 100 >>= f) : M _)) : M _) =
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

Let wadler94_sect32_2 :
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

End shiftreset_examples.
