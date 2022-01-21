(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2020 monae authors, license: LGPL-2.1-or-later               *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require boolp.
Require Import monae_lib.
From HB Require Import structures.
Require Import hierarchy monad_lib.

(******************************************************************************)
(*     Definitions and lemmas using failure and nondeterministic monads       *)
(*                                                                            *)
(*                arb == arbitrary nondeterministic choice between booleans   *)
(*              foldM                                                         *)
(*      unfoldM p f y == generates a list a from a seed y, if p y holds the   *)
(*                       generation stops,otherwise an element and a new seed *)
(*                       of generated using f                                 *)
(*              hyloM == [2, Sect. 5.1]                                       *)
(*    arbitrary def s == nondeterministic choice of an element in the list s, *)
(*                       def if the list is empty                             *)
(*             subs s == subsequence of a list                                *)
(*                       (ref: Sect. 3.1, gibbons2012utp)                     *)
(*       nondetSyntax == syntax of nondeterministic monad                     *)
(*                       (constructors: ndRet ndBind ndFail ndAlt)            *)
(*         ndDenote x == semantics of x : nondetSyntax                        *)
(*         insert a s == insert a in the list s nondeterministically          *)
(*            iperm s == nondeterministic permutation of the list s, defined  *)
(*                       as a Fixpoint using insert [1, Sect. 3]              *)
(*           select s == nondeterministically splits the list s into a pair   *)
(*                       of one chosen element and the rest [3, Sect. 4.4]    *)
(*                       [2, Sect. 3.2]                                       *)
(*          tselect s == same as select but returns a pair whose second       *)
(*                       projection has type (size s).-1.-tuple A, useful to  *)
(*                       write perms                                          *)
(*            perms s == of type seq A -> M (seq A), nondeterministically     *)
(*                       computes a permutation of s using (t)select          *)
(*            uperm s == nondeterministically computes a permutation of s,    *)
(*                       defined using unfoldM and select [2, Sect. 3.2]      *)
(*        dassert p a == computation of type M {x | p x} that fails if a does *)
(*                       not satisfy p or return a otherwise (with a proof    *)
(*                       that is satisfies p)                                 *)
(*           splits s == split a list nondeterministically                    *)
(*                       type: seq A -> M (seq A * seq A) with M : plusMonad  *)
(*      splits_bseq s == same as split with an enriched return type           *)
(*                       M ((size s).-bseq A * (size s).-bseq A))             *)
(*          dsplits s == same as split with an enriched return type           *)
(*                       M {x : seq A * seq A | size x.1 + size x.2 == n}     *)
(*            qperm s == permute the list s                                   *)
(*                      type: seq A -> M (seq A) with M : plusMonad           *)
(*   nondetPlus_sub m == m is a computation of the plusMonad that can be      *)
(*                       written with the syntax of the nondeterministic monad*)
(*         m1 `<=` m2 == m1 refines m2, i.e., every result of m1 is a         *)
(*                       possible result of m2                                *)
(*          f `<.=` g == refinement relation lifted to functions, i.e.,       *)
(*                       forall x, f x `<=` g x                               *)
(*                                                                            *)
(* ref:                                                                       *)
(* - [1] mu2019tr2                                                            *)
(* - [2] mu2019tr3                                                            *)
(* - [3] gibbons2011icfp                                                      *)
(* - [4] mu2020flops                                                          *)
(******************************************************************************)

Reserved Notation "m1 `<=` m2" (at level 70, no associativity).
Reserved Notation "f `<.=` g" (at level 70, no associativity).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.

(* TODO: move *)
Lemma mem_rcons_cat (A : eqType) (b : seq A) h : h \in b ->
  exists b1 b2, b = rcons b1 h ++ b2.
Proof.
move=> hb; exists (take (index h b) b), (drop (index h b).+1 b).
rewrite -cats1 -catA -{1}(cat_take_drop (index h b) b); congr (_ ++ _) => /=.
by rewrite -{2}(nth_index h hb) -drop_nth // index_mem.
Qed.

Lemma bind_ext_guard {M : failMonad} (A : UU0) (b : bool) (m1 m2 : M A) :
  (b -> m1 = m2) -> guard b >> m1 = guard b >> m2.
Proof. by case: b => [->//|_]; rewrite guardF !bindfailf. Qed.

Definition arb {M : altMonad} : M bool := Ret true [~] Ret false.

Section monadalt_lemmas.
Variable (M : altMonad).

Lemma alt_fmapDr (A B : UU0) (f : A -> B) (m1 m2 : M A) :
  (M # f) (m1 [~] m2) = (M # f) m1 [~] (M # f) m2.
Proof. by rewrite 3!fmapE alt_bindDl. Qed.

End monadalt_lemmas.

Lemma fmap_fail {A B : UU0} (M : failMonad) (f : A -> B) :
  (M # f) fail = fail.
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

Lemma arbitrary_cons (T : UU0) (def : T) h t : 0 < size t ->
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

Lemma perm_eq_arbitrary (A : eqType) def (a b : seq A) : perm_eq a b ->
  arbitrary def a = arbitrary def b :> M _.
Proof.
elim: a def b => [def b| h [|t1 t2] ih def b].
- by move/perm_size/esym/size0nil ->.
- move: b => [/perm_size//|b1]; move => [|b2 b3 /perm_size//].
  move/perm_consP => [i [s [ihb1s /perm_size/size0nil s0]]].
  move: ihb1s; rewrite s0 /=.
  by move: i => [/=|i]; [rewrite rot0 => -[->]|rewrite /rot /= => -[->]].
- move=> htb.
  have [b1 [b2 bE]] : exists b1 b2, b = rcons b1 h ++ b2.
    suff : h \in b by exact: mem_rcons_cat.
    by move: htb => /perm_mem /(_ h); rewrite mem_head.
  rewrite bE arbitrary_cons // (ih _ (b1 ++ b2)); last first.
    move: htb; rewrite bE -cats1 -catA perm_sym (perm_catCA b1 [:: h] b2).
    by rewrite perm_cons perm_sym.
  move: b2 bE => [|b2 b3 bE].
    rewrite !cats0.
    move: b1 => [bE|b1 b11].
      by move: htb; rewrite bE => /perm_size.
    by rewrite -cats1 arbitrary_cat// arbitrary1 altC.
  rewrite [in RHS]arbitrary_cat ?size_rcons//.
  move: b1 => [//|b1 b11] in bE *.
  rewrite arbitrary_cat// altA; congr (_ [~] _).
  by rewrite -cats1 arbitrary_cat// arbitrary1 altC.
Qed.

Lemma arbitrary_flatten (A : UU0) def (s : seq A) (f : A -> A) : (0 < size s)%nat ->
  (do x <- arbitrary def s; Ret (f x))%Do =
  arbitrary def (flatten [seq [:: f y] | y <- s]) :> M _.
Proof.
elim: s f => // a [_ f _ /=|h t ih f _].
  by rewrite /arbitrary /= bindretf.
rewrite [h :: t]lock /= -lock [in RHS]arbitrary_cons// -ih//.
by rewrite arbitrary_cons// alt_bindDl bindretf.
Qed.

Lemma arbitrary_flatten2 (A : UU0) def (s : seq A) (f g : A -> A) : (0 < size s)%nat ->
  (do x <- arbitrary def s; Ret (f x) [~] Ret (g x))%Do =
  arbitrary def (flatten [seq [:: f y; g y] | y <- s]) :> M _.
Proof.
elim: s def f g => //.
move=> h [|t1 t2] ih def f g _.
  by rewrite /= arbitrary1 bindretf arbitrary_cons //.
rewrite [t1 :: t2]lock /= -lock [in RHS]arbitrary_cons//.
rewrite [in RHS]arbitrary_cons// -ih// arbitrary_cons//.
by rewrite alt_bindDl bindretf altA.
Qed.

End arbitrary_lemmas.
Arguments arbitrary_naturality {M T U}.
Arguments perm_eq_arbitrary {M A}.

Section subsequences_of_a_list.
Local Open Scope mprog.

Variables (M : altMonad) (A : UU0).

Fixpoint subs (s : seq A) : M (seq A) :=
  if s isn't h :: t then Ret [::] else
  let t' := subs t in
  fmap (cons h) t' [~] t'.

(*Fixpoint SUBS (s : list A) : MonadAlt.sort M (list A) :=
  if s isn't h :: t then
      @Natural.cpnt ssrfun_idfun__canonical__hierarchy_Functor
        (@Functor.Pack (Monad.sort (hierarchy_MonadAlt__to__hierarchy_Monad M))
           (@Functor.Class (Monad.sort (hierarchy_MonadAlt__to__hierarchy_Monad M))
              (@Monad.hierarchy_isFunctor_mixin (Monad.sort (hierarchy_MonadAlt__to__hierarchy_Monad M))
                 (Monad.class (hierarchy_MonadAlt__to__hierarchy_Monad M))))) (@ret (hierarchy_MonadAlt__to__hierarchy_Monad M))
        (list A) (@nil A)
  else
      let t' : MonadAlt.sort M (list A) := SUBS t in
      @alt M (list A) (@actm (hierarchy_MonadAlt__to__hierarchy_Functor M) (list A) (list A) (@cons A h) t') t'.
Goal subs = SUBS. by []. Abort.*)

Lemma subs_cons x (xs : seq A) :
  subs (x :: xs) = let t' := subs xs in fmap (cons x) t' [~] t'.
Proof. by []. Qed.

Lemma subs_cat (xs ys : seq A) :
  (subs (xs ++ ys) = do us <- subs xs; do vs <- subs ys; Ret (us ++ vs))%Do.
Proof.
elim: xs ys => [ys |x xs ih ys].
  by rewrite cat0s /= bindretf bindmret.
rewrite {1}[in RHS]/subs fmapE -/(subs _) alt_bindDl bindA.
Open (X in subs xs >>= X).
  rewrite bindretf.
  under eq_bind do rewrite cat_cons.
  over.
rewrite [X in _ = X [~] _](_ : _ = fmap (cons x) (do x0 <- subs xs; do x1 <- subs ys; Ret (x0 ++ x1)))%Do; last first.
  rewrite fmapE bindA.
  bind_ext => x0.
  rewrite bindA.
  by under [in RHS]eq_bind do rewrite bindretf.
by rewrite -ih cat_cons subs_cons.
Qed.

End subsequences_of_a_list.

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
  | fail A => hierarchy.fail
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

Section insert.
Context {M : altMonad} {A : UU0}.
Local Open Scope mprog.

Fixpoint insert (a : A) (s : seq A) : M (seq A) :=
  if s isn't h :: t then Ret [:: a] else
  Ret (a :: h :: t) [~] fmap (cons h) (insert a t).

Lemma insertE (a : A) s :
  insert a s = if s isn't h :: t then Ret [:: a] else
  Ret (a :: h :: t) [~] fmap (cons h) (insert a t).
Proof. by case: s. Qed.

End insert.
Arguments insert : simpl never.

Section insert_altMonad.
Variable M : altMonad.
Local Open Scope mprog.

(* see also netys2017 *)
Lemma insert_map (A B : UU0) (f : A -> B) (a : A) :
  insert (f a) \o map f = map f (o) insert a :> (_ -> M _).
Proof.
rewrite boolp.funeqE; elim => [|y xs IH].
  by rewrite fcompE insertE -(compE (fmap (map f))) (natural ret) compE insertE.
apply/esym.
rewrite fcompE insertE alt_fmapDr.
(* first branch *)
rewrite -(compE (fmap (map f))) (natural ret) FIdf [ in X in X [~] _ ]/=.
(* second branch *)
rewrite -fmap_oE (_ : map f \o cons y = cons (f y) \o map f) //.
by rewrite fmap_oE -(fcompE (map f)) -IH [RHS]/= insertE.
Qed.

Hypothesis Mmm : forall A, idempotent (@alt _ A : M A -> M A -> M A).

Variables (A : UU0) (p : pred A).

Lemma filter_insertN a : ~~ p a ->
  forall s, (filter p (o) insert a) s = Ret (filter p s) :> M _.
Proof.
move=> pa; elim => [|h t IH].
  by rewrite fcompE insertE -(compE (fmap _)) (natural ret) FIdf /= (negbTE pa).
rewrite fcompE insertE alt_fmapDr.
rewrite -(compE (fmap _)) (natural ret) FIdf [in X in X [~] _]/= (negbTE pa).
case: ifPn => ph.
- rewrite -fmap_oE (_ : filter p \o cons h = cons h \o filter p); last first.
    rewrite boolp.funeqE => x /=; by rewrite ph.
  rewrite fmap_oE.
  move: (IH); rewrite fcompE => ->.
  by rewrite fmapE /= ph bindretf /= Mmm.
- rewrite -fmap_oE (_ : filter p \o cons h = filter p); last first.
    rewrite boolp.funeqE => x /=; by rewrite (negbTE ph).
  move: (IH); rewrite fcompE => -> /=; by rewrite (negbTE ph) Mmm.
Qed.

Lemma filter_insertT a : p a ->
  filter p (o) insert a = insert a \o filter p :> (_ -> M _).
Proof.
move=> pa; rewrite boolp.funeqE; elim => [|h t IH].
  by rewrite fcompE !insertE fmapE bindretf /= pa.
rewrite fcompE [in RHS]/=; case: ifPn => ph.
- rewrite [in RHS]insertE.
  move: (IH); rewrite [in X in X -> _]/= => <-.
  rewrite [in LHS]insertE alt_fmapDr; congr (_ [~] _).
    by rewrite fmapE bindretf /= pa ph.
  rewrite !fmapE /= fcompE bind_fmap bindA.
  under [LHS]eq_bind do rewrite bindretf.
  by rewrite /= ph.
- rewrite [in LHS]insertE alt_fmapDr.
  rewrite -[in X in _ [~] X = _]fmap_oE.
  rewrite (_ : (filter p \o cons h) = filter p); last first.
    by rewrite boolp.funeqE => x /=; rewrite (negbTE ph).
  move: (IH); rewrite fcompE => ->.
  rewrite fmapE bindretf /= pa (negbTE ph) [in RHS]insertE; case: (filter _ _) => [|h' t'].
    by rewrite insertE Mmm.
  by rewrite !insertE altA Mmm.
Qed.

End insert_altMonad.

(* mu2019tr2, Sect. 3, see also netsys2017 *)
Section insert_altCIMonad.
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
rewrite alt_fmapDr [in X in _ [~] X = _]fmapE bindretf.
rewrite alt_fmapDr [in X in _ = _ [~] X]fmapE bindretf.
by rewrite -!fmap_oE altCA.
Qed.

Lemma rev_insert : rev (o) insert a = insert a \o rev :> (_ -> M _).
Proof.
rewrite boolp.funeqE; elim => [|h t ih].
  by rewrite fcompE insertE fmapE bindretf.
rewrite fcompE insertE compE alt_fmapDr fmapE bindretf compE [in RHS]rev_cons.
rewrite insert_rcons rev_cons -cats1 rev_cons -cats1 -catA; congr (_ [~] _).
move: ih; rewrite fcompE [X in X -> _]/= => <-.
rewrite -!fmap_oE. congr (fmap _ (insert a t)).
by rewrite boolp.funeqE => s; rewrite /= -rev_cons.
Qed.

End insert_altCIMonad.

Lemma test_canonical (M : nondetMonad) A (a : M A) (b : A -> M A) :
  a [~] (fail >>= b) = a [~] fail.
Proof.
Set Printing All.
Unset Printing All.
by rewrite bindfailf.
Abort.

Section insert_plusMonad.
Variable M : plusMonad.

Lemma insertC (A : UU0) a b (s : seq A) :
  (do x <- insert b s; insert a x = do x <- insert a s; insert b x :> M _)%Do.
Proof.
have [n ns] := ubnP (size s); elim: n s ns a b => // n ih s ns a b.
case: s ns => [|h t].
  by rewrite !insertE !bindretf !insertE altC !fmapE !bindretf.
rewrite ltnS /= => ns.
rewrite (insertE _ (h :: t)) alt_bindDl bindretf.
rewrite [in LHS](insertE _ [:: b, h & t]) [in LHS](insertE _ (h :: t)).
rewrite [in RHS](insertE _ (h :: t)) [in RHS]alt_bindDl bindretf.
rewrite 2![in RHS]insertE.
rewrite [in LHS]alt_fmapDr ![in LHS]altA [in LHS](altC (Ret [:: a, b, h & t])).
rewrite -!altA; congr (_ [~] _); first by rewrite fmapE bindretf.
rewrite alt_fmapDr -!altA; congr (_ [~] _); first by rewrite fmapE bindretf.
rewrite [in LHS]altC bind_fmap /= [in LHS]/comp /=.
under eq_bind do rewrite insertE.
rewrite alt_bindDr.
under [in X in (_ [~] X) [~] _]eq_bind do rewrite fmapE.
rewrite -bindA [in LHS]ih // [in RHS]altC bind_fmap /= [in RHS]/comp /=.
under [in RHS]eq_bind do rewrite insertE.
rewrite alt_bindDr [in RHS]altC -!altA; congr (_ [~] _).
  rewrite !fmapE !bindA.
  by under [in RHS]eq_bind do rewrite !bindretf.
rewrite [in RHS]altC; congr (_ [~] _); last first.
  rewrite !fmapE !bindA.
  by under eq_bind do rewrite bindretf.
rewrite bindA.
by under [in RHS]eq_bind do rewrite fmapE.
Qed.

Lemma insert_cat (A : UU0) h (a b : seq A) u :
  insert h (a ++ u :: b) = (do x <- insert h a; Ret (x ++ u :: b))%Do [~]
                          (do x <- insert h b; Ret (a ++ u :: x))%Do :> M _.
Proof.
elim: a h u b => [h u b|a1 a2 ih h u b].
  by rewrite /= (insertE h nil) bindretf insertE fmapE.
rewrite cat_cons [in LHS]insertE [u :: b]lock /= -lock [in LHS]ih.
rewrite [in RHS]insertE [in RHS]alt_bindDl bindretf -altA; congr (_ [~] _).
rewrite [in RHS]bind_fmap [in LHS]fmapE [in LHS]alt_bindDl !bindA.
by congr (_ [~] _); under eq_bind do rewrite bindretf.
Qed.

End insert_plusMonad.

Section insert_nondetMonad.
Context {M : nondetMonad} {A : UU0}.
Implicit Types s : seq A.

Lemma insert_Ret a s : exists m, insert a s = Ret (a :: s) [~] m :> M _.
Proof.
elim: s => [|h t [m ih]] /=; last by eexists; rewrite insertE; reflexivity.
by rewrite insertE; exists fail; rewrite altmfail.
Qed.

End insert_nondetMonad.

Fixpoint iperm {M : altMonad} {A : UU0} (s : seq A) : M (seq A) :=
  if s isn't h :: t then Ret [::] else iperm t >>= insert h.

Section iperm_altMonad.
Context {M : altMonad}.
Local Open Scope mprog.

(* lemma 3.3 in mu2019tr2 *)
Lemma iperm_o_map (A B : UU0) (f : A -> B) :
  iperm \o map f = map f (o) iperm :> (_ -> M _).
Proof.
rewrite boolp.funeqE; elim => [/=|x xs IH].
  by rewrite fcompE [iperm _]/= -[in RHS]compE (natural ret).
by rewrite fcompE [in iperm _]/= fmap_bind -insert_map -bind_fmap -fcompE -IH.
Qed.

Hypothesis Mmm : forall A, idempotent (@alt _ A : M A -> M A -> M A).

Variables (A : UU0) (p : pred A).

(* netys2017 *)
Lemma iperm_filter : iperm \o filter p = filter p (o) iperm :> (_ -> M _).
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

End iperm_altMonad.

Section iperm_nondetMonad.
Context {M : nondetMonad} {A : UU0}.
Implicit Types s : seq A.

Lemma iperm_is_alt_ret s : exists m, iperm s = Ret s [~] m :> M _.
Proof.
elim: s => [|h t [m ih] /=]; first by exists fail; rewrite altmfail.
case: (@insert_Ret M A h t) => n Hn.
by eexists; rewrite ih alt_bindDl bindretf Hn -altA.
Qed.

End iperm_nondetMonad.

Section iperm_plusMonad.
Context {M : plusMonad}.

Lemma iperm_insert {A : UU0} a b (s t : seq A) :
  (do x <- iperm (b :: s ++ t); insert a x =
   do x <- iperm (rcons s a ++ t); insert b x :> M _)%Do.
Proof.
elim: s => [/=|h tl ih] in a b t *.
  rewrite !bindA.
  by under eq_bind do rewrite insertC.
rewrite [h :: tl]lock /= -lock ih /= !bindA.
suff : (do x <- iperm (rcons tl b ++ t); do x0 <- insert a x; insert h x0 =
    do x <- iperm (rcons tl a ++ t); do x0 <- insert b x; insert h x0 :> M _)%Do.
  under eq_bind do rewrite insertC.
  move=> ->.
  by under eq_bind do rewrite insertC.
rewrite -bindA -ih /= -bindA -[in RHS]ih /= !bindA; bind_ext => a'.
by rewrite -bindA insertC bindA.
Qed.

Lemma perm_eq_iperm (A : eqType) (a b : seq A) :
  perm_eq a b -> iperm a = iperm b :> M _.
Proof.
have [n na] := ubnP (size a); elim: n a na b => // n ih a na b.
case: a na => [na|a1 a2]; first by move=> /perm_size/esym/size0nil ->.
rewrite [in X in X -> _]/= ltnS => na.
case: b => [/perm_size //|b1 b2].
have [a1b1|a1b1 ab] := eqVneq a1 b1.
  by rewrite {}a1b1 perm_cons => ab /=; rewrite (ih _ na b2).
have [b21 [b22 Hb]] : exists b21 b22, b2 = rcons b21 a1 ++ b22.
  apply: mem_rcons_cat.
  by move/perm_mem : ab => /(_ a1); rewrite mem_head inE (negbTE a1b1).
have {} : perm_eq a2 (b1 :: b21 ++ b22).
  move: ab; rewrite Hb -cats1 -catA -cat_cons perm_sym.
  by rewrite perm_catCA perm_cons perm_sym.
by move=> /(ih _ na) /= ->; rewrite Hb iperm_insert.
Qed.

Lemma iperm_rcons (A : eqType) t (x : A) :
  iperm (rcons t x) = iperm (x :: t) :> M _.
Proof. by apply perm_eq_iperm; rewrite perm_rcons. Qed.

Lemma iperm_insertC (A : eqType) x y (s : seq A) :
  (do s' <- iperm (rcons s x); insert y s' =
   do s' <- insert y s; iperm (rcons s' x) :> M _)%Do.
Proof.
have [n ns] := ubnP (size s); elim: n s ns x y => // n ih.
move=> [/= _ x y|h t].
  by rewrite !bindA !bindretf /= bindA bindretf [in RHS]insertE bindretf.
rewrite ltnS /= => tn x y.
rewrite bindA iperm_rcons /= !bindA [in RHS]insertE alt_bindDl bindretf /=.
rewrite bindA iperm_rcons /= bindA bind_fmap /comp /= -[in X in _ [~]X]bindA.
rewrite -ih// bindA iperm_rcons /= !bindA -alt_bindDr; bind_ext => s'.
rewrite -alt_bindDr; bind_ext => t'.
by rewrite insertC altmm.
Qed.

Lemma iperm_rcons_bind (E : eqType) (s : seq E) x :
  iperm (rcons s x) = iperm s >>= (fun s' => iperm (rcons s' x)) :> M _.
Proof.
have [n ns] := ubnP (size s); elim: n s ns x => // n ih.
case=> [_ x|h t]; first by rewrite /= 2!bindretf /= bindretf.
rewrite ltnS /= => tn x; rewrite ih// !bindA.
by under [in RHS]eq_bind do rewrite -iperm_insertC.
Qed.

Lemma iperm_idempotent (E : eqType) : iperm >=> iperm = iperm :> (seq E -> M _).
Proof.
apply: fun_ext_dep => s; rewrite kleisliE.
elim: s => [|h t ih]; first by rewrite /= bindretf.
rewrite /= -[in RHS]ih !bindA; bind_ext.
elim/last_ind => [|s x _].
  by rewrite insertE /= !bindretf insertE /= bindretf insertE.
rewrite iperm_insertC insert_rcons alt_bindDl bind_fmap /= /comp /=.
under [in RHS]eq_bind do rewrite iperm_rcons_bind.
rewrite bindretf (@perm_eq_iperm _ _ (h :: rcons s x)); last first.
  by rewrite -cats1 -cat1s catA perm_catC.
rewrite /= iperm_insertC -alt_bindDr; bind_ext => s'.
by rewrite altmm iperm_rcons_bind.
Qed.

End iperm_plusMonad.

Section select.
Variables (M : nondetMonad) (A : UU0).
Implicit Types s : seq A.

Fixpoint select s : M (A * seq A)%type :=
  if s isn't h :: t then fail else
  (Ret (h, t) [~] select t >>= (fun x => Ret (x.1, h :: x.2))).

Local Obligation Tactic := idtac.
(* variant of select that keeps track of the length, useful to write perms *)
Program Fixpoint tselect (s : seq A) : M (A * (size s).-1.-tuple A)%type :=
  if s isn't h :: t then fail else
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

Lemma tselect_nil : tselect [::] = fail. Proof. by []. Qed.

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
- rewrite {1}/select -/(select (h' :: t)) IH [in RHS]alt_fmapDr.
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

Section uperm.
Variables (A : UU0) (M : nondetMonad).

Definition uperm : seq A -> M (seq A) :=
  unfoldM (@well_founded_size _) (@nilp _) select.

Lemma upermE s : (uperm s = if s isn't h :: t then Ret [::]
  else do a <- select (h :: t) ; do b <- uperm a.2; Ret (a.1 :: b))%Do.
Proof.
rewrite /uperm unfoldME; last exact: decr_size_select.
case: s => // h t; rewrite (_ : nilp _ = false) //.
by bind_ext => -[x1 x2] ; rewrite fmapE.
Qed.

Lemma perms_uperm s : perms s = uperm s.
Proof.
move Hn : (size s) => n.
elim: n s Hn => [|n IH [//|h t] /= [tn]].
  case => //; by rewrite permsE upermE.
rewrite tpermsE upermE selectE bind_fmap; bind_ext => -[a b].
by rewrite IH // size_tuple.
Qed.

End uperm.
Arguments uperm {A} {M}.

Section dassert.
Context {M : failMonad} (A : UU0).

Definition dassert (p : pred A) a : M { a | p a } :=
  if Bool.bool_dec (p a) true is left pa then Ret (exist _ _ pa) else fail.

Lemma bind_ext_dassert (p : pred A) a (B : UU0) (m1 m2 : {x : A | p x} -> M B) :
  (forall x h, p x -> m1 (exist _ x h) = m2 (exist _ x h)) ->
  dassert p a >>= m1 = dassert p a >>= m2.
Proof.
move=> m1m2; have [pa|pa] := boolP (p a).
  by bind_ext => -[x px]; exact: m1m2.
rewrite /dassert; case: Bool.bool_dec => [px|px]; first by rewrite px in pa.
by rewrite !bindfailf.
Qed.

End dassert.

Section splits.
Context {M : altMonad} {A : UU0}.
Implicit Types s : seq A.

Fixpoint splits s : M (seq A * seq A)%type :=
  if s isn't x :: xs then Ret ([::], [::]) else
    splits xs >>= (fun yz => Ret (x :: yz.1, yz.2) [~] Ret (yz.1, x :: yz.2)).

Fixpoint splits_bseq s : M ((size s).-bseq A * (size s).-bseq A)%type :=
  if s isn't x :: xs then Ret ([bseq of [::]], [bseq of [::]])
  else splits_bseq xs >>= (fun '(ys, zs) =>
    Ret ([bseq of x :: ys], widen_bseq (leqnSn _) zs) [~]
    Ret (widen_bseq (leqnSn _) ys, [bseq of x :: zs])).

Local Open Scope mprog.
Lemma splitsE s : splits s =
  fmap (fun '(ys, zs) => (bseqval ys, bseqval zs)) (splits_bseq s) :> M _.
Proof.
elim: s => /= [|h t ih]; first by rewrite fmapE bindretf.
rewrite {}ih /= !fmapE 2!bindA; bind_ext => -[a b] /=.
by rewrite bindretf alt_bindDl 2!bindretf.
Qed.
Local Close Scope mprog.

End splits.

Section splits_examples.
Variable M : altMonad.

Example splits0 : @splits M nat [::] = Ret ([::], [::]).
Proof. by []. Qed.

Example splits2 : @splits M nat [:: 1; 2] =
  Ret ([:: 1; 2], [::]) [~] Ret ([:: 2], [:: 1]) [~]
  Ret ([:: 1], [:: 2]) [~] Ret ([::], [:: 1; 2]).
Proof.
rewrite /splits bindA.
repeat rewrite bindretf alt_bindDl !bindretf.
by rewrite altA.
Qed.

End splits_examples.

Section splits_nondetMonad.
Context {M : nondetMonad}.

Lemma splits_guard_subseq (A : eqType) (s : seq A) :
  splits s = splits s >>= (fun x =>
    guard [&& subseq x.1 s, subseq x.2 s & perm_eq (x.1 ++ x.2) s] >> Ret x) :> M _.
Proof.
have [n ns] := ubnP (size s); elim: n s ns => // n ih s ns.
move: s ns => [ns |h t].
  by rewrite bindretf perm_refl guardT bindskipf.
rewrite [in X in X -> _]/= ltnS => ns.
rewrite [in LHS]/= [splits (h :: t)]/= bindA.
rewrite ih // [in LHS]bindA [in RHS]bindA; bind_ext => -[a b].
rewrite [subseq]lock /= -lock.
rewrite [in LHS]bindA [in RHS]bindA.
apply: bind_ext_guard => /and3P[ta tb abt]; rewrite [subseq]lock /= -lock.
rewrite !bindretf alt_bindDl !bindretf; congr (_ [~] _).
  rewrite [subseq (_ :: _) _]/= eqxx ta andTb perm_cons abt andbT.
  by rewrite (subseq_trans tb (subseq_cons _ _)) guardT bindskipf.
rewrite (subseq_trans ta (subseq_cons _ _)) andTb.
rewrite [subseq (_ :: _) _]/= eqxx tb andTb.
rewrite -cat_rcons -cats1 -catA perm_catCA perm_cons abt.
by rewrite guardT bindskipf.
Qed.

Definition dsplitsT (A : UU0) n := {x : seq A * seq A | size x.1 + size x.2 == n}.
Definition dsplitsT1 (A : UU0) n (a : dsplitsT A n) : seq A := (sval a).1.
Definition dsplitsT2 (A : UU0) n (a : dsplitsT A n) : seq A := (sval a).2.

Definition dsplits (A : UU0) (s : seq A) : M (dsplitsT A (size s)) :=
  splits s >>= dassert [pred n | size n.1 + size n.2 == size s].

End splits_nondetMonad.

Section splits_prePlusMonad.
Context {M : prePlusMonad}.

Lemma splits_guard (A : UU0) (s : seq A) :
  splits s = splits s >>=
    (fun x => guard (size x.1 + size x.2 == size s) >> Ret x) :> M _.
Proof.
elim: s => [|h t ih]; first by rewrite bindretf addn0 eqxx guardT bindskipf.
rewrite /= {1}ih !bindA; bind_ext => -[a b] /=.
by rewrite alt_bindDl !bindretf /= bindA bindretf alt_bindDr addSn addnS eqSS.
Qed.

Local Open Scope mprog.
Lemma dsplitsE (A : UU0) (s : seq A) :
  splits s = fmap (fun x => (dsplitsT1 x, dsplitsT2 x)) (dsplits s) :> M _.
Proof.
rewrite fmapE /dsplits /= bindA [LHS]splits_guard; bind_ext => -[a b].
rewrite /dassert; case: Bool.bool_dec => /= [|/negP] abs.
  by rewrite !bindretf /= abs guardT bindskipf.
by rewrite (negbTE abs) guardF 2!bindfailf.
Qed.
Local Close Scope mprog.

End splits_prePlusMonad.

Section qperm.
Variables (M : altMonad) (A : UU0) (d : unit) (T : orderType d).

Local Obligation Tactic := idtac.
Program Definition qperm' (s : seq A)
  (f : forall s', size s' < size s -> M (seq A)) : M (seq A) :=
  if s isn't x :: xs then Ret [::] else
    splits_bseq xs >>=
      (fun '(ys, zs) => liftM2 (fun a b => a ++ x :: b) (f ys _) (f zs _)).
Next Obligation.
move=> [|h t] // ht x xs [xh ->] [a b] ys _ _ .
exact: (leq_ltn_trans (size_bseq ys)).
Qed.
Next Obligation.
move=> [|h t] // ht x xs [xh ->] [a b] _ zs _.
exact: (leq_ltn_trans (size_bseq zs)).
Qed.
Next Obligation. by []. Qed.

Definition qperm : seq A -> M (seq A) :=
  Fix (@well_founded_size _) (fun _ => M _) qperm'.

Lemma qperm'_Fix (s : seq A)
  (f g : forall y, (size y < size s)%N -> M (seq A)) :
  (forall y (p : (size y < size s)%N), f y p = g y p) -> qperm' f = qperm' g.
Proof.
move=> H; rewrite /qperm'; case: s f g H => // h t f g H.
bind_ext => -[a b] /=.
rewrite (_ : f = g) //; apply fun_ext_dep => s.
by rewrite boolp.funeqE => ?; exact: H.
Qed.

Lemma qperm_nil : qperm [::] = Ret [::].
Proof. by rewrite /qperm (Fix_eq _ _ _ qperm'_Fix). Qed.

Lemma qperm_cons x xs : qperm (x :: xs) =
  splits xs >>= (fun '(ys, zs) =>
    liftM2 (fun a b => a ++ x :: b) (qperm ys) (qperm zs)).
Proof.
rewrite {1}/qperm {1}(Fix_eq _ _ _ qperm'_Fix) /=.
rewrite splitsE /= fmapE bindA; bind_ext => -[? ?].
by rewrite bindretf.
Qed.

Definition qpermE := (qperm_nil, qperm_cons).

End qperm.
Arguments qperm {M} {A}.

Section qperm_examples.
Variable M : altCIMonad.

Example perm1 : qperm [:: 1]%N = Ret [:: 1] :> M (seq nat).
Proof.
rewrite qperm_cons /=.
rewrite bindretf.
rewrite qperm_nil.
by rewrite liftM2_ret.
Qed.

Example perm2 : qperm [:: 2; 1] = Ret [:: 1; 2] [~] Ret [:: 2; 1] :> M (seq nat).
Proof.
rewrite qpermE !bindA bindretf alt_bindDl bindretf /liftM2.
by repeat rewrite !qpermE !bindA bindretf !bindretf /=.
Qed.

Example perm3 :
  qperm [:: 3; 2; 1] = Ret [:: 1; 2; 3] [~] Ret [:: 1; 3; 2] [~]
                      Ret [:: 2; 1; 3] [~] Ret [:: 2; 3; 1] [~]
                      Ret [:: 3; 1; 2] [~] Ret [:: 3; 2; 1] :> M (seq nat).
Proof.
rewrite qpermE !bindA.
repeat rewrite bindretf alt_bindDl.
rewrite bindretf /liftM2.
repeat rewrite !qpermE /= !bindA !bindretf !alt_bindDl !bindretf /= !/liftM2.
repeat rewrite !qpermE !bindA bindretf !bindretf /=.
by rewrite -altA altACA !altA.
Qed.

End qperm_examples.

Section qperm_preserves_nondetMonad.
Variable M : nondetMonad.

(* NB: not used *)
Lemma qperm_preserves_elements (A : eqType) (s : seq A) :
  qperm s = qperm s >>= (fun x => guard (perm_eq x s) >> Ret x) :> M _.
Proof.
have [n ns] := ubnP (size s); elim: n s ns => // n ih s ns.
move: s ns => [ns |h t].
  by rewrite qperm_nil bindretf perm_refl guardT bindskipf.
rewrite /= ltnS => ns; rewrite qperm_cons bindA splits_guard_subseq !bindA.
bind_ext => -[a b]; rewrite /= !bindA; apply: bind_ext_guard => /and3P[_ _ abt].
rewrite !bindretf /liftM2 /= !bindA ih; last first.
  by rewrite (leq_trans _ ns) // ltnS -(perm_size abt) size_cat leq_addr.
rewrite !bindA; bind_ext => a'; rewrite !bindA; apply: bind_ext_guard => aa'.
rewrite !bindretf !bindA ih; last first.
  by rewrite (leq_trans _ ns) // ltnS -(perm_size abt) size_cat leq_addl.
rewrite !bindA; bind_ext => b'; rewrite !bindA; apply: bind_ext_guard => bb'.
rewrite !bindretf -[in X in _ = X >> _]cat_rcons -cats1 -catA perm_catCA.
by rewrite perm_cons (perm_trans (perm_cat aa' bb') abt) guardT bindskipf.
Qed.

End qperm_preserves_nondetMonad.

Section qperm_preserves_prePlusMonad.
Variable M : prePlusMonad.

Let qperm_preserves_size A : preserves (@qperm M A) size.
Proof.
move=> s; have [n ns] := ubnP (size s); elim: n s ns => // n ih s ns.
move: s ns => [ns|p s]; first by rewrite !qperm_nil !bindretf.
rewrite /= ltnS => ns; rewrite qpermE !bindA !dsplitsE !fmapE !bindA.
bind_ext => -[a b] /=; apply: bind_ext_dassert => -[{}a {}b /= abs _].
rewrite !bindretf (bind_liftM2_size _ _ 1%N); last first.
  by move=> x y; rewrite size_cat /= addn1 -addnS.
rewrite {1}/liftM2 ih; last first.
  by rewrite /dsplitsT1 /= (leq_trans _ ns)// ltnS -(eqP abs) leq_addr.
rewrite /liftM2 !bindA; bind_ext => xa; rewrite bindretf ih; last first.
  by rewrite /dsplitsT2 /= (leq_trans _ ns)// ltnS -(eqP abs) leq_addl.
by rewrite !bindA; bind_ext => xb; rewrite !bindretf /= (eqP abs) addn1.
Qed.

(* NB: easier to use than qperm_preserves_size? worth explaining? *)
Lemma qperm_preserves_size2 A (x : seq A) B (f : seq A -> nat -> M B) :
  (qperm x >>= f^~ (size x)) = qperm x >>= (fun x' => f x' (size x')) :> M _.
Proof.
transitivity (qperm x >>= (fun y => Ret (y, size y)) >>= (fun x' => f x'.1 x'.2)).
  by rewrite qperm_preserves_size bindA; bind_ext => s; rewrite bindretf.
by rewrite bindA; bind_ext => s; rewrite bindretf.
Qed.

Lemma bind_qperm_guard A (s : seq A) B (f : seq A -> M B) :
  qperm s >>= f = qperm s >>= (fun x => guard (size s == size x) >> f x).
Proof.
rewrite -(qperm_preserves_size2 s (fun a b => guard (size s == b) >> f a)).
rewrite eqxx guardT.
by under [in RHS]eq_bind do rewrite bindskipf.
Qed.

End qperm_preserves_prePlusMonad.

(* TODO: move this example *)
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
  if O \in s then fail else Ret (product s).

Let Work s := if O \in s then @fail M nat
              else Ret (product s).

(* work refined to eliminate multiple traversals *)
Lemma workE :
  let next := fun n (mx : M _) => if n == 0 then fail else fmap (muln n) mx in
  work = foldr next (Ret 1).
Proof.
apply foldr_universal => // h t; case: ifPn => [/eqP -> //| h0].
by rewrite /work inE eq_sym (negbTE h0) [_ || _]/= fmap_if fmap_fail.
Qed.

End work.
Arguments work {M}.

Variable M : exceptMonad.

Definition fastprod s : M _ := catch (work s) (Ret O).

Let Fastprod (s : seq nat) := @catch M nat (work s) (Ret O).

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

Let wadler94_sect31 : Ret 1 +m callcc (fun f => Ret 10 +m f 100) = Ret (1 + 100) :> M _.
Proof.
rewrite {1}/addM bindretf.
rewrite (_ : callcc _ = Ret 100) ?bindretf //.
transitivity (callcc (fun _ : nat -> M nat => Ret 100)); last by rewrite callcc1.
transitivity (callcc (fun f : nat -> M nat => Ret 10 >>= (fun a => f 100))); first by rewrite callcc2.
rewrite callcc3 //; congr callcc.
rewrite boolp.funeqE => g.
by rewrite bindretf.
Qed.

End continuation_example.

Section shiftreset_examples.
Variable (M : shiftresetMonad nat).

Let wadler94_sect32_1 :
  Ret 1 +m (reset (Ret 10 +m (shift (fun f : _ -> M nat => f 100 >>= f) : M _)) : M _) =
  Ret (1 + (10 + (10 + 100))).
Proof.
rewrite /addM.
rewrite bindretf.
transitivity ((Ret (10 + (10 + 100))) >>= (fun y => Ret (1 + y)) : M _); last first.
  by rewrite bindretf.
congr (bind _ _).
rewrite shiftreset3.
rewrite (_ : do x <- Ret 10; _ = do y <- shift (@^~ 100) : M _; Ret (10 + (10 + y)))%Do; last first.
  by rewrite bindretf.
by rewrite shiftreset4.
Qed.

Let wadler94_sect32_2 :
  Ret 1 +m (reset (Ret 10 +m (shift (fun f : _ -> M nat => Ret 100 : M _) : M _)) : M _) =
  Ret (1 + 100).
Proof.
rewrite /addM.
rewrite bindretf.
transitivity (Ret 100 >>= (fun y => Ret (1 + y)) : M _); last first.
  by rewrite bindretf.
congr (bind _ _). (* TODO : bind_ext casse *)
rewrite (shiftreset2 _ _).
by rewrite bindretf.
Qed.

End shiftreset_examples.

Definition refin (M : altMonad) A (m1 m2 : M A) : Prop := m1 [~] m2 = m2.
Notation "m1 `<=` m2" := (refin m1 m2).

Lemma refin_bindr (M : altMonad) A B (m1 m2 : M A) (f : A -> M B) :
  (m1 `<=` m2) -> (m1 >>= f `<=` m2 >>= f).
Proof. by move=> m12; rewrite /refin -alt_bindDl m12. Qed.

Lemma refin_if (M : altMonad) A (m1 m2 m1' m2' : M A) (b : bool) :
  (b -> m1 `<=` m1') -> (~~ b -> m2 `<=` m2') ->
  (if b then m1 else m2) `<=` (if b then m1' else m2').
Proof. by case: b => [+ _|_]; exact. Qed.

Section commute.
Variable M : plusMonad.
Variables (d : unit) (T : orderType d).

(* NB: on the model of nondetState_sub in state_lib.v *)
Definition nondetPlus_sub A (n : M A) := {m | ndDenote m = n}.

Lemma nondetPlus_sub_insert A (s : seq A) a : nondetPlus_sub (@insert M _ a s).
Proof.
elim: s => /= [|h t ih]; first by exists (ndRet [:: a]).
rewrite insertE /=; have [syn synE] := ih.
exists (ndAlt (ndRet [:: a, h & t]) (ndBind syn (fun x => ndRet (h :: x)))).
by rewrite /= synE fmapE.
Qed.

Lemma nondetPlus_sub_splits A (s : seq A) : nondetPlus_sub (splits s : M _).
Proof.
elim: s => [|h t ih /=]; first by exists (ndRet ([::], [::])).
have [syn syn_splits] := ih.
exists (ndBind syn (fun '(a, b) => ndAlt (ndRet (h :: a, b)) (ndRet (a, h :: b)))).
by rewrite /= syn_splits; bind_ext => -[].
Qed.

Lemma nondetPlus_sub_splits_bseq A (s : seq A) :
  nondetPlus_sub (splits_bseq s : M _).
Proof.
elim: s => [|h t ih]; first by exists (ndRet ([bseq], [bseq])).
have [syn syn_tsplits] := ih.
exists (ndBind syn (fun '(a, b) => ndAlt
    (ndRet ([bseq of h :: a], widen_bseq (leqnSn _) b))
    (ndRet (widen_bseq (leqnSn _) a, [bseq of h :: b])))).
by rewrite /= syn_tsplits; bind_ext => -[].
Qed.

Lemma nondetPlus_sub_liftM2 A B C (f : A -> B -> C) (ma : M A) (mb : M B) :
  nondetPlus_sub ma -> nondetPlus_sub mb ->
  nondetPlus_sub (liftM2 f ma mb).
Proof.
move=> [s1 s1_ma] [s2 s2_mb].
exists (ndBind s1 (fun a => ndBind s2 (fun b => ndRet (f a b)))).
by rewrite /= s1_ma s2_mb.
Qed.

Lemma nondetPlus_sub_qperm A (s : seq A) : nondetPlus_sub (qperm s : M _).
Proof.
have [n sn] := ubnP (size s); elim: n s => // n ih s in sn *.
move: s => [|h t] in sn *; first by exists (ndRet [::]); rewrite qperm_nil.
rewrite qperm_cons splitsE fmapE bindA.
have [syn syn_tsplits] := nondetPlus_sub_splits_bseq t.
have nondetPlus_sub_liftM2_qperm : forall a b : (size t).-bseq A,
  nondetPlus_sub (liftM2 (fun x y => x ++ h :: y) (qperm a) (qperm b : M _)).
  move=> a b; apply nondetPlus_sub_liftM2 => //; apply: ih.
  - by rewrite (leq_ltn_trans (size_bseq a)).
  - by rewrite (leq_ltn_trans (size_bseq b)).
exists (ndBind syn (fun a => sval (nondetPlus_sub_liftM2_qperm a.1 a.2))).
rewrite /= syn_tsplits; bind_ext => -[a b] /=.
by rewrite bindretf; case: (nondetPlus_sub_liftM2_qperm _ _).
Qed.

Lemma commute_plus A (m : M A) B (n : M B) C (f : A -> B -> M C) :
  nondetPlus_sub m -> commute m n f.
Proof.
case=> x; elim: x m n f => [{}A a m n f <-| D {}A n0 ih0 n1 ih1 m n2 f <- |
  D m n f <- | D n0 ih0 n1 ih1 m n2 f <-].
- rewrite /commute bindretf.
  by under [RHS]eq_bind do rewrite bindretf.
- rewrite /commute /= bindA.
  under eq_bind. move=> x; rewrite (ih1 x) //. over.
  by rewrite ih0 //; under eq_bind do rewrite -bindA.
- rewrite /commute /= bindfailf.
  under eq_bind do rewrite bindfailf.
  by rewrite bindmfail.
- rewrite /commute /= alt_bindDl.
  under [RHS]eq_bind do rewrite alt_bindDl.
  by rewrite alt_bindDr ih0 // ih1.
Qed.

Lemma commute_guard (b : bool) B (n : M B) C (f : unit -> B -> M C) :
  commute (guard b) n f.
Proof.
apply commute_plus; exists (if b then ndRet tt else @ndFail _).
by case: ifP; rewrite (guardT, guardF).
Qed.

End commute.

Section splits_plusMonad.
Context {M : plusMonad}.

Lemma iperm_cons_splits (A : eqType) (s : seq A) p :
  iperm (p :: s) = splits s >>= (fun '(ys, zs) =>
                  liftM2 (fun x y => x ++ p :: y) (iperm ys) (iperm zs)) :> M _.
Proof.
have [n ns] := ubnP (size s); elim: n s ns => // n ih s ns.
move: s ns => [ns |h t].
  by rewrite /= bindretf insertE bindretf /= /liftM2 /= !bindretf.
rewrite [in X in X -> _]/= ltnS => ns.
rewrite [in RHS]/= bindA.
under eq_bind do rewrite alt_bindDl 2!bindretf.
transitivity (iperm [:: h, p & t] : M _).
  by apply: perm_eq_iperm; rewrite -cat1s -(cat1s h) perm_catCA.
rewrite [p :: t]lock /= -lock ih // bindA; bind_ext => -[a b] /=.
rewrite liftM2E /liftM2 /= bindA -alt_bindDr; bind_ext => a'.
rewrite bindA (_ : commute (insert h a') _ _) //; last first.
  exact/commute_plus/nondetPlus_sub_insert.
rewrite -alt_bindDr.
by under eq_bind do rewrite insert_cat.
Qed.

End splits_plusMonad.

Section qperm_lemmas.
Context {M : plusMonad} {A : eqType}.

Lemma iperm_qperm : @iperm M A = @qperm M A.
Proof.
rewrite boolp.funeqE => s.
have [n ns] := ubnP (size s); elim: n s ns => // n ih s ns.
move: s ns => [na |h t]; first by rewrite qperm_nil.
rewrite [in X in X -> _]/= ltnS => ns.
rewrite qperm_cons iperm_cons_splits splits_guard_subseq !bindA.
bind_ext => -[a b] /=; rewrite !bindA.
apply: bind_ext_guard => /and3P[ta tb _].
rewrite !bindretf ih; last first.
  by rewrite (leq_trans _ ns)// ltnS; apply: size_subseq.
by rewrite ih // (leq_trans _ ns)// ltnS; apply: size_subseq.
Qed.

Lemma perm_eq_qperm (a b : seq A) : perm_eq a b -> qperm a = qperm b :> M _.
Proof. by rewrite -!iperm_qperm; exact: perm_eq_iperm. Qed.

Lemma qperm_cons_rcons h (t : seq A) : qperm (h :: t) = qperm (rcons t h) :> M _.
Proof. by apply: perm_eq_qperm; rewrite perm_sym perm_rcons perm_refl. Qed.

(* NB: postulate perm-snoc in Nondet.agda *)
Lemma qperm_rcons (s : seq A) x :
  qperm (rcons s x) = qperm s >>= (fun s' => qperm (rcons s' x)) :> M _.
Proof. by rewrite -iperm_qperm iperm_rcons_bind. Qed.

(* NB: postulate perm-idempotent in Nondet.agda *)
Lemma qperm_idempotent : qperm >=> qperm = qperm :> (seq A -> M (seq A)).
Proof. by rewrite -iperm_qperm iperm_idempotent. Qed.

End qperm_lemmas.

Import Order.TTheory.
Local Open Scope order_scope.

Section refin_lemmas_altCIMonad.
Variable M : altCIMonad.
Implicit Types A : UU0.

Lemma refin_refl A (a : M A) : a `<=` a.
Proof. by rewrite /refin altmm. Qed.

Lemma eq_refin A (a b : M A) : a = b -> a `<=` b.
Proof. by move=> ->; exact: refin_refl. Qed.

Lemma refin_trans A (b a c : M A) : a `<=` b -> b `<=` c -> a `<=` c.
Proof. by rewrite /refin => h1 <-; rewrite altA h1. Qed.

Lemma refin_antisym A (a b : M A) : a `<=` b -> b `<=` a -> a = b.
Proof. by rewrite /refin => h1 <-; rewrite altC. Qed.

Lemma refin_alt A (m1 m1' m2 m2' : M A) :
  m1 `<=` m1' -> m2 `<=` m2' -> m1 [~] m2 `<=` m1' [~] m2'.
Proof. by move=> h1 h2; rewrite /refin altACA h1 h2. Qed.

Lemma refinR A (a b : M A) : a `<=` a [~] b.
Proof. by rewrite /refin altA altmm. Qed.

End refin_lemmas_altCIMonad.

Definition lrefin {M : altMonad} A B (f g : A -> M B) := forall x, f x `<=`g x.
Notation "f `<.=` g" := (lrefin f g).

Section lrefin_lemmas_altCIMonad.
Variable M : altCIMonad.

Lemma lrefin_refl A B (a : A -> M B) : a `<.=` a.
Proof. by move => ?; exact: refin_refl. Qed.

Lemma lrefin_trans A B (b a c : A -> M B) : a `<.=` b -> b `<.=` c -> a `<.=` c.
Proof. by move => ? ? ?; exact: refin_trans. Qed.

Lemma lrefin_antisym A B (a b : A -> M B) : a `<.=` b -> b `<.=` a -> a = b.
Proof. move => ? ?; rewrite boolp.funeqE => ?; exact: refin_antisym. Qed.
End lrefin_lemmas_altCIMonad.

Lemma refin_bindl (M : prePlusMonad) A B (m : M A) (f g : A -> M B) :
  (f `<.=` g) -> (m >>= f `<=` m >>= g).
Proof. by move=> fg; rewrite /refin -alt_bindDr; bind_ext => a; exact: fg. Qed.

Lemma refin_bind (M : plusMonad) A B {m n : M A} {f g : A -> M B} :
  m `<=` n -> f `<.=` g -> (m >>= f) `<=` (n >>= g).
Proof.
by move=> mn /refin_bindl ?; exact: (refin_trans _ (refin_bindr _ mn)).
Qed.

Lemma refin_liftM2 (M : plusMonad) (A B C : UU0) {f : A -> B -> C}
    {m1 n1 : M A} {m2 n2 : M B} :
  m1 `<=` n1 -> m2 `<=` n2 -> liftM2 f m1 m2 `<=` liftM2 f n1 n2.
Proof.
move=> mn1 mn2; rewrite /liftM2.
by apply: (refin_bind mn1 _) => a; exact: refin_bindr.
Qed.

Lemma refin_guard_le (M : plusMonad) (d : unit) (T : orderType d) (x y : T) :
  (guard (~~ (y <= x)%O) : M _) `<=` guard (x <= y)%O.
Proof.
rewrite -ltNge le_eqVlt.
case: guardPn => H.
rewrite orbT guardT; exact: refin_refl.
by rewrite orbF /refin altfailm.
Qed.

Lemma refin_if_guard (M : plusMonad) A (p : bool) (m1 m2 : M A) :
  (if p then m1 else m2) `<=` (guard p >> m1) [~] (guard (~~ p) >> m2).
Proof.
rewrite /refin; case: ifPn => /= [pT|pF]; rewrite !(guardT,guardF).
by rewrite bindskipf bindfailf altA altmm.
by rewrite bindfailf bindskipf altCA altmm.
Qed.

(* NB: worth explaining *)
Lemma refin_bind_guard {M : plusMonad} A (b : bool) (m1 m2 : M A) :
  (b -> m2 `<=` m1) -> guard b >> m2 `<=` guard b >> m1.
Proof.
case: b => [h|_]; first by apply: refin_bindl => -[]; exact: h.
by rewrite guardF !bindfailf; exact: refin_refl.
Qed.

Lemma refin_ret_insert (M : altCIMonad) (A : UU0) h (t : seq A) :
  Ret (h :: t) `<=` (insert h t : M _).
Proof.
elim: t h => [h|t1 t2 ih h]; first by rewrite insertE; exact: refin_refl.
by rewrite insertE; exact: refinR.
Qed.

Lemma refin_ret_iperm (M : plusMonad) (A : UU0) (s : seq A) :
  (Ret s : M _) `<=` iperm s.
Proof.
by case: (@iperm_is_alt_ret M _ s) => m ->; rewrite /refin altA altmm.
Qed.

(* NB: postulate return⊑perm in in Nondet.agda *)
Lemma refin_qperm_ret (M : plusMonad) (A : eqType) (s : seq A) :
  (Ret s : M _) `<=` qperm s.
Proof. by rewrite -iperm_qperm; exact: refin_ret_iperm. Qed.

Lemma qperm_refin_rcons (M : plusMonad) (A : eqType) h (t : seq A) :
  (Ret (rcons t h) : M _) `<=` qperm (h :: t).
Proof. by rewrite qperm_cons_rcons; exact: refin_qperm_ret. Qed.

Lemma qperm_refin_cons (M : plusMonad) (A : eqType) h (t : seq A) :
  (Ret (h :: t) : M _) `<=` qperm (rcons t h).
Proof. by rewrite -qperm_cons_rcons; exact: refin_qperm_ret. Qed.
