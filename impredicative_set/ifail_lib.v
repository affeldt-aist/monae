(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2020 monae authors, license: LGPL-2.1-or-later               *)
From mathcomp Require Import all_ssreflect.
Require Import imonae_lib.
From HB Require Import structures.
Require Import ihierarchy imonad_lib.
From Equations Require Import Equations.

(******************************************************************************)
(*     Definitions and lemmas using failure and nondeterministic monads       *)
(*                                                                            *)
(*                   arb == arbitrary nondeterministic choice between         *)
(*                          booleans                                          *)
(*                 foldM                                                      *)
(*         unfoldM p f y == generates a list a from a seed y, if p y holds    *)
(*                          the generation stops,otherwise an element and a   *)
(*                          new seed of generated using f                     *)
(*                 hyloM == [2, Sect. 5.1]                                    *)
(*       arbitrary def s == nondeterministic choice of an element in the list *)
(*                          s and def if the list is empty                    *)
(*                subs s == subsequence of a list                             *)
(*                          (ref: Sect. 3.1, gibbons2012utp)                  *)
(*            insert a s == insert a in the list s nondeterministically       *)
(*               iperm s == nondeterministic permutation of the list s,       *)
(*                          defined as a Fixpoint using insert [1, Sect. 3]   *)
(*              select s == nondeterministically splits the list s into a     *)
(*                          pair of one chosen element and the rest           *)
(*                       [2, Sect. 3.2]                                       *)
(*               uperm s == nondeterministically computes a permutation of s, *)
(*                          defined using unfoldM and select [2, Sect. 3.2]   *)
(*              splits s == split a list nondeterministically                 *)
(*                          type: seq A -> M (seq A * seq A)                  *)
(*            m1 `<=` m2 == m1 refines m2, i.e., every result of m1 is a      *)
(*                          possible result of m2                             *)
(*             f `<.=` g == refinement relation lifted to functions, i.e.,    *)
(*                          forall x, f x `<=` g x                            *)
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
rewrite /unfoldM Init.Wf.Fix_eq; last first.
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
rewrite /hyloM Init.Wf.Fix_eq; last first.
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

Section subsequences_of_a_list.
Local Open Scope mprog.

Variables (M : altMonad) (A : UU0).

Fixpoint subs (s : seq A) : M (seq A) :=
  if s isn't h :: t then Ret [::] else
  let t' := subs t in
  fmap (cons h) t' [~] t'.

(*Fixpoint SUBS (s : list A) : MonadAlt.sort M (list A) :=
  if s isn't h :: t then
      @Natural.cpnt ssrfun_idfun__canonical__ihierarchy_Functor
        (@Functor.Pack (Monad.sort (ihierarchy_MonadAlt__to__ihierarchy_Monad M))
           (@Functor.Class (Monad.sort (ihierarchy_MonadAlt__to__ihierarchy_Monad M))
              (@Monad.ihierarchy_isFunctor_mixin (Monad.sort (ihierarchy_MonadAlt__to__ihierarchy_Monad M))
                 (Monad.class (ihierarchy_MonadAlt__to__ihierarchy_Monad M))))) (@ret (ihierarchy_MonadAlt__to__ihierarchy_Monad M))
        (list A) (@nil A)
  else
      let t' : MonadAlt.sort M (list A) := SUBS t in
      @alt M (list A) (@actm (ihierarchy_MonadAlt__to__ihierarchy_Functor M) (list A) (list A) (@cons A h) t') t'.
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
apply funext; elim => [|y xs IH].
  by rewrite fcompE insertE -(compE (fmap (map f))) (natural ret) compE insertE.
apply/esym.
rewrite fcompE insertE alt_fmapDr.
(* first branch *)
rewrite -(compE (fmap (map f))) (natural ret) FIdE [in X in X [~] _ ]/=.
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
  by rewrite fcompE insertE -(compE (fmap _)) (natural ret) FIdE /= (negbTE pa).
rewrite fcompE insertE alt_fmapDr.
rewrite -(compE (fmap _)) (natural ret) FIdE [in X in X [~] _]/= (negbTE pa).
case: ifPn => ph.
- rewrite -fmap_oE (_ : filter p \o cons h = cons h \o filter p); last first.
    by apply funext => x /=; rewrite ph.
  rewrite fmap_oE.
  move: (IH); rewrite fcompE => ->.
  by rewrite fmapE /= ph bindretf /= Mmm.
- rewrite -fmap_oE (_ : filter p \o cons h = filter p); last first.
    by apply funext => x /=; rewrite (negbTE ph).
  by move: (IH); rewrite fcompE => -> /=; rewrite (negbTE ph) Mmm.
Qed.

Lemma filter_insertT a : p a ->
  filter p (o) insert a = insert a \o filter p :> (_ -> M _).
Proof.
move=> pa; apply funext; elim => [|h t IH].
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
    by apply funext => x /=; rewrite (negbTE ph).
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
apply funext; elim => [|h t ih].
  by rewrite fcompE insertE fmapE bindretf.
rewrite fcompE insertE compE alt_fmapDr fmapE bindretf compE [in RHS]rev_cons.
rewrite insert_rcons rev_cons -cats1 rev_cons -cats1 -catA; congr (_ [~] _).
move: ih; rewrite fcompE [X in X -> _]/= => <-.
rewrite -!fmap_oE. congr (fmap _ (insert a t)).
by apply funext => s; rewrite /= -rev_cons.
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
apply funext; elim => [/=|x xs IH].
  by rewrite fcompE [iperm _]/= -[in RHS]compE (natural ret).
by rewrite fcompE [in iperm _]/= fmap_bind -insert_map -bind_fmap -fcompE -IH.
Qed.

Hypothesis Mmm : forall A, idempotent (@alt _ A : M A -> M A -> M A).

Variables (A : UU0) (p : pred A).

(* netys2017 *)
Lemma iperm_filter : iperm \o filter p = filter p (o) iperm :> (_ -> M _).
Proof.
apply funext; elim => [|h t /= IH].
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

End iperm_plusMonad.

Section select.
Variables (M : nondetMonad) (A : UU0).
Implicit Types s : seq A.

Fixpoint select s : M (A * seq A)%type :=
  if s isn't h :: t then fail else
  (Ret (h, t) [~] select t >>= (fun x => Ret (x.1, h :: x.2))).
(* NB: see .. for the theory of select *)

End select.
Arguments select {M} {A}.

Section uperm.
Variables (A : UU0) (M : nondetMonad).

Definition uperm : seq A -> M (seq A) :=
  unfoldM (@well_founded_size _) (@nilp _) select.
(* NB: see .. for the theory of mu_perm *)

End uperm.
Arguments uperm {A} {M}.

Section splits.
Context {M : altMonad} {A : UU0}.
Implicit Types s : seq A.

Fixpoint splits s : M (seq A * seq A)%type :=
  if s isn't x :: xs then Ret ([::], [::]) else
    splits xs >>= (fun yz => Ret (x :: yz.1, yz.2) [~] Ret (yz.1, x :: yz.2)).

End splits.

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
by apply funext => g; rewrite bindretf.
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
congr (bind _ _).
rewrite (shiftreset2 _ _).
by rewrite bindretf.
Qed.

End shiftreset_examples.

Definition refin {M : altMonad} A (m1 m2 : M A) : Prop := m1 [~] m2 = m2.
Notation "m1 `<=` m2" := (refin m1 m2).

Lemma refin_bindr (M : altMonad) A B (m1 m2 : M A) (f : A -> M B) :
  (m1 `<=` m2) -> (m1 >>= f `<=` m2 >>= f).
Proof. by move=> m12; rewrite /refin -alt_bindDl m12. Qed.

Lemma refin_if (M : altMonad) A (m1 m2 m1' m2' : M A) (b : bool) :
  (b -> m1 `<=` m1') -> (~~ b -> m2 `<=` m2') ->
  (if b then m1 else m2) `<=` (if b then m1' else m2').
Proof. by case: b => [+ _|_]; exact. Qed.

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
Proof. move => ? ?; apply funext => ?; exact: refin_antisym. Qed.
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
