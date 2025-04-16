(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2025 monae authors, license: LGPL-2.1-or-later               *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require boolp.
Require Import preamble.
From HB Require Import structures.
Require Import hierarchy monad_lib alt_lib.
From infotheo Require convex necset.
From Equations Require Import Equations.

(**md**************************************************************************)
(* # Definitions and lemmas using failure and nondeterministic monads         *)
(*                                                                            *)
(* ```                                                                        *)
(*                 hyloM == [2, Sect. 5.1]                                    *)
(*          nondetSyntax == syntax of nondeterministic monad                  *)
(*                          (constructors: ndRet ndBind ndFail ndAlt)         *)
(*           nondetSem x == semantics of x : nondetSyntax                     *)
(*              select s == nondeterministically splits the list s into a     *)
(*                          pair of one chosen element and the rest           *)
(*                          [3, Sect. 4.4] [2, Sect. 3.2]                     *)
(*             tselect s == same as select but returns a pair whose second    *)
(*                          projection has type (size s).-1.-tuple A, useful  *)
(*                          to write perms                                    *)
(*               perms s == of type seq A -> M (seq A), nondeterministically  *)
(*                          computes a permutation of s using (t)select       *)
(*               uperm s == nondeterministically computes a permutation of s, *)
(*                          defined using unfoldM and select [2, Sect. 3.2]   *)
(*           dassert p a == computation of type M {x | p x} that fails if a   *)
(*                          does not satisfy p or return a otherwise (with a  *)
(*                          proof that is satisfies p)                        *)
(*             dsplits s == same as split with an enriched return type        *)
(*                          M {x : seq A * seq A | size x.1 + size x.2 == n}  *)
(*       plus_isNondet m == m is a computation of the plusMonad that can be   *)
(*                          written with the syntax of the nondeterministic   *)
(*                          monad                                             *)
(* ```                                                                        *)
(*                                                                            *)
(* ref:                                                                       *)
(* - [1] mu2019tr2                                                            *)
(* - [2] mu2019tr3                                                            *)
(* - [3] gibbons2011icfp                                                      *)
(* - [4] mu2020flops                                                          *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.

Lemma bind_ext_guard {M : failMonad} (A : UU0) (b : bool) (m1 m2 : M A) :
  (b -> m1 = m2) -> guard b >> m1 = guard b >> m2.
Proof. by case: b => [->//|_]; rewrite guardF !bindfailf. Qed.

Lemma fmap_fail {A B : UU0} (M : failMonad) (f : A -> B) :
  (M # f) fail = fail.
Proof. by rewrite fmapE bindfailf. Qed.

Definition bassert_hylo {M : failMonad} (A B : UU0)
  (f : B -> M (A * B)%type) (p : pred B) (r : forall p f, B -> B -> bool) :=
  forall b, f b = bassert (fun z => r p f z.2 b) (f b).

Definition bassert_size {M : failMonad} (A B : UU0)
  (f : seq B -> M (A * seq B)%type) :=
  @bassert_hylo M _ _ f predT (fun _ _ x y => size x < size y).

Section unfoldM_failMonad.
Variables (M : failMonad) (A B' : UU0).
Let B := seq B'.
Notation unfoldM := (@unfoldM M A _ _ (@well_founded_size B')).
Variables (p : pred B) (f : B -> M (A * B)%type).

Hypothesis decr_size : bassert_size f.

Local Open Scope mprog.

Lemma unfoldME y : unfoldM p f y =
  if p y then Ret [::]
  else f y >>= (fun xz => fmap (cons xz.1) (unfoldM p f xz.2)).
Proof.
rewrite /unfoldM Init.Wf.Fix_eq; last first.
  move => b g g' H; rewrite /unfoldM'; case: ifPn => // pb.
  bind_ext => -[a' b'] /=.
  by destruct Bool.bool_dec => //; rewrite H.
rewrite /unfoldM'; case: ifPn => // py.
rewrite decr_size /bassert 2!bindA; bind_ext => -[a' b'].
case: assertPn => b'y; last by rewrite 2!bindfailf.
by rewrite 2!bindretf /= b'y.
Qed.

End unfoldM_failMonad.

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

Module SyntaxNondet.

Inductive t : Type -> Type :=
| ret : forall A, A -> t A
| bind : forall B A, t B -> (B -> t A) -> t A
| fail : forall A, t A
| alt : forall A, t A -> t A -> t A.

Fixpoint sem {M : nondetMonad} {A} (m : t A) : M A :=
  match m with
  | ret A a => Ret a
  | bind A B m f => sem m >>= (sem \o f)
  | fail A => hierarchy.fail
  | alt A m1 m2 => sem m1 [~] sem m2
  end.

Module Exports.
Notation nondetSyntax := t.
Notation ndAlt := alt.
Notation ndRet := ret.
Notation ndBind := bind.
Notation ndFail := fail.
Notation nondetSem := sem.
End Exports.
End SyntaxNondet.
Export SyntaxNondet.Exports.

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
apply: funext_dep => s; rewrite kleisliE.
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
rewrite {1}/perms Init.Wf.Fix_eq //; [by case: s|move=> s' f g H].
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
Context {M : failMonad} {A : UU0}.

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

Module qperm_function.
Section qperm_function.
Context (M : plusMonad) (A : UU0) d (T : orderType d).

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
rewrite (_ : f = g) //; apply funext_dep => s.
by apply boolp.funext => ?; exact: H.
Qed.
End qperm_function.
End qperm_function.

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
by apply boolp.funext => g; rewrite bindretf.
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

(* NB: see also nondetState_isNondet *)
Definition plus_isNondet {M : plusMonad} A (n : M A) := {m | nondetSem m = n}.

Section plus_commute.
Context {M : plusMonad}.

Lemma plus_commute A (m : M A) B (n : M B) C (f : A -> B -> M C) :
  plus_isNondet m -> commute m n f.
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

Lemma liftM2_isNondet A B C (f : A -> B -> C) (ma : M A) (mb : M B) :
  plus_isNondet ma -> plus_isNondet mb -> plus_isNondet (liftM2 f ma mb).
Proof.
move=> [s1 s1_ma] [s2 s2_mb].
exists (ndBind s1 (fun a => ndBind s2 (fun b => ndRet (f a b)))).
by rewrite /= s1_ma /comp /= s2_mb.
Qed.

Lemma guard_isNondet (b : bool) : plus_isNondet (guard b : M _).
Proof.
exists (if b then ndRet tt else @ndFail _).
by case: ifP; rewrite (guardT, guardF).
Qed.

Lemma insert_isNondet A (s : seq A) a : plus_isNondet (@insert M _ a s).
Proof.
elim: s => /= [|h t ih]; first by exists (ndRet [:: a]).
rewrite insertE /=; have [syn synE] := ih.
exists (ndAlt (ndRet [:: a, h & t]) (ndBind syn (fun x => ndRet (h :: x)))).
by rewrite /= synE fmapE.
Qed.

Lemma splits_isNondet A (s : seq A) : plus_isNondet (splits s : M _).
Proof.
elim: s => [|h t ih /=]; first by exists (ndRet ([::], [::])).
have [syn syn_splits] := ih.
exists (ndBind syn (fun '(a, b) => ndAlt (ndRet (h :: a, b)) (ndRet (a, h :: b)))).
by rewrite /= syn_splits; bind_ext => -[].
Qed.

Lemma splits_bseq_isNondet A (s : seq A) : plus_isNondet (splits_bseq s : M _).
Proof.
elim: s => [|h t ih]; first by exists (ndRet ([bseq], [bseq])).
have [syn syn_tsplits] := ih.
exists (ndBind syn (fun '(a, b) => ndAlt
    (ndRet ([bseq of h :: a], widen_bseq (leqnSn _) b))
    (ndRet (widen_bseq (leqnSn _) a, [bseq of h :: b])))).
by rewrite /= syn_tsplits; bind_ext => -[].
Qed.

Lemma qperm_isNondet A (s : seq A) : plus_isNondet (qperm s : M _).
Proof.
have [n sn] := ubnP (size s); elim: n s => // n ih s in sn *.
move: s => [|h t] in sn *; first by exists (ndRet [::]); rewrite qperm_nil.
rewrite qperm_cons splits_bseqE fmapE bindA.
have [syn syn_tsplits] := splits_bseq_isNondet t.
have liftM2_qperm_isNondet (a b : (size t).-bseq A) :
  plus_isNondet (liftM2 (fun x y => x ++ h :: y) (qperm a) (qperm b : M _)).
  apply: liftM2_isNondet => //; apply: ih.
  - by rewrite (leq_ltn_trans (size_bseq a)).
  - by rewrite (leq_ltn_trans (size_bseq b)).
exists (ndBind syn (fun a => sval (liftM2_qperm_isNondet a.1 a.2))).
rewrite /= syn_tsplits; bind_ext => -[a b] /=.
by rewrite bindretf; case: (liftM2_qperm_isNondet _ _).
Qed.

End plus_commute.

Arguments plus_commute {M A} m {B} n {C} f.
#[global] Hint Extern 0 (liftM2_isNondet (guard _)) =>
  solve[exact: liftM2_isNondet] : core.
#[global] Hint Extern 0 (plus_isNondet (guard _)) =>
  solve[exact: guard_isNondet] : core.
#[global] Hint Extern 0 (plus_isNondet (insert _ _)) =>
  solve[exact: insert_isNondet] : core.
#[global] Hint Extern 0 (plus_isNondet (splits _)) =>
  solve[exact: splits_isNondet] : core.
#[global] Hint Extern 0 (plus_isNondet (splits_bseq _)) =>
  solve[exact: splits_bseq_isNondet] : core.
#[global] Hint Extern 0 (plus_isNondet (qperm _)) =>
  solve[exact: qperm_isNondet] : core.

Section splits_plusMonad.
Context {M : plusMonad}.

Lemma guard_splits {T A : UU0} (p : pred T) (t : seq T) (f : seq T * seq T -> M A) :
  splits t >>= (fun x => guard (all p t) >> f x) =
  splits t >>= (fun x => guard (all p x.1) >> guard (all p x.2) >> f x).
Proof.
rewrite -plus_commute//.
elim: t => [|h t ih] in p f *; first by rewrite /= !bindretf.
rewrite [LHS]/= guard_and 2!bindA ih /= plus_commute//.
rewrite bindA; bind_ext => -[a b] /=.
rewrite !alt_bindDl !bindretf /= !guard_and !bindA !alt_bindDr.
by congr (_ [~] _); rewrite plus_commute.
Qed.

(* NB: corresponds to perm-preserves-all? *)
Lemma guard_all_qperm {T B : UU0} (p : pred T) s (f : seq T -> M B) :
  qperm s >>= (fun x => guard (all p s) >> f x) =
  qperm s >>= (fun x => guard (all p x) >> f x).
Proof.
rewrite -plus_commute//.
have [n leMn] := ubnP (size s); elim: n => // n ih in s f leMn *.
case: s leMn => [|h t]; first by move=> _; rewrite qperm_nil !bindretf.
rewrite ltnS => tn.
rewrite qperm_cons !bindA /= guard_and bindA (@plus_commute _ _ (guard (all p t)))//.
rewrite guard_splits splits_bseqE fmapE 2!bindA plus_commute//.
bind_ext => -[a b]; rewrite 2!bindretf !bindA /=.
rewrite (@plus_commute _ _ (guard (all p b)))//.
rewrite ih; last by rewrite (leq_trans _ tn) //= ltnS size_bseq.
rewrite (@plus_commute _ _(guard (p h)))//.
bind_ext => a'; rewrite !bindA (@plus_commute _ _ (guard (p h)))//.
rewrite ih; last by rewrite (leq_trans _ tn) //= ltnS size_bseq.
rewrite (@plus_commute _ _ (guard (p h)))// plus_commute//.
bind_ext => b'; rewrite !bindretf all_cat /= andbA andbAC !guard_and !bindA.
by under eq_bind do rewrite plus_commute//.
Qed.

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
rewrite bindA (plus_commute (insert h a'))// -alt_bindDr.
by under eq_bind do rewrite insert_cat.
Qed.

End splits_plusMonad.

Section qperm_lemmas.
Context {M : plusMonad} {A : eqType}.

Lemma iperm_qperm : @iperm M A = @qperm M A.
Proof.
(*rewrite boolp.funeqE => s.
apply qperm_elim => [//|h t ihys ihzs].
rewrite iperm_cons_splits splits_bseqE fmapE bindA.
bind_ext => -[a b]; rewrite bindretf.
by rewrite (ihys (a, b) _ b) (ihzs (a, b) a).
Qed.*)
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

Lemma refin_guard_le (M : plusMonad) d (T : orderType d) (x y : T) :
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
