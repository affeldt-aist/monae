(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2025 monae authors, license: LGPL-2.1-or-later               *)
From mathcomp Require Import all_ssreflect.
Require Import ipreamble.
From HB Require Import structures.
Require Import ihierarchy ialt_lib imonad_lib.
From Equations Require Import Equations.

(**md**************************************************************************)
(* # Definitions and lemmas using failure and nondeterministic monads         *)
(*                                                                            *)
(* ```                                                                        *)
(*                 hyloM == [2, Sect. 5.1]                                    *)
(*              select s == nondeterministically splits the list s into a     *)
(*                          pair of one chosen element and the rest           *)
(*                          [3, Sect. 4.4] [2, Sect. 3.2]                     *)
(*               uperm s == nondeterministically computes a permutation of s, *)
(*                          defined using unfoldM and select [2, Sect. 3.2]   *)
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
rewrite -Order.TotalTheory.ltNge Order.POrderTheory.le_eqVlt.
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
