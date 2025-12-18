(* monae: Monadic equational reasoning in Rocq                                *)
(* Copyright (C) 2025 monae authors, license: LGPL-2.1-or-later               *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require boolp.
Require Import preamble.
From HB Require Import structures.
Require Import hierarchy monad_lib.
From infotheo Require convex necset.
From Equations Require Import Equations.

(**md**************************************************************************)
(* # Definitions and lemmas using nondeterminism but no failure               *)
(*                                                                            *)
(* ```                                                                        *)
(*                   arb == arbitrary nondeterministic choice between         *)
(*                          booleans                                          *)
(*       arbitrary def s == nondeterministic choice of an element in the list *)
(*                          s and def if the list is empty                    *)
(*                subs s == subsequence of a list                             *)
(*                          (ref: Sect. 3.1, gibbons2012utp)                  *)
(*            insert a s == insert a in the list s nondeterministically       *)
(*               iperm s == nondeterministic permutation of the list s,       *)
(*                          defined as a Fixpoint using insert [1, Sect. 3]   *)
(*              splits s == split a list nondeterministically                 *)
(*                          type: seq A -> M (seq A * seq A)                  *)
(*                          with M : altMonad                                 *)
(*         splits_bseq s == same as splits with an enriched return type       *)
(*                          M ((size s).-bseq A * (size s).-bseq A))          *)
(*               qperm s == permute the list s                                *)
(*                          type: seq A -> M (seq A) with M : altMonad        *)
(*            m1 `<=` m2 == m1 refines m2, i.e., every result of m1 is a      *)
(*                          possible result of m2                             *)
(*             f `<.=` g == refinement relation lifted to functions, i.e.,    *)
(*                          forall x, f x `<=` g x                            *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "m1 `<=` m2" (at level 70, no associativity).
Reserved Notation "f `<.=` g" (at level 70, no associativity).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* TODO: move *)
Lemma mem_rcons_cat (A : eqType) (b : seq A) h : h \in b ->
  exists b1 b2, b = rcons b1 h ++ b2.
Proof.
move=> hb; exists (take (index h b) b), (drop (index h b).+1 b).
rewrite -cats1 -catA -{1}(cat_take_drop (index h b) b); congr (_ ++ _) => /=.
by rewrite -{2}(nth_index h hb) -drop_nth // index_mem.
Qed.

(* TODO: move *)
Lemma well_founded_size A : well_founded (fun x y : seq A => size x < size y).
Proof. by apply: (@Wf_nat.well_founded_lt_compat _ size) => ? ? /ltP. Qed.

Definition arb {M : altMonad} : M bool := Ret true [~] Ret false.

Section altci_semilatttype.
Import necset SemiLattice.
Variable M : altCIMonad.
Variable T : Type.

Definition altCI_semiLattType := M T.

HB.instance Definition _ := boolp.gen_eqMixin altCI_semiLattType.
HB.instance Definition _ := boolp.gen_choiceMixin altCI_semiLattType.

HB.instance Definition _ := @isSemiLattice.Build altCI_semiLattType
  (fun x y => x [~] y)
  (@altC M T) (@altA M T) (@altmm M T).

Local Open Scope latt_scope.

Lemma alt_lub (x y : altCI_semiLattType) : x [~] y = x [+] y.
Proof. by []. Qed.

End altci_semilatttype.

Section monadalt_lemmas.
Variable (M : altMonad).
Local Open Scope monae_scope.

Lemma alt_fmapDr (A B : UU0) (f : A -> B) (m1 m2 : M A) :
  (M # f) (m1 [~] m2) = (M # f) m1 [~] (M # f) m2.
Proof. by rewrite 3!fmapE alt_bindDl. Qed.

End monadalt_lemmas.

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

Local Open Scope monae_scope.

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
  (0 < size y)%N ->
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

Lemma arbitrary_flatten (A : UU0) def (s : seq A) (f : A -> A) : (0 < size s)%N ->
  (do x <- arbitrary def s; Ret (f x))%Do =
  arbitrary def (flatten [seq [:: f y] | y <- s]) :> M _.
Proof.
elim: s f => // a [_ f _ /=|h t ih f _].
  by rewrite /arbitrary /= bindretf.
rewrite [h :: t]lock /= -lock [in RHS]arbitrary_cons// -ih//.
by rewrite arbitrary_cons// alt_bindDl bindretf.
Qed.

Lemma arbitrary_flatten2 (A : UU0) def (s : seq A) (f g : A -> A) : (0 < size s)%N ->
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
Variables (M : altMonad) (A : UU0).
Local Open Scope mprog.
Local Open Scope monae_scope.

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
apply boolp.funext; elim => [|y xs IH].
  by rewrite fcompE insertE -(compE (fmap (map f))) (natural ret) compE insertE.
apply/esym.
rewrite fcompE insertE alt_fmapDr.
(* first branch *)
rewrite -(compE (fmap (map f))) (natural ret) FIdE [in X in X [~] _ ]/=.
(* second branch *)
rewrite -fmap_oE (_ : map f \o cons y = cons (f y) \o map f) //.
by rewrite fmap_oE -(fcompE (map f)) -IH [RHS]/= insertE.
Qed.

Hypothesis Mmm : forall A, idempotent_op (@alt _ A : M A -> M A -> M A).

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
    by apply boolp.funext => x /=; rewrite ph.
  rewrite fmap_oE.
  move: (IH); rewrite fcompE => ->.
  by rewrite fmapE /= ph bindretf /= Mmm.
- rewrite -fmap_oE (_ : filter p \o cons h = filter p); last first.
    by apply boolp.funext => x /=; rewrite (negbTE ph).
  by move: (IH); rewrite fcompE => -> /=; rewrite (negbTE ph) Mmm.
Qed.

Lemma filter_insertT a : p a ->
  filter p (o) insert a = insert a \o filter p :> (_ -> M _).
Proof.
move=> pa; apply boolp.funext; elim => [|h t IH].
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
    by apply boolp.funext => x /=; rewrite (negbTE ph).
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
apply boolp.funext; elim => [|h t ih].
  by rewrite fcompE insertE fmapE bindretf.
rewrite fcompE insertE compE alt_fmapDr fmapE bindretf compE [in RHS]rev_cons.
rewrite insert_rcons rev_cons -cats1 rev_cons -cats1 -catA; congr (_ [~] _).
move: ih; rewrite fcompE [X in X -> _]/= => <-.
rewrite -!fmap_oE. congr (fmap _ (insert a t)).
by apply boolp.funext => s; rewrite /= -rev_cons.
Qed.

End insert_altCIMonad.

Fixpoint iperm {M : altMonad} {A : UU0} (s : seq A) : M (seq A) :=
  if s isn't h :: t then Ret [::] else (iperm t >>= insert h)%monae.

Section iperm_altMonad.
Context {M : altMonad}.
Local Open Scope mprog.

(* lemma 3.3 in mu2019tr2 *)
Lemma iperm_o_map (A B : UU0) (f : A -> B) :
  iperm \o map f = map f (o) iperm :> (_ -> M _).
Proof.
apply boolp.funext; elim => [/=|x xs IH].
  by rewrite fcompE [iperm _]/= -[in RHS]compE (natural ret).
by rewrite fcompE [in iperm _]/= fmap_bind -insert_map -bind_fmap -fcompE -IH.
Qed.

Hypothesis Mmm : forall A, idempotent_op (@alt _ A : M A -> M A -> M A).

Variables (A : UU0) (p : pred A).

(* netys2017 *)
Lemma iperm_filter : iperm \o filter p = filter p (o) iperm :> (_ -> M _).
Proof.
apply boolp.funext; elim => [|h t /= IH].
  by rewrite fcompE fmapE bindretf.
case: ifPn => ph.
  rewrite [in LHS]/= IH [in LHS]fcomp_def compE [in LHS]bind_fmap.
  rewrite [in RHS]fcomp_def compE -/(fmap _ _) [in RHS]fmap_bind; bind_ext => s.
  by rewrite filter_insertT.
rewrite fcompE fmap_bind IH fcompE fmapE; bind_ext => s.
by rewrite filter_insertN.
Qed.

End iperm_altMonad.

Section splits.
Context {M : altMonad} {A : UU0}.
Implicit Types s : seq A.
Local Open Scope monae_scope.

Fixpoint splits s : M (seq A * seq A)%type :=
  if s is h :: t then
    splits t >>= (fun xy => Ret (h :: xy.1, xy.2) [~] Ret (xy.1, h :: xy.2))
  else
    Ret ([::], [::]).

Fixpoint splits_bseq s : M ((size s).-bseq A * (size s).-bseq A)%type :=
  if s is h :: t then
    splits_bseq t >>= (fun '(x, y) =>
      Ret ([bseq of h :: x], widen_bseq (leqnSn _) y) [~]
      Ret (widen_bseq (leqnSn _) x, [bseq of h :: y]))
  else
    Ret ([bseq of [::]], [bseq of [::]]).

Local Open Scope mprog.
Lemma splits_bseqE s : splits s =
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

Section qperm.
Context (M : altMonad) (A : UU0) d (T : orderType d).
Local Open Scope monae_scope.

Local Obligation Tactic := idtac.
Program Definition qperm' (s : seq A)
  (f : forall s' : seq A, size s' < size s -> M (seq A)) : M (seq A) :=
match s with
| [::] => Ret [::]
| x :: xs =>
  splits_bseq xs >>=
    (fun '(ys, zs) => liftM2 (fun a b => a ++ x :: b) ((*qperm ys*) f ys _ : M (seq A)) (f zs _) (*(qperm zs)*))
end.
Next Obligation.
move=> s f x xs <- ? ys zs ?.
exact: (leq_ltn_trans (size_bseq ys)).
Defined.
Next Obligation.
move=> s f x xs <- ? ys zs ?.
exact: (leq_ltn_trans (size_bseq zs)).
Defined.

(*Equations? qperm (s : seq A) : M (seq A) by wf (size s) lt :=
| [::] => Ret [::]
| x :: xs =>
  splits_bseq xs >>=
    (fun '(ys, zs) => liftM2 (fun a b => a ++ x :: b) (qperm ys : M (seq A)) (qperm zs)).
Proof.
apply/ltP.
exact: (leq_ltn_trans (size_bseq ys)).
apply/ltP.
exact: (leq_ltn_trans (size_bseq zs)).
(*
Error: Missing universe constraint declared for inductive type: Type <= Type
                                                                Type <= Type
*)
Defined.*)

Definition qperm : seq A -> M (seq A) :=
  Fix (@well_founded_size _) (fun _ => M _) qperm'.

Lemma qperm_nil : qperm [::] = Ret [::].
(*Proof. by []. Qed.*)
Proof.
rewrite /qperm Init.Wf.Fix_eq // => -[//|h t f g H].
rewrite /qperm'; bind_ext => -[s1 s2].
by rewrite !H.
Qed.

Lemma qperm_cons x xs : qperm (x :: xs) =
  splits xs >>= (fun '(ys, zs) =>
    liftM2 (fun a b => a ++ x :: b) (qperm ys) (qperm zs)).
Proof.
rewrite /qperm Init.Wf.Fix_eq //; last first.
  move=> -[//|] h t f g fg.
  rewrite /qperm'; bind_ext => -[s1 s2].
  by rewrite !fg.
rewrite {1}/qperm' /=.
rewrite splits_bseqE fmapE bindA; bind_ext => -[? ?].
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

Definition refin {M : altMonad} A (m1 m2 : M A) : Prop := m1 [~] m2 = m2.
Notation "m1 `<=` m2" := (refin m1 m2).

Lemma refin_bindr (M : altMonad) A B (m1 m2 : M A) (f : A -> M B) :
  (m1 `<=` m2) -> (m1 >>= f `<=` m2 >>= f)%monae.
Proof. by move=> m12; rewrite /refin -alt_bindDl m12. Qed.

Lemma refin_if (M : altMonad) A (m1 m2 m1' m2' : M A) (b : bool) :
  (b -> m1 `<=` m1') -> (~~ b -> m2 `<=` m2') ->
  (if b then m1 else m2) `<=` (if b then m1' else m2').
Proof. by case: b => [+ _|_]; exact. Qed.

Definition lrefin {M : altMonad} A B (f g : A -> M B) := forall x, f x `<=`g x.
Notation "f `<.=` g" := (lrefin f g).

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

Section lrefin_lemmas_altCIMonad.
Variable M : altCIMonad.

Lemma lrefin_refl A B (a : A -> M B) : a `<.=` a.
Proof. by move => ?; exact: refin_refl. Qed.

Lemma lrefin_trans A B (b a c : A -> M B) : a `<.=` b -> b `<.=` c -> a `<.=` c.
Proof. by move => ? ? ?; exact: refin_trans. Qed.

Lemma lrefin_antisym A B (a b : A -> M B) : a `<.=` b -> b `<.=` a -> a = b.
Proof. move => ? ?; apply boolp.funext => ?; exact: refin_antisym. Qed.
End lrefin_lemmas_altCIMonad.

Lemma refin_ret_insert (M : altCIMonad) (A : UU0) h (t : seq A) :
  Ret (h :: t) `<=` (insert h t : M _).
Proof.
elim: t h => [h|t1 t2 ih h]; first by rewrite insertE; exact: refin_refl.
by rewrite insertE; exact: refinR.
Qed.
