(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2020 monae authors, license: LGPL-2.1-or-later               *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require boolp.
Require Import monae_lib hierarchy monad_lib fail_lib state_lib.
From infotheo Require Import ssr_ext.
(* Require Import Classical. *)

(******************************************************************************)
(*                            Quicksort example                               *)
(*                                                                            *)
(* wip!                                                                       *)
(******************************************************************************)

(* TODO: shouldn't prePlusMonad be plusMonad (like list monad) and
    plusMonad be plusCIMonad (like set monad) *)

Reserved Notation "A `<=` B" (at level 70, no associativity).
Reserved Notation "A `>=` B" (at level 70, no associativity).
Reserved Notation "A `<.=` B" (at level 70, no associativity).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope order_scope.
Import Order.TTheory.
Local Open Scope monae_scope.
Local Open Scope tuple_ext_scope.

(* TODO: move *)
Lemma kleisliE (M : monad) (A B C : UU0) (g : B -> M C) (f : A -> M B) (a : A) :
  (f >=> g) a = (f a) >>= g.
Proof. by rewrite /kleisli /= join_fmap. Qed.

Definition refin (M : altMonad) A (m1 m2 : M A) : Prop := m1 [~] m2 = m2.

Notation "m1 `<=` m2" := (refin m1 m2) : monae_scope.
Notation "m1 `>=` m2" := (refin m2 m1) : monae_scope.

Section refin_lemmas.
  Variable M : altCIMonad.
  Lemma refin_refl A (a : M A) : a `<=` a.
  Proof. by rewrite /refin altmm. Qed.

  Lemma refin_trans A (b a c : M A) :
  a `<=` b -> b `<=` c -> a `<=` c.
  Proof. by rewrite /refin => h1 <-; rewrite altA h1. Qed.

  Lemma refin_antisym A (a b : M A) :
  a `<=` b -> b `<=` a -> a = b.
  Proof. by rewrite /refin => h1 <-; rewrite altC. Qed.
End refin_lemmas.

Definition lrefin {M : altMonad} A B (f g : A -> M B) : Prop :=
  forall x, f x `<=`g x.
Notation "f `<.=` g" := (lrefin f g) : monae_scope.

Section lrefin_lemmas.
  Variable M : altCIMonad.
  Lemma lrefin_refl A B (a : A -> M B) : a `<.=` a.
  Proof. move => ?; exact: refin_refl. Qed.

  Lemma lrefin_trans A B (b a c : A -> M B) :
  a `<.=` b -> b `<.=` c -> a `<.=` c.
  Proof. move => ? ? ?; exact: refin_trans. Qed.

  Lemma lrefin_antisym A B (a b : A -> M B) :
  a `<.=` b -> b `<.=` a -> a = b.
  Proof. move => ? ?; rewrite boolp.funeqE => ?; exact: refin_antisym. Qed.
End lrefin_lemmas.

Lemma bind_monotonic_refin (M : altMonad) A B (m1 m2 : M A) (f : A -> M B) :
  (m1 `<=` m2) -> (m1 >>= f `<=` m2 >>= f).
Proof. by move=> m12; rewrite /refin -alt_bindDl m12. Qed.

Lemma bind_monotonic_lrefin (M : prePlusMonad) A B (m : M A) (f1 f2 : A -> M B) :
  (f1 `<.=` f2) -> (m >>= f1 `<=` m >>= f2).
Proof. 
  move=> f12; rewrite /refin -alt_bindDr.
  by bind_ext => a; apply f12.
Qed.

Fixpoint splits {M : plusMonad} A (s : seq A) : M (seq A * seq A)%type :=
  if s isn't x :: xs then Ret ([::], [::]) else
    splits xs >>= (fun yz => Ret (x :: yz.1, yz.2) [~] Ret (yz.1, x :: yz.2)).

Program Fixpoint tsplits {M : plusMonad} A (s : seq A) : M ((size s).-bseq A * (size s).-bseq A)%type :=
  if s isn't x :: xs then Ret (bseq0 _  _, bseq0 _ _) (*TODO: try to use [bseq of [::]]*) else
    tsplits xs >>= (fun '(ys, zs) => Ret (@Bseq _ _ (x :: ys) _ , @Bseq _ _ zs _) [~]
                                     Ret (@Bseq _ _  ys _, @Bseq _ _ (x :: zs) _)).
Next Obligation. by rewrite (leq_ltn_trans (size_bseq b)). Qed.
Next Obligation. by rewrite (leq_trans (size_bseq b0)). Qed.
Next Obligation. by rewrite (leq_trans (size_bseq b)). Qed.
Next Obligation. by rewrite (leq_ltn_trans (size_bseq b0)). Qed.

(* Goal forall M, @splits M nat [::] = Ret ([::], [::]). by []. Abort. *)

(* Goal forall M, @splits M _ [:: O; 1]%nat = Ret ([::], [::]).
move=> M.
rewrite /= bindretf alt_bindDl !bindretf.
Abort. *)

Local Open Scope mprog.
Lemma splitsE {M : plusMonad} A (s : seq A) :
  splits s = fmap (fun xy => (bseqval xy.1, bseqval xy.2)) (tsplits s) :> M _.
Proof.
elim: s => /= [|h t ih]; first by rewrite fmapE bindretf.
rewrite {}ih /= !fmapE 2!bindA; bind_ext => -[a b] /=.
by rewrite bindretf alt_bindDl 2!bindretf.
Qed.

Lemma all_cons {d : unit} {T : porderType d} (h : T) (p : pred T) (t : seq T) :
  (p h) && all p t = all p (h :: t).
Proof.
  by [].
Qed.

Lemma all_cat {d : unit} {T : porderType d} (p : pred T) (s1 s2 : seq T) :
  all p s1 && all p s2 = all p (s1 ++ s2).
Proof.
  elim: s1 s2 => [//|a l ih] [|a0 l0].
  by rewrite cats0 andbT.
  by rewrite /= -ih -all_cons -andbA.
Qed.

Lemma all_cat_cons {d : unit} {T : porderType d} h (p : pred T) (s1 s2 : seq T) :
  p h && all p s1 && all p s2 = all p (s1 ++ h :: s2).
Proof.
  elim: s1 s2 => [/=|a l ih] [|a0 l0].
  by rewrite andbC andTb.
  by rewrite andbC andbA andbT andbC.
  rewrite -all_cat -!all_cons.
  by rewrite -andbA -andbC andbAC andbA.
  rewrite -all_cat -!all_cons.
  by rewrite andbA andbCA -andbA !andbA -andbA -andbA andbACA !andbA .
Qed.

Lemma guard_splits {d : unit} {T : porderType d} {M : plusMonad} (p : pred T) (t : seq T) (C : Type) (f : seq T * seq T -> M C) :
guard (all p t) >> (splits t >>= f)
=
splits t >>= (fun x => guard (all p x.1) >>
guard (all p x.2) >> f x).
Proof.
  elim: t p C f => [p C f|h t ih p C f].
  by rewrite /= 2!bindretf /= guardT bindmskip.
  rewrite /= guard_and !bindA ih -bindA.
  rewrite guardsC; last exact: (@bindmfail M).
  rewrite bindA.
  (* bind_ext => -[a b].
  rewrite assertE bindA bindretf bindA /=.
  rewrite [in RHS]alt_bindDl /=.
  do 2 rewrite bindretf /= guard_and !bindA.
  rewrite -!bindA.
  rewrite [in RHS](@guardsC M (@bindmfail M) (all p a)).
  rewrite !bindA -alt_bindDr.
  bind_ext; case.
  rewrite assertE bindmskip -[in RHS]alt_bindDr.
  bind_ext; case.
  by rewrite alt_bindDl /= 2!bindretf -alt_bindDr. *)
Admitted.

Lemma guard_splits' {d : unit} {T : porderType d} {M : plusMonad} (p : pred T) (t : seq T) (C : Type) (f : seq T * seq T -> M C) :
  splits t >>= (fun x => guard (all p t) >> f x) =
  splits t >>= (fun x => (guard (all p x.1) >> guard (all p x.2)) >> f x).
Proof.
  rewrite -guard_splits guardsC; last exact : (@bindmfail M).
  rewrite bindA.
  bind_ext => -[a b].
  by rewrite guardsC; last exact : (@bindmfail M).
Abort.

Lemma guard_splits_cons {d : unit} {T : porderType d} {M : plusMonad} h (p : pred T) (t : seq T) (C : Type) (f : seq T * seq T -> M C) :
  guard (all p (h :: t)) >> (splits t >>= f)
  =
  splits t >>= (fun x => guard (all p x.1) >>
                         guard (all p x.2) >>
                         guard (p h) >> f x).
Proof.
  elim: t p C f h => [p C f h|h0 t ih p C f h].
  by rewrite /= 2!bindretf /= guardT andbT !bindskipf.
  rewrite /= guard_and !bindA all_cons ih -bindA.
  rewrite guardsC; last exact: (@bindmfail M).
  rewrite bindA.
  (* bind_ext => -[a b] /=.
  rewrite assertE bindA bindretf bindA /=.
  rewrite [in RHS]alt_bindDl /=.
  rewrite !bindretf /= -![in RHS]guard_and. 
  rewrite andbC -andbA andbCA andbC !andbA 3!guard_and.
  rewrite andbC andbAC !andbA 3!guard_and.
  rewrite !bindA -alt_bindDr.
  bind_ext; case.
  rewrite -alt_bindDr.
  bind_ext; case.
  rewrite -alt_bindDr.
  bind_ext; case.
  rewrite -alt_bindDr.
  bind_ext; case.
  by rewrite alt_bindDl 2!bindretf. *)
Admitted.

(* Lemma splits_guard_cons' {d : unit} {T : porderType d} {M : plusMonad} h (p : pred T) (t : seq T) (C : Type) (f : seq T * seq T -> M C) :
  splits t >>= (fun x => guard (all p (x.1 ++ t ::)) >> f x) =
  splits t >>= (fun x => guard (all p x.1) >> guard (all p x.2) >> guard (p h) >> f x).
Proof.
Admitted. *)
  (* elim: t p C f => [p C f|a l ih p C f]. 
  by rewrite /splits 2!bindretf /= guardT 2!bindskipf andbT.
  bind_ext; case.*)
  (* rewrite /= andbT.
  rewrite -all_cons guard_and.
  rewrite splits_guardC.
  rewrite splits_guard_sub.
  rewrite guardsC; last exact (@bindmfail M).
  rewrite 
  rewrite splits_guardAC.
  rewrite (@guardsC M _ (p h) _ (guard (all p _))); last exact (@bindmfail M).
  rewrite -bindA.
  rewrite (@splits_guardA _ _ M (p h)).
  rewrite splits_guard_sub.
  case: (p h); rewrite (guardT, guardF). *)
(* Admitted. *)

Local Close Scope mprog.

Section qperm.
Variables (M : plusMonad) (A : Type).

Local Obligation Tactic := idtac.
Program Definition qperm' (s : seq A)
    (f : forall s', size s' < size s -> M (seq A)) : M (seq A) :=
  if s isn't x :: xs then Ret [::] else
    tsplits xs >>= (fun a => let: (ys, zs) := a in liftM2 (fun a b => a ++ [:: x] ++ b) (f ys _) (f zs _)).
Next Obligation.
move=> [|h t] // ht x xs [xh xst] [a b ys zs] [-> zsb].
by apply: (leq_ltn_trans (size_bseq a)); rewrite xst.
Qed.
Next Obligation.
move=> [|h t] // ht x xs [xh xst] [a b ys zs] [ysa ->].
by apply: (leq_ltn_trans (size_bseq b)); rewrite xst.
Qed.
Next Obligation. by move=> /= s _ x xs. Qed.

Definition qperm : seq A -> M (seq A) :=
  Fix (@well_founded_size _) (fun _ => M _) qperm'.

Lemma qperm'_Fix (s : seq A) (f g : forall y, (size y < size s)%N -> M (seq A)) :
  (forall y (p : (size y < size s)%N), f y p = g y p) -> qperm' f = qperm' g.
Proof.
move=> H; rewrite /qperm'; case: s f g H => // h t f g H.
bind_ext => -[a b] /=; rewrite /liftM2 H (_ : f = g) //.
apply fun_ext_dep => s.
by rewrite boolp.funeqE=> p; exact: H.
Qed.

Lemma qperm_nil : qperm [::] = Ret [::].
Proof. by rewrite /qperm (Fix_eq _ _ _ qperm'_Fix). Qed.

Lemma qperm_cons x xs :
  qperm (x :: xs) = splits xs >>= (fun a => let: (ys, zs) := a in
                    liftM2 (fun a b => a ++ [:: x] ++ b) (qperm ys) (qperm zs)).
Proof.
rewrite {1}/qperm {1}(Fix_eq _ _ _ qperm'_Fix) /=.
rewrite splitsE /= fmapE bindA; bind_ext => -[s1 s2] /=.
by rewrite bindretf.
Qed.

Lemma qperm_consE x xs :
  qperm (x :: xs) = splits xs >>= (fun z =>
    liftM2 (fun a b => a ++ [:: x] ++ b) (qperm z.1) (qperm z.2)).
Proof. by rewrite qperm_cons; bind_ext => -[]. Qed.

Definition qpermE := (qperm_nil, qperm_cons).

End qperm.
Arguments qperm {M} {A}.

Lemma guard_neg (M : plusMonad) A (p q : bool) (m1 m2 : M A) :
  (if p then m1 else m2) `<=` (guard p >> m1) [~] (guard (~~ p) >> m2).
Proof.
rewrite /refin; case: ifPn => /= [pT|pF]; rewrite !(guardT,guardF).
by rewrite bindskipf bindfailf altA altmm.
by rewrite bindfailf bindskipf altCA altmm.
Qed.

Section slowsort.
Variable M : plusMonad.
Variables (d : unit) (T : porderType d).

Let leT := (fun x y : T => x <= y)%O.
Let sorted := sorted leT.

Lemma sorted_cat' (a b : seq T) : sorted (a ++ b) -> sorted a && sorted b.
Proof.
elim: a b => //= h t ih b; rewrite cat_path => /andP[-> /=].
exact: path_sorted.
Qed.

(* equation 5 *)
Lemma sorted_cat_cons (s s' : seq T) (p : T) :
  sorted (s ++ p :: s') = [&& sorted s, sorted s', all (<= p) s & all (>= p) s'].
Proof.
apply/idP/idP => [|].
  rewrite -cat1s => H; apply/and4P; split.
  by move: H => /sorted_cat'/andP[].
  by move: H; rewrite catA => /sorted_cat'/andP[].
  move: H; rewrite catA => /sorted_cat'/andP[].
  by rewrite {1}/sorted -rev_sorted rev_cat /= (path_sortedE ge_trans) all_rev => /andP[].
  move/sorted_cat' : H => /andP[_].
  by rewrite {1}/sorted /= (path_sortedE le_trans) // => /andP[].
case/and4P=> ss ss' ps ps'; apply sorted_cat => //=.
  by rewrite (path_sortedE le_trans) ps'.
move=> t ts t' t'ps'; apply: (@le_trans _ _ p); first by move/allP : ps; apply.
by move: t'ps'; rewrite inE => /orP[/eqP ->//|]; move/allP : ps'; apply.
Qed.

Definition slowsort : seq T -> M (seq T) :=
  (qperm >=> assert sorted)%monae.

Lemma slowsort_nil : slowsort [::] = Ret [::].
Proof.
by rewrite /slowsort kleisliE qpermE bindretf /assert /= guardT bindskipf; unlock.
Qed.

(*Definition invariant_by_qperm (p : pred (seq T)) :=
  forall s, p s -> qperm s >>= (fun x => guard (p x)) = Ret true.*)

Lemma sub (x p : T) (xs : seq T) : (x <= p) && all (<= p) xs -> all (<= p) (x :: xs).
Proof.
  (* by []. *)
  elim: xs => [ // | a l h1 h2 ]. simpl in *.
  by rewrite h2; simpl.
Qed.

Lemma sub_inv (x p : T) (xs : seq T) : (x <= p) && all (<= p) xs <-> all (<= p) (x :: xs).
Proof.
  by [].
Qed.

Lemma guard_sub_inv (x p : T) (xs : seq T) (B : Type) (f : seq T -> M B) : 
  guard ((x <= p) && all (<= p) xs) >> (do x <- qperm (x :: xs); f x)%Do 
  = guard (all (<= p) (x :: xs)) >> (do x <- qperm (x :: xs); f x)%Do.
Proof.
  by [].
Qed.
  
Lemma in_all_r (r : rel T) {r_trans : transitive r} (x p : T) (t : seq T) :
  mem t x -> all (r p) t -> r p x.
Proof.
  elim: t => /= //.
  move=> a l ih /=.
  rewrite in_cons => /orP[/eqP|] h /andP[] h1 h2.
  by subst.
  move: h h2 => //.
Qed.

Definition nondet_plusMonad (M : plusMonad) A (n : M A) :=
  {m | ndDenote m = n}.

Lemma commute_plusMonad
  A (m : M A) B (n : M B) C (f : A -> B -> M C) :
  nondet_plusMonad m -> commute m n f.
Proof.
case => x.
elim: x m n f => [{}A a m n f <-| B0 {}A n0 H0 n1 H1 m n2 f <- |
  A0 m n f <- | A0 n0 H0 n1 H1 m n2 f <-].
- rewrite /commute bindretf /=.
  by under [RHS]eq_bind do rewrite bindretf.
- rewrite /commute /= !bindA.
  transitivity (do x <- ndDenote n0; do y <- n2; ndDenote (n1 x) >>= f^~ y)%Do.
    bind_ext => s.
    by rewrite (H1 s).
  rewrite H0 //.
  bind_ext => b.
  by rewrite bindA.
- rewrite /commute /= bindfailf.
  transitivity (n >> fail : M C).
    by rewrite (@bindmfail M).
  bind_ext => b.
  by rewrite (@bindfailf M).
- rewrite /commute /= alt_bindDl.
  transitivity (do y <- n2; ndDenote n0 >>= f^~ y [~]
                           ndDenote n1 >>= f^~ y)%Do; last first.
    bind_ext => a.
    by rewrite alt_bindDl.
  by rewrite alt_bindDr H0 // H1.
Qed.

Lemma commute_guard_n
  (b : bool) B (n : M B) C (f : unit -> B -> M C) :
  commute (guard b) n f.
Proof.
  rewrite /commute.
  rewrite commute_plusMonad => [//|]; exists (if b then ndRet tt else @ndFail _).
  by case: ifP; rewrite (guardT, guardF).
Qed.

Lemma guard_qperm_eq (B : Type) (p : pred T) (a : seq T) (f : seq T -> M B) :
  guard (all p a) >>= (fun _ => qperm a >>= f) =
  qperm a >>= (fun x => guard (all p x) >> f x).
Proof.
  move: p.
  have [n leMn] := ubnP (size a); elim: n => // n ih in a f leMn *.
  move: a leMn.
  case. 
  move=> _ p.
  by rewrite /= qperm_nil 2!bindretf /=.
  move => h t.
  rewrite ltnS => tn p.
  rewrite qperm_consE {1}/liftM2 !bindA /= guard_and [in LHS]bindA.
  rewrite -bindA -guard_and (all_cons h).
  rewrite guard_splits_cons /liftM2.
  rewrite splitsE /= fmapE !bindA.
  bind_ext => -[a b] /=.
  rewrite 2!bindretf /=.
  (* transitivity (
    ((guard (all p b) >> guard (p h)) >> guard (all p a) >>
    (do x <- do x1 <- qperm a; do x2 <- qperm b; Ret (x1 ++ h :: x2); f x)%Do)
    ). *)
  rewrite -2!guard_and andbC andbA andbC andbA 2!guard_and !bindA.
  rewrite ih; last by rewrite (leq_trans _ tn) //= ltnS size_bseq.
  (* transitivity (
    (do x0 <- qperm a; ((guard (p h) >> guard (all p x0)) >> guard (all p b))
    >> (do x1 <- do x2 <- qperm b; Ret (x0 ++ h :: x2); f x1)%Do)%Do
  ). *)
  rewrite -bindA -guard_and commute_guard_n.
  bind_ext => x0.
  rewrite -bindA -guard_and andbC andbA andbC andbA 2!guard_and !bindA.
  rewrite ih; last by rewrite (leq_trans _ tn) //= ltnS size_bseq.
  (* transitivity (
    (do x2 <- qperm b; ((guard (p h) >> guard (all p x0)) >> guard (all p x2)) >>
    (do x3 <- Ret (x0 ++ h :: x2); f x3)%Do)%Do
  ). *)
  rewrite -bindA -guard_and commute_guard_n.
  bind_ext => x1.
  by rewrite -bindA -!guard_and 2!bindretf all_cat_cons.
Qed.

Lemma guard_qperm_eq2 (B : Type) (p : T) (a : seq T) (f : seq T -> M B) :
 guard (all (>= p) a) >> (qperm a >>= f) = qperm a >>= (fun x => (guard (all (>= p) x) >> f x)).
Proof. by rewrite guard_qperm_eq. Qed.

Lemma guard_qperm_neq (B : Type) (b a : seq T) (r : pred T) (f : seq T -> M B) :
  guard (all r b) >> (qperm a >>= f) =
  qperm a >>= (fun x => (guard (all r b) >> f x)).
Proof.
rewrite guardsC; last exact: (@bindmfail M).
rewrite bindA.
bind_ext => x.
by rewrite guardsC; last exact: (@bindmfail M).
Qed.

Lemma refin_slowsort_inductive_case (p : T) (xs : seq T) :
  slowsort (p :: xs) =
  splits xs >>= (fun '(ys, zs) => guard (all (<= p) ys && all (>= p) zs) >>
    (qperm ys >>= assert sorted) >>= (fun ys' =>
    (qperm zs >>= assert sorted) >>= (fun zs' =>
    Ret (ys' ++ [:: p] ++ zs')))).
Proof.
transitivity (
  splits xs >>= (fun '(ys, zs) =>
  qperm ys >>= (fun ys' => qperm zs >>= (fun zs' =>
  assert sorted (ys' ++ [:: p] ++ zs')))) : M _
).
  rewrite /slowsort /= kleisliE qperm_cons /= !bindA.
  bind_ext => -[a b] /=.
  rewrite /liftM2 bindA; bind_ext => s.
  by rewrite bindA; bind_ext => s'; rewrite bindretf.
transitivity (
  splits xs >>= (fun '(ys, zs) =>
  qperm ys >>= (fun ys' => qperm zs >>= (fun zs' =>
  guard ([&& sorted ys', sorted zs', all (<= p) ys' & all (>= p) zs']) >>
  Ret (ys' ++ [:: p] ++ zs')))) : M _
).
  bind_ext => -[a b]; bind_ext => s; bind_ext => s'; rewrite assertE /=.
  by rewrite -sorted_cat_cons.
bind_ext=> {xs} -[a b].
rewrite guard_and 2!bindA (bindA (qperm a)).
rewrite guard_qperm_neq.
rewrite guard_qperm_eq.
bind_ext => s.
do 3 under eq_bind do rewrite guard_and.
transitivity (qperm b >>=
  (fun x =>
   guard (all (>= p) x) >> (guard (all (<= p) s) >> (guard (sorted x) >> ((guard (sorted s)) >> Ret (s ++ [:: p] ++ x)))) : M _)).
  bind_ext => s'.
  rewrite -!bindA -!guard_and.
  rewrite andbC.
  rewrite (andbC _ (all (<= p) s)).
  rewrite (andbC (sorted s)).
  by rewrite !andbA.
rewrite -guard_qperm_eq2.
rewrite -[in RHS]bindA.
rewrite -[in RHS]guard_and [in RHS]andbC [in RHS]guard_and.
rewrite [in RHS]bindA.
congr (_ >> _).
rewrite boolp.funeqE => s'.
rewrite -guard_qperm_neq.
congr (_ >> _).
rewrite boolp.funeqE => s2.
under [RHS]eq_bind do rewrite bindA.
rewrite assertE bindA bindretf.
rewrite guardsC; last exact: (@bindmfail M).
rewrite bindA.
bind_ext => s3.
by rewrite assertE !bindA 2!bindretf assertE.
Qed.

Fixpoint partition p (s : seq T) : seq T * seq T :=
  if s isn't x :: xs then ([::], [::]) else
  let: yz := partition p xs in
  if x <= p then (x :: yz.1, yz.2) else (yz.1, x :: yz.2).

Lemma size_partition p (s : seq T) :
  size (partition p s).1 + size (partition p s).2 = size s.
Proof.
elim: s p => //= x xs ih p; have {ih} := ih p.
move H : (partition p xs) => h; case: h H => a b ab /= abxs.
by case: ifPn => xp /=; rewrite ?(addSn,addnS) abxs.
Qed.

Lemma partition_ p x (xs ys zs: seq T) :
(* (partition p xs).1 = ys -> (partition p xs).2 = zs -> *)
  (ys, zs) = partition p xs ->
  (Ret (partition p (x :: xs)) : M (seq T * seq T)%type)
  `<=` Ret (x :: ys, zs) [~] Ret (ys, x :: zs).
Proof. move=> hyz. rewrite /=. case: (x <= p); rewrite -hyz /refin.
by rewrite altA altmm.
by rewrite altCA altmm.
Qed.

Lemma refin_partition (p : T) (xs : seq T) :
  (Ret (partition p xs) : M (seq T * seq T)%type (*TODO: :> notation for `<=`?*))
  `<=`
  splits xs >>= assert (fun '(ys, zs) => (all (<= p) ys && all (>= p) zs)).
Proof.
  move: p.
  rewrite /refin.
  have [n leMn] := ubnP (size xs); elim: n => // n ih in xs leMn *.
  move: xs leMn.
  case. 
  move=> _ p.
  by rewrite bindretf assertE /= guardT bindskipf /refin altmm.
  move => h t.
  rewrite ltnS => tn p.
  move ppt : (partition p t) => pt.
  (* /rewrite /= -guardsC. *)
  case: pt => ys zs in ppt *.
  rewrite /= ppt.
  case: (h <= p).
  rewrite /refin.
  (* have := (partition p t).1 => ys. *)
  (* have := (partition p t).2 => zs. *)
  (* rewrite ih. *)
  (* rewrite /=.
  rewrite /= bindA. guard_and [in LHS]bindA.
  rewrite -bindA -guard_and (all_cons h).
  rewrite guard_splits_cons /liftM2.
  rewrite splitsE /= fmapE !bindA. *)
Abort.

(* Lemma __ (x y : T) (b : bool) : (b -> leT x y) -> y < x -> ~~ b.
Proof. rewrite contra_ltN. rewrite le_eqVlt. lt_trans.
elim : T.
rewrite not_lt.
rewrite /negb.
case: ifPn => [xy|]. *)

Lemma __ (x y : T) : (x < y) -> (x <= y).
Proof. rewrite le_eqVlt orbC => ->.
rewrite orTb //. Abort.

Definition is_partition p (yz : seq T * seq T) := all (<= p) yz.1 && all (>= p) yz.2.

Lemma is_partition_consL p x (ys zs : seq T) :
  is_partition p (x :: ys, zs) = (x <= p) && is_partition p (ys, zs).
Proof. by rewrite /is_partition -all_cons /= andbA. Qed.

Lemma is_partition_consR p x (ys zs : seq T) :
  is_partition p (ys, x :: zs) = (x >= p) && is_partition p (ys, zs).
Proof. by rewrite /is_partition -all_cons /= andbCA. Qed.

Definition is_partition_consE := (is_partition_consL, is_partition_consR).
  
Lemma bind_cong A B (m n : M A) (f g : A -> M B) :
  m = n -> (forall x, f x = g x) -> m >>= f = n >>= g.
Proof.
  move=> mn fg.
  rewrite mn.
  bind_ext.
  move: fg.
  rewrite -boolp.funeqE.
  apply fun_ext_dep.
Qed.

Lemma ata p x (xs : seq T): 
(do x0 <- splits xs;
 do x <- let '(ys, zs) := x0 in (Ret (x :: ys, zs) [~] Ret (ys, x :: zs) : M _);
 assert (is_partition p) x)%Do =
 splits xs >>= (fun '(ys, zs) => ((Ret (x :: ys, zs) : M _) [~] 
                                    (Ret (ys, x :: zs) : M _)) >>= assert (is_partition p)).
Proof.
  bind_ext => -[a b] //.
Qed.                                  

Lemma negle_ge (p x : T) : ~~ (x <= p) -> (p <= x).
Proof.
  admit.
Admitted.
  
  (* rewrite le_eqVlt negb_or => /andP[xnp nxp].
move: nxp.
rewrite /negb.
case: ifPn => [xp fls|nxp tru].
inversion fls.

rewrite neq_lt in xnp.
rewrite nxp in xnp.
rewrite le_eqVlt.
apply /orP.  rewrite nxp.
case: ifPn. *)

Lemma partition_spec_1 p x (xs : seq T) :
splits xs >>= (fun yz => ((Ret (x :: yz.1, yz.2) : M _) [~] 
                          (Ret (yz.1, x :: yz.2) : M _)) >>= assert (is_partition p)) =
splits xs >>= (fun yz => (
guard (x <= p) >> guard (is_partition p yz) >> (Ret (x :: yz.1 , yz.2) : M _) [~]
guard (p <= x) >> guard (is_partition p yz) >> (Ret (yz.1 , x :: yz.2) : M _) : M _)).
Proof.
  bind_ext => -[a b].
  rewrite alt_bindDl !bindretf !assertE.
  rewrite !is_partition_consE 2!guard_and !bindA //.
Qed.

Lemma partition_spec_2 p x (xs : seq T) :
splits xs >>= (fun yz => (
guard (x <= p) >> guard (is_partition p yz) >> (Ret (x :: yz.1 , yz.2) : M _) [~]
guard (p <= x) >> guard (is_partition p yz) >> (Ret (yz.1 , x :: yz.2) : M _))) = (* `>=` *)
splits xs >>= (fun yz => (
guard (x <= p) >> guard (is_partition p yz) >> (Ret (x :: yz.1 , yz.2) : M _) [~]
guard (~~ (x <= p)) >> guard (is_partition p yz) >> (Ret (yz.1 , x :: yz.2) : M _))).
Proof.
Admitted.
  (* rewrite /refin -alt_bindDr.
  bind_ext => -[a b].
  case: guardPn => xp.
  by rewrite /= guardF bindskipf bindfailf altmfail altA (altmm (_ : M _)).
  rewrite /= guardT bindskipf bindfailf !altfailm.
  rewrite negle_ge. (* Admitted *)
  by rewrite guardT bindskipf (altmm (_ : M _)).
  by []. *)
(* Qed. *)

Lemma eq7 A (p : bool) (m1 m2 : M A) :
  (if p then m1 else m2) `<=` (guard p >> m1) [~] (guard (~~ p) >> m2).
Proof.
  rewrite /refin; case: ifPn => /= [pT|pF]; rewrite !(guardT,guardF).
  by rewrite bindskipf bindfailf altA altmm.
  by rewrite bindfailf bindskipf altCA altmm.
Qed.

Lemma partition_spec_3 p x (xs : seq T) :
splits xs >>= (fun yz =>
(guard (x <= p) >> guard (is_partition p yz) >> (Ret (x :: yz.1 , yz.2) : M _)) [~]
(guard (~~ (x <= p)) >> guard (is_partition p yz) >> (Ret (yz.1 , x :: yz.2) : M _))) =
splits xs >>= (fun yz =>
guard (is_partition p yz) >> (guard (x <= p) >> (Ret (x :: yz.1, yz.2) : M _) [~] guard (~~ (x <= p)) >> (Ret (yz.1, x :: yz.2) : M _))).
Proof.
  bind_ext => -[a b].
  rewrite -guard_and andbC guard_and altC.
  rewrite -guard_and andbC guard_and altC.
  by rewrite !bindA -alt_bindDr.
Qed.

Lemma partition_spec_4 p x (xs : seq T) :
splits xs >>= (fun yz =>
guard (is_partition p yz) >> (guard (x <= p) >> (Ret (x :: yz.1, yz.2) : M _) [~] guard (~~ (x <= p)) >> (Ret (yz.1, x :: yz.2) : M _))) `>=`
splits xs >>= (fun yz =>
guard (is_partition p yz) >>
if x <= p then Ret (x :: yz.1 , yz.2)
          else Ret (yz.1 , x :: yz.2)).
Proof.
  rewrite /refin -alt_bindDr.
  bind_ext => -[a b].
  rewrite -alt_bindDr.
  by rewrite eq7.
Abort.

Lemma partition_spec_4 p x (xs : seq T) :
splits xs >>= (fun yz =>
guard (is_partition p yz) >> (guard (x <= p) >> (Ret (x :: yz.1, yz.2) : M _) [~] guard (~~ (x <= p)) >> (Ret (yz.1, x :: yz.2) : M _))) `>=`
splits xs >>= (fun yz =>
guard (is_partition p yz) >>
Ret (if x <= p then (x :: yz.1 , yz.2)
          else (yz.1 , x :: yz.2))).
Proof.
  rewrite /refin -alt_bindDr.
  bind_ext => -[a b].
  rewrite -alt_bindDr.
  case: ifPn => xp.
  by rewrite guardT guardF bindskipf bindfailf altmfail /= (altmm (_ : M _)).
  by rewrite /= guardT guardF bindskipf bindfailf altfailm (altmm (_ : M _)).
Qed.

Lemma partition_spec_5 p x (xs : seq T) :
splits xs >>= (fun yz =>
guard (is_partition p yz) >>
Ret (if x <= p then (x :: yz.1 , yz.2)
          else (yz.1 , x :: yz.2))) =
splits xs >>= assert (is_partition p) >>= (fun yz =>
Ret (if x <= p then (x :: yz.1 , yz.2)
          else (yz.1 , x :: yz.2)) : M _).
Proof.
  rewrite bindA.
  bind_ext => -[a b].
  rewrite assertE bindA.
  bind_ext; case.
  by rewrite bindretf /=.
Qed.

Lemma partition_spec_6 p x (xs : seq T) :
splits xs >>= assert (is_partition p) >>= (fun yz =>
Ret (if x <= p then (x :: yz.1 , yz.2)
          else (yz.1 , x :: yz.2)) : M _) =
Ret (partition p xs) >>= (fun yz =>
if x <= p then Ret (x :: yz.1 , yz.2)
          else Ret (yz.1 , x :: yz.2)).
Proof.
  elim: xs => [/=|h xs ih].
  rewrite bindA !bindretf assertE guardT bindskipf bindretf /=.
  by case: (x <= p).
  rewrite bindretf.
  Admitted.
  (* rewrite bind_monotonic_refin. *)

Lemma partition_spec' p x (xs : seq T):
splits xs >>= (fun '(ys, zs) => ((Ret (x :: ys, zs) : M _) [~] 
                                    (Ret (ys, x :: zs) : M _)) >>= assert (is_partition p)) =
splits xs >>= (fun '(ys, zs) => ((Ret (x :: ys, zs) : M _) >>= assert (is_partition p)) [~] 
                                    ((Ret (ys, x :: zs) : M _) >>= assert (is_partition p))).
Proof.
  bind_ext => -[a b].
  by rewrite alt_bindDl !bindretf.
Qed.

Lemma partition_spec'' p x (xs : seq T) :
splits xs >>= (fun '(ys, zs) => ((Ret (x :: ys, zs) : M _) >>= assert (is_partition p)) [~] 
                                    ((Ret (ys, x :: zs) : M _) >>= assert (is_partition p))) =
  splits xs >>= (fun '(ys, zs) => (assert (is_partition p) (x :: ys, zs) : M _) [~] 
  (assert (is_partition p) (ys, x :: zs) : M _)).
Proof.
  bind_ext => -[a b].
  by rewrite !bindretf.
Qed.

Lemma partition_spec''' p x (xs : seq T) :
splits xs >>= (fun '(ys, zs) => 
  (assert (is_partition p) (x :: ys, zs) : M _) [~] 
  (assert (is_partition p) (ys, x :: zs) : M _)) =
  splits xs >>= (fun '(ys, zs) => 
  (guard (is_partition p (x :: ys, zs)) >> Ret (x :: ys, zs) : M _) [~] 
  (guard (is_partition p (ys, x :: zs)) >> Ret (ys, x :: zs) : M _)).
Proof.
  (* eapply bind_cong. *)
  bind_ext => -[a b].
  by rewrite !assertE.
Qed.

Lemma partition_spec p : 
  (Ret \o partition p) `<.=` (@splits M T) >=> assert (is_partition p).
Proof.
  rewrite /lrefin => xs.
  elim: xs.
  rewrite kleisliE bindretf assertE guardT bindskipf /=; exact: refin_refl.
  move => x xs ih.
  rewrite kleisliE /= bindA.
  rewrite partition_spec_1.
  rewrite partition_spec_2.
  rewrite partition_spec_3.
  apply: (@refin_trans _ _
    (splits xs >>= (fun yz =>
    guard (is_partition p yz) >>
    Ret (if x <= p then (x :: yz.1 , yz.2)
              else (yz.1 , x :: yz.2))))
  ).
  rewrite partition_spec_5 bindA.
  (* apply bind_monotonic_refin.
  admit.
  apply partition_spec_4.
  rewrite /refin altC.
  rewrite ih. *)
Admitted.

Lemma splits_partition p (xs : seq T) :
  (do x0 <- splits xs;
  assert (fun '(ys, zs) => all (<= p) ys && all (> p) zs) x0)%Do
  = (Ret (partition p xs) : M _).
Proof.
  move: p.
  have [n leMn] := ubnP (size xs); elim: n => // n ih in xs leMn *.
  move: xs leMn.
  case. 
  move=> _ p.
  by rewrite bindretf assertE /= guardT bindskipf.
  move => h t.
  rewrite ltnS => tn p.
  rewrite /= bindA.
  move ppxs : (partition p t) => s; case: s ppxs => ys zs ppxs.
  transitivity (
    (do x <- splits t;
    do x0 <- Ret (h :: x.1, x.2) [~] Ret (x.1, h :: x.2) : M _;
    assert (fun '(ys, zs) => all (<= p) ys && all (> p) zs) x0)%Do
  ).
  bind_ext; case => //.
  transitivity (
    (do x <- splits t;
    do x0 <- Ret (h :: x.1, x.2) [~] Ret (x.1, h :: x.2) : M _;
    assert (fun x => all (<= p) x.1 && all (> p) x.2) x0)%Do
  ).
  bind_ext=> -[a b].
  rewrite !alt_bindDl !bindretf //.
  transitivity (
    (do x <- splits t;
    do x0 <- Ret (h :: x.1, x.2) [~] Ret (x.1, h :: x.2) : M _;
    guard ((fun x => all (<= p) x.1 && all (> p) x.2) x0) >> Ret x0)%Do
  ).
  bind_ext => -[a b] /=.
  rewrite !alt_bindDl !bindretf !assertE //.
  rewrite splitsE /= fmapE bindA.
  (* rewrite commute_plusMonad. *)
  case: ifP => h_le_p.
  (* rewrite (_ : (fun '(_, _) => _) = (fun i => Ret (h :: i.1, i.2) [~] Ret (i.1, h :: i.2))); last first.
  rewrite commute_plusMonad.



  elim: xs p => [p /=|x xs ih p].
  by rewrite bindretf assertE guardT bindskipf.
  rewrite /=.
  move ppxs : (partition p xs) => s; case: s ppxs => ys zs ppxs.
  rewrite bindA.
  rewrite -join_fmap joinE. *)
  (* rewrite ih. *)
  (* rewrite -guard_splits_cons.
  rewrite ret_kleisli.
  rewrite -!kleisliE.
  rewrite ret_kleisli.
  rewrite /assert /guard; unlock.
  rewrite -(@guardsC M _ _ _ (splits (x :: xs))). *)
Admitted.

Lemma __ (p x : T) (xs : seq T) : 
  (Ret (partition p (x :: xs)) : M _) = 
  (do x <- Ret (partition p (x :: xs)); assert (fun '(ys, zs) => all (<= p) ys && all (>= p) zs) x)%Do.
Proof.
Admitted.

Lemma neg_all p (xs : seq T) :
  all (> p) xs -> all (>= p) xs.
Proof. elim: xs => [//|h t ih].
rewrite -!all_cons => /andP[ph allpt].
rewrite ih => [|//].
by rewrite andbT le_eqVlt ph orbT.
Qed.

Lemma altmmm (ys zs : seq T) :
  Ret (ys, zs) [~] Ret (ys, zs) = Ret (ys, zs) :> M _.
Proof. rewrite altmm. by []. Qed.

Lemma refin_partition'' (p : T) (xs : seq T) :
  (Ret (partition p xs) : M _ (*TODO: :> notation for `<=`?*))
  `<=`
  splits xs >>= assert (fun '(ys, zs) => (all (<= p) ys && all (> p) zs)).
  (* splits xs >>= assert (fun '(ys, zs) => (all (<= p) ys && all (> p) zs))
  `>=`
  Ret (partition p xs) :> M. *)
Proof.

  apply: (@refin_trans _ _ (splits xs >>= assert (fun '(ys, zs) => (all (<= p) ys && all (> p) zs)))).
  (* rewrite -splits_partition.  (*Admitted*)
  rewrite /refin -alt_bindDr.
  bind_ext => -[a b].
  rewrite /assert /guard; unlock.
  case: ifPn; rewrite (bindskipf, bindfailf) => _.
  by rewrite -[in RHS](altmm (Ret (a, b))). 
  by rewrite altfailm. *)
  admit.
  rewrite /refin -alt_bindDr.
  bind_ext => -[a b].
  by rewrite (altmm (_ : M _)).
Admitted.

Lemma refin_partition (p : T) (xs : seq T) :
  (Ret (partition p xs) : M (seq T * seq T)%type (*TODO: :> notation for `<=`?*))
  `<=`
  splits xs >>= assert (fun '(ys, zs) => (all (<= p) ys && all (>= p) zs)).
Proof.
elim: xs p => [p /=|x xs ih p].
  by rewrite bindretf /refin /= !assertE !all_nil /= guardT bindskipf altmm.
  rewrite /=.
move pxs : (partition p xs) => s; case: s pxs => ys zs pxs.
case: ifPn => xp.
(* rewrite (_ : (fun '(_, _) => _) = (fun i => Ret (x :: i.1, i.2) [~] Ret (i.1, x :: i.2))); last first. *)
  (* by rewrite boolp.funeqE => -[a b]. (* TODO: awkward  *)
  rewrite /refin.
  rewrite alt_bindDr.
  rewrite alt_bindDl. *)
Admitted.

Lemma refin_slowsort (p : T) (xs : seq T) :
  slowsort (p :: xs) `>=`
  Ret (partition p xs) >>= (fun '(ys, zs) =>
    slowsort ys >>= (fun ys' => slowsort zs >>= (fun zs' => Ret (ys' ++ [:: p] ++ zs')))).
Proof.
rewrite [X in X `>=` _]refin_slowsort_inductive_case.
rewrite [X in X `>=` _](_ : _ = splits xs >>=
  (fun a => guard (let '(ys, zs) := a in all (<= p) ys && all (>= p) zs) >> Ret a) >>=
  fun '(ys, zs) => (qperm ys >>= assert sorted) >>=
   (fun ys' => (qperm zs >>= assert sorted) >>= (fun zs'=> Ret (ys' ++ [:: p] ++ zs')))); last first.
  rewrite bindA; bind_ext => -[s1 s2];rewrite !bindA; congr (_ >> _).
  by rewrite boolp.funeqE => -[]; rewrite bindretf bindA.
(*apply: bind_monotonic_refin.
have := refin_partition p xs.
by rewrite /assert; unlock.
Qed.*) (*TODO: broken since HB *) Admitted.

Program Fixpoint qsort' (s : seq T)
    (f : forall s', (size s' < size s)%N -> seq T) : seq T :=
  if s isn't p :: xs then [::] else
  let: (ys, zs) := partition p xs in
  f ys _ ++ [:: p] ++ f zs _.
Next Obligation.
have := size_partition p xs.
by rewrite -Heq_anonymous /= => <-; rewrite ltnS leq_addr.
Qed.
Next Obligation.
have := size_partition p xs.
by rewrite -Heq_anonymous /= => <-; rewrite ltnS leq_addl.
Qed.

Definition qsort : seq T -> seq T :=
  Fix (@well_founded_size _) (fun _ => _) qsort'.

Lemma qsort'_Fix (x : seq T)
  (f g : forall y : seq T, (size y < size x)%N -> seq T) :
  (forall (y : seq T) (p : (size y < size x)%N), f y p = g y p) ->
  qsort' f = qsort' g.
Proof.
by move=> ?; congr qsort'; apply fun_ext_dep => ?; rewrite boolp.funeqE.
Qed.

Lemma qsort_nil : qsort [::] = [::].
Proof. by rewrite /qsort Fix_eq //; exact: qsort'_Fix. Qed.

Lemma qsort_cons p (xs : seq T) :
  qsort (p :: xs) = let: (ys, zs) := partition p xs in
                    qsort ys ++ [:: p] ++ qsort zs.
Proof.
rewrite [in LHS]/qsort Fix_eq /=; last exact: qsort'_Fix.
by move s12 : (partition p xs) => h; case: h s12.
Qed.

Definition qsortE := (qsort_nil, qsort_cons).

Lemma quicksort_on_lists : Ret \o qsort `<.=` slowsort.
Proof.
move=> s.
  have [n sn] := ubnP (size s); elim: n => // n ih in s sn *.
  case: s => [|h t] in sn *.
    rewrite /= qsort_nil slowsort_nil. exact: refin_refl.
  rewrite /= qsort_cons.
  move pht : (partition h t) => ht.
  case: ht => ys zs in pht *.
  apply: (refin_trans _ (refin_slowsort h t)).
  rewrite bindretf pht.
  rewrite -(ih ys).
  rewrite -(ih zs).
  repeat rewrite alt_bindDl bindretf.
  rewrite /refin !altA altmm //.
  (*TODO: problems of size*)
Admitted.

(* TODO: Ret \o qsort `<.=` slowsort by induction on the length of the input list *)

End slowsort.

Goal qsort [:: 3; 42; 230; 1; 67; 2]%N = [:: 1; 2; 3; 42; 67; 230]%N.
by repeat rewrite qsortE /=. Abort.

Goal let s := [:: 3; 42; 230; 1; 67; 2]%N in qsort s = sort ltn s.
move=> s; rewrite /s sortE /=.
by repeat rewrite qsortE /=.
Abort.

Definition size_preserving (M : monad) (A : UU0) (f : seq A -> M (seq A)) :=
  forall xs, f xs >>= (fun ys => Ret (ys, size ys)) = f xs >>= (fun ys => Ret (ys, size xs)).

Lemma size_preserving_qperm (M : plusMonad) (A : UU0) :
  size_preserving (@qperm M A).
Proof.
move=> s; move sn : (size s) => n.
elim/ltn_ind: n s sn => n ih [/= <-{ih n}| h t].
  by rewrite qperm_nil 2!bindretf.
case: n ih => // n ih [tn].
rewrite qperm_cons.
rewrite splitsE /=.
Abort.

Section scratch_saito.
Variable M : plusMonad.
Lemma eq1 A B (f : A -> M B) : fail >>= f = fail.
Proof. by apply: bindfailf. Qed.
Lemma eq2 A (m : M A) : m >> fail = (@fail M A).
Proof. by apply: (@bindmfail M). Qed.
  (* move: (@bindmfail M). rewrite /BindLaws.right_zero. //. Qed. *)
Lemma eq3 A B (m1 m2 : M A) (f : A -> M B) : 
  (m1 [~] m2) >>= f = (m1 >>= f) [~] (m2 >>= f).
Proof. by apply: alt_bindDl. Qed.
Lemma eq4 A B (m : M A) (f1 f2 : A -> M B) :
  m >>= (fun x => f1 x [~] f2 x) = (m >>= f1) [~] (m >>= f2).
Proof. by apply: alt_bindDr. Qed.

Variables (d : unit) (T : porderType d).
(* Variables (r : rel T) (r_trans : transitive r). *)
Let leT : rel T := (fun x y : T => x <= y)%O.
Let geT := (fun x y : T => y <= x)%O.

Lemma sorted_cons {r : rel T} {r_trans : transitive r} (x : T) (xs : seq T) :
  sorted r (x :: xs) = sorted r xs && all (r x) xs.
Proof.
  apply/idP/idP => [ /= xxs |/andP[ _ /path_min_sorted /= ->//]].
  rewrite (order_path_min r_trans xxs) ?andbT//.
  exact: path_sorted xxs.
Qed.

Lemma rev_transitivity {r : rel T} {r_trans : transitive r}:
  (transitive (fun x y : T => r^~ x y)).
Proof.
  move=> y x z h1 h2. move: h2 h1.
  by apply r_trans.
Qed.

Lemma sorted_rcons {r : rel T} {r_trans : transitive r} (x : T) (xs : seq T) :
  sorted r (rcons xs x) = sorted r xs && all (r^~ x) xs.
Proof.
  rewrite -rev_sorted rev_rcons sorted_cons.
  rewrite rev_sorted all_rev //.
  apply (@rev_transitivity _ r_trans).
Qed.

Local Notation sorted := (sorted leT).

Lemma sorted_cons' (x : T) (xs : seq T) :
  sorted (x :: xs) = sorted xs && all (leT x) xs.
Proof. by rewrite sorted_cons //; apply le_trans. Qed.

Lemma sorted_rcons' (x : T) (xs : seq T) :
 sorted (rcons xs x) = sorted xs && all (geT x) xs.
Proof. by rewrite sorted_rcons //; apply le_trans. Qed.
(* Proof. by rewrite -rev_sorted rev_rcons (@sorted_cons _ ge_trans) rev_sorted all_rev. Qed. *)

Lemma sorted_cat_cons' (x : T) (ys zs : seq T) : 
  sorted (ys ++ x :: zs) = [&& sorted ys, sorted zs, all (<= x) ys & all (>= x) zs].
Proof.
  apply/idP/idP => H.
  (* -> *)
  have Hr : sorted (ys) && sorted (x :: zs) by apply sorted_cat'.
  rewrite -cat1s catA cats1 in H.
  have Hl : sorted (rcons ys x) && sorted (zs) by apply sorted_cat'.
  move: Hl Hr. rewrite sorted_cons' sorted_rcons' andbC => /and3P[] ? ? ? /and3P[] _ _ ?.
  apply /and4P; split => //.
  (* <- *)
  move: H => /and4P[] p1 p2 allYs allZs.
  rewrite sorted_cat //.
  by rewrite sorted_cons'; apply/andP; split.
  move => a ha b hb.
  apply /(@le_trans _ _ x).
  by move/allP : allYs; apply.
  move: hb; rewrite inE => /orP[/eqP -> //|].
  by move/allP : allZs; apply.
Qed.

(* Lemma eq7 A (p q : bool) (m1 m2 : M A) :
  (if p then m1 else m2) `<=` (guard p >> m1) [~] (guard (~~ p) >> m2).
Proof.
  rewrite /refin; case: ifPn => /= [pT|pF]; rewrite !(guardT,guardF).
  by rewrite bindskipf bindfailf altA altmm.
  by rewrite bindfailf bindskipf altCA altmm.
Qed. *)

Definition nondetState_sub S (M : nondetStateMonad S) A (n : M A) :=
  {m | ndDenote m = n}.

Definition commute {M : monad} A B (m : M A) (n : M B) C (f : A -> B -> M C) : Prop :=
  m >>= (fun x => n >>= (fun y => f x y)) = n >>= (fun y => m >>= (fun x => f x y)) :> M _.

Lemma div1 (p : T) (xs : seq T) : 
  slowsort M (p :: xs) = 
  splits xs >>= (fun '(ys, zs) =>
  qperm ys >>= (fun ys' => qperm zs >>= (fun zs' =>
  assert sorted (ys' ++ [:: p] ++ zs')))).
Proof.
  (* expanding definitions, monad laws *)
  rewrite /slowsort.
  rewrite /= kleisliE.
  rewrite qperm_cons /=.
  rewrite bindA.
  bind_ext => -[? ?].
  rewrite /liftM2.
  rewrite bindA; bind_ext => ?.
  rewrite bindA; bind_ext => ?.
  rewrite bindretf.
  done.
Qed.

Lemma div2 (p : T) (xs : seq T) :
  (@splits M _ xs) >>= (fun '(ys, zs) =>
    qperm ys >>= (fun ys' => qperm zs >>= (fun zs' =>
    assert sorted (ys' ++ [:: p] ++ zs')))) =
  splits xs >>= (fun '(ys, zs) =>
      qperm ys >>= (fun ys' => qperm zs >>= (fun zs' =>
      guard ([&& sorted ys', sorted zs', all (<= p) ys' & all (>= p) zs']) >>
      Ret (ys' ++ [:: p] ++ zs')))).
Proof.
  bind_ext => -[? ?]; bind_ext => ?; bind_ext => ?; rewrite assertE /=.
  by rewrite -sorted_cat_cons'. (* by (5) *)
Qed.

Lemma div3 (p : T) (xs : seq T) :
  (@splits M _ xs) >>= (fun '(ys, zs) =>
  qperm ys >>= (fun ys' => 
  qperm zs >>= (fun zs' =>
  guard ([&& sorted ys', sorted zs', all (<= p) ys' & all (>= p) zs']) >>
  Ret (ys' ++ [:: p] ++ zs')))) =
  (@splits M _ xs) >>= (fun '(ys, zs) =>
  qperm ys >>= (fun ys' => 
  qperm zs >>= (fun zs' =>
  guard (sorted ys') >>= (fun _ => 
  guard (sorted zs') >>= (fun _ =>
  guard (all (<= p) ys') >>= (fun _ =>
  guard (all (>= p) zs') >>= (fun _ =>
  Ret (ys' ++ [:: p] ++ zs')))))))).
Proof.
  bind_ext => -[? ?].
  bind_ext => ?.
  bind_ext => ?.
  by rewrite !guard_and !bindA. (* by (6) *)
Qed.

Lemma rev_rev : forall (xs : seq T), rev (rev xs) = xs.
Proof. by induction xs => //; rewrite rev_cons rev_rcons IHxs. Qed.

End scratch_saito.
