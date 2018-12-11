Require Import FunctionalExtensionality Coq.Program.Tactics ProofIrrelevance.
Require Classical.
Require Import ssreflect ssrmatching ssrfun ssrbool.
From mathcomp Require Import eqtype ssrnat seq choice fintype tuple.
From mathcomp Require Import finfun finset bigop.
From mathcomp Require Import boolp classical_sets.

Require Import monad monad_composition monad_model.
Require Import proba_monad. (* NB(rei): just to have the reserved for <| and `Pr *)

Require Import Reals Lra.
From infotheo Require Import ssrR Reals_ext Rbigop proba.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* wip *)
(* ref: cheung phd *)

Local Open Scope reals_ext_scope.

Local Open Scope proba_scope.

Lemma dist_supp1 (d : {dist 'I_1}) : dist_supp d = ([set ord0])%SET.
Proof.
case: d => -[/= f f0] f1; apply/setP => i.
rewrite (ssr_ext.ord1 i) /= !inE /= eqxx.
move: f1; rewrite big_ord_recl big_ord0 addR0 => ->; exact/eqP.
Qed.

Lemma FamilyDist1 (A : finType) (g : 'I_1 -> dist A) (d : {dist 'I_1}) :
  FamilyDist.d g d = g ord0.
Proof.
apply/dist_ext => a.
rewrite FamilyDist.dE /= big_ord_recl /= big_ord0 addR0.
suff -> : d ord0 = 1%R by rewrite mul1R.
apply/dist_supp_singleP; by rewrite dist_supp1.
Qed.

Lemma FamilyDist2 (A : finType) (g : 'I_2 -> dist A) (d : {dist 'I_2}) H :
  FamilyDist.d g d = @ConvexDist.d _ (g ord0) (g (lift ord0 ord0)) (d ord0) H.
Proof.
apply/dist_ext => a.
rewrite FamilyDist.dE /= 2!big_ord_recl /= big_ord0 addR0 ConvexDist.dE.
congr (_ + _ * _)%R.
move: (pmf1 d); rewrite 2!big_ord_recl big_ord0 addR0 => /eqP.
by rewrite eq_sym addRC -subR_eq => /eqP <-.
Qed.

Local Close Scope proba_scope.

Module DistBelast.
Local Open Scope proba_scope.
Section distbelast.
Variables (n : nat) (e : {dist 'I_n.+1}) (emax1 : e ord_max != 1%R).

Let D : {dist 'I_n.+1} := D1Dist.d emax1.

Definition f := fun i => D (widen_ord (leqnSn _) i).

Lemma f0 i : (0 <= f i)%R. Proof. exact/dist_ge0. Qed.

Lemma f1 : \rsum_(i < n) f i = 1%R.
Proof.
rewrite -(pmf1 D) big_ord_recr /= {2}/D D1Dist.dE eqxx addR0.
apply eq_bigr => i _; rewrite /f /D D1Dist.dE /= ifF //.
apply/negP => /eqP/(congr1 val) => /= ni; move: (ltn_ord i); by rewrite ni ltnn.
Qed.

Definition d := locked (makeDist f0 f1).

Lemma dE i : d i = D (widen_ord (leqnSn _) i).
Proof. by rewrite /d; unlock. Qed.
End distbelast.

Section prop.
Variables (A : finType) (n : nat) (g : 'I_n.+1 -> dist A) (d : {dist 'I_n.+1}).
Lemma Convex H (dmax1 : d ord_max != 1%R) :
  let g' := (fun i : 'I_n => g (widen_ord (leqnSn _) i)) in
  FamilyDist.d g d =
  @ConvexDist.d _ (FamilyDist.d g' (DistBelast.d dmax1)) (g ord_max)
    (d ord_max).~ (Prob.Op1 (Prob.mk H)).
Proof.
move=> g' /=.
apply/dist_ext => a.
rewrite ConvexDist.dE 2!FamilyDist.dE big_ord_recr /= onemK; congr (_ + _)%R.
rewrite big_distrr /=; apply eq_bigr => i _.
rewrite DistBelast.dE D1Dist.dE /= ifF; last first.
  apply/negP => /eqP/(congr1 val) => /= ni.
  move: (ltn_ord i); by rewrite ni ltnn.
rewrite mulRA; congr (_ * _)%R.
by rewrite mulRCA mulRV ?mulR1 // subR_eq0 eq_sym.
Qed.
End prop.
End DistBelast.

Module CatDist.
Section catdist.
Local Open Scope proba_scope.
Variables (n m : nat) (d1 : {dist 'I_n}) (d2 : {dist 'I_m}) (p : R) (Hp : (0 <= p <= 1)%R).

Definition f (i : 'I_(n + m)) :=
  match fintype.split i with | inl a => (p * d1 a)%R | inr a => (p.~ * d2 a)%R end.

Lemma f0 i : (0 <= f i)%R.
Proof.
rewrite /f; case: splitP => a _.
apply mulR_ge0; [by case: Hp|exact/dist_ge0].
apply mulR_ge0; [by apply/onem_ge0; case: Hp|exact/dist_ge0].
Qed.

Lemma f1 : \rsum_(i < n + m) f i = 1%R.
Proof.
rewrite -(onemKC p) -{1}(mulR1 p) -(mulR1 p.~)%R.
rewrite -{1}(pmf1 d1) -(pmf1 d2) big_split_ord /=; congr (_ + _)%R.
rewrite big_distrr /=; apply eq_bigr => i _; rewrite /f; case: splitP.
  move=> j Hj; congr (_ * d1 _)%R.
  apply/val_inj => /=; by rewrite -Hj.
  move=> k /= Hi.
  move: (ltn_ord i); by rewrite Hi -ltn_subRL subnn ltn0.
rewrite big_distrr /=; apply eq_bigr => i _; rewrite /f; case: splitP.
  move=> j /= Hi.
  move: (ltn_ord j); by rewrite -Hi -ltn_subRL subnn ltn0.
  move=> k /= /eqP; rewrite eqn_add2l => /eqP ik.
  congr (_ * d2 _)%R.
  exact/val_inj.
Qed.

Definition d : {dist 'I_(n + m)} := locked (makeDist f0 f1).

Lemma dE i : d i = match fintype.split i with | inl a => (p * d1 a)%R | inr a => (p.~ * d2 a)%R end.
Proof. by rewrite /d; unlock. Qed.
End catdist.
Section prop.
Local Open Scope proba_scope.
Variables (n m : nat) (d1 : {dist 'I_n}) (d2 : {dist 'I_m}) (p : R) (Hp : (0 <= p <= 1)%R).
Lemma ConvexFamily (A : finType) (g : 'I_n -> dist A) (h : 'I_m -> dist A) :
  ConvexDist.d (FamilyDist.d g d1) (FamilyDist.d h d2) Hp =
  FamilyDist.d [ffun i => match fintype.split i with
                            | inl a => g a
                            | inr a => h a
                            end] (d d1 d2 Hp).
Proof.
apply/dist_ext => a.
rewrite !ConvexDist.dE !FamilyDist.dE.
rewrite 2!big_distrr /= big_split_ord /=; congr (_ + _)%R;
  apply eq_bigr => i _; rewrite dE ffunE.
case: splitP => /= j ij.
rewrite mulRA; congr (_ * d1 _ * (g _) a)%R; exact/val_inj.
move: (ltn_ord i); by rewrite ij -ltn_subRL subnn ltn0.
case: splitP => /= j ij.
move: (ltn_ord j); by rewrite -ij -ltn_subRL subnn ltn0.
move/eqP : ij; rewrite eqn_add2l => /eqP ij.
rewrite mulRA; congr (_ * d2 _ * (h _) a)%R; exact/val_inj.
Qed.
End prop.
End CatDist.

Reserved Notation "mx <.| p |.> my" (format "mx  <.| p |.>  my", at level 50).

Section model.
Local Open Scope proba_scope.
Local Open Scope classical_set_scope.
Variable A : finType.

Definition convex (X : set (dist A)) : bool :=
  `[< forall x y p, x \in X -> y \in X -> ConvexDist.d x y (Prob.Op1 p) \in X >].

Lemma convex0 : convex set0.
Proof. apply/asboolP => x y p; by rewrite in_setE. Qed.

Definition convex_n (X : set (dist A)) : bool :=
  `[< forall n (g : 'I_n -> dist A) (d : {dist 'I_n}),
      g @` setT `<=` X -> FamilyDist.d g d \in X >].

Lemma convexP (X : set (dist A)) : convex X = convex_n X.
Proof.
apply/idP/idP => H; apply/asboolP.
  elim => [g d|n IH g d].
    by move: (dist_domain_not_empty d); rewrite card_ord ltnn.
  destruct n as [|n] => gX.
    rewrite {IH} FamilyDist1 in_setE; exact/gX/classical_sets.imageP.
  case/boolP : (d ord_max == 1%R) => dmax1.
    suff -> : FamilyDist.d g d = g ord_max by rewrite in_setE; apply gX; exists ord_max.
    apply/dist_ext => a; rewrite FamilyDist.dE big_ord_recr /= (eqP dmax1) ?mul1R.
    rewrite big1 ?add0R // => i _.
    rewrite (_ : d _ = 0%R) ?mul0R //; apply/eqP.
    move/eqP : dmax1 => /dist_supp_singleP/eqP/setP/(_ (widen_ord (leqnSn _) i)).
    rewrite !inE => /(congr1 negb).
    rewrite negbK /= => ->.
    apply/eqP => /(congr1 val) /= ni.
    move: (ltn_ord i); by rewrite ni ltnn.
  set D : {dist 'I_n.+2} := D1Dist.d dmax1.
  set d' := DistBelast.d dmax1.
  pose g' : 'I_n.+1 -> dist A := fun i => g (widen_ord (leqnSn _) i).
  have g'X : g' @` classical_sets.setT `<=` X.
    move=> x -[i _ <-{x}]; by apply gX; exists (widen_ord (leqnSn _) i).
  move: {IH}(IH g' d' g'X) => IH.
  have Htmp : (0 <= 1 - d ord_max <= 1)%R by split; [exact/onem_ge0/dist_max|exact/onem_le1/dist_ge0].
  have -> : FamilyDist.d g d =
    ConvexDist.d (FamilyDist.d g' d') (g ord_max) (Prob.Op1 (Prob.mk Htmp)).
    by rewrite DistBelast.Convex.
  move/asboolP : H; apply => //.
  rewrite in_setE; apply gX.
  exists (lift ord0 ord_max) => //=; congr g; exact/val_inj.
move=> x y p xX yX.
pose f : 'I_2 -> R := [eta (fun=>R0) with ord0 |-> Prob.p p, 1 |-> ((Prob.p p).~)%R].
have f0 : forall i, (0 <= f i)%R.
  move=> i; rewrite /f /=; case: ifP => _.
    by case: (Prob.Op1 p).
  case: ifPn => _; last exact/leRR.
  apply onem_ge0; by case: (Prob.Op1 p).
have f1 : \rsum_(i < 2) f i = 1%R by rewrite 2!big_ord_recl big_ord0 addR0 /f /= onemKC.
pose g : 'I_2 -> dist A := [eta (fun=>x) with ord0 |-> x, 1 |-> y].
have -> : ConvexDist.d x y (Prob.Op1 p) = FamilyDist.d g (makeDist f0 f1).
  rewrite FamilyDist2.
  split; [exact/dist_ge0|exact/dist_max].
  move=> H'; congr ConvexDist.d; exact: ProofIrrelevance.proof_irrelevance.
move/asboolP : H; apply => d -[i _ <-{d}].
rewrite /g /=; case: ifP => _; first by rewrite -in_setE.
case: ifP => _; by rewrite -in_setE.
Qed.

Record convset : Type := mkCset {
  car :> set (dist A) ;
  Hcset : convex car }.

Canonical convset_subType := [subType for car].

Canonical convset_predType :=
  Eval hnf in mkPredType (fun t : convset => (fun x => x \in car t)).

Definition convset0 : convset := mkCset convex0.

Definition hull (X : set (dist A)) : set (dist A) :=
  [set d | exists n, exists g : 'I_n -> dist A, exists e : {dist 'I_n},
    g @` classical_sets.setT `<=` X /\ d = FamilyDist.d g e].

Lemma hull_convset (X : convset) : hull X = X.
Proof.
rewrite predeqE => d; split.
- move=> -[n [g [e [gX ->{d}]]]].
  move: (Hcset X);   rewrite convexP /convex_n => /asboolP/(_ _ g e gX).
  by rewrite in_setE.
- move=> Xd; rewrite /hull.
  exists 1, (fun x : 'I_1 => d), (Dist1.d ord0).
  split.
    move=> e; by case=> x _ <-.
  apply/dist_ext => a.
  by rewrite FamilyDist.dE big_ord_recl big_ord0 addR0 Dist1.dxx mul1R.
Qed.

Lemma convex_hull (X : set (dist A)) : convex (hull X).
Proof.
apply/asboolP => x y p; rewrite 2!in_setE.
move=> -[n [g [d [gX ->{x}]]]].
move=> -[m [h [e [hX ->{y}]]]].
rewrite in_setE.
exists (n + m).
exists [ffun i => match fintype.split i with inl a => g a | inr a => h a end].
exists (CatDist.d d e (Prob.Op1 p)).
rewrite CatDist.ConvexFamily; split => //.
move=> a -[i _].
rewrite ffunE.
case: splitP => j _ <-; by [apply gX; exists j | apply hX; exists j].
Qed.

Definition P (X : set (dist A)) :=
  [set Y : set (dist A) | (Y `<=` X) /\ (Y !=set0) /\ convex Y].

Definition pchoice' (p : prob) (X Y : convset) : set (dist A) :=
  [set d | exists x, x \in X /\ exists y, y \in Y /\ d = ConvexDist.d x y (Prob.Op1 p)].

Lemma pchoice'_self (p : prob) (X : convset) :
  [set d | exists x, x \in car X /\ d = ConvexDist.d x x (Prob.Op1 p)] `<=` pchoice' p X X.
Proof.
move=> d [x [xX ->{d}]]; rewrite /pchoice'.
exists x; split => //; by exists x; split.
Qed.

Lemma Hpchoice (p : prob) (X Y : convset) : convex (pchoice' p X Y).
Proof.
apply/asboolP => x y q /=; rewrite in_setE => -[d [dX [d' [d'Y ->]]]].
rewrite in_setE => -[e [eX [e' [e'Y ->]]]]; rewrite in_setE ConvexDist.commute.
exists (ConvexDist.d d e (Prob.Op1 q)); split; first exact: (asboolW (Hcset X)).
exists (ConvexDist.d d' e' (Prob.Op1 q)); split => //; exact: (asboolW (Hcset Y)).
Qed.

Definition pchoice (p : prob) (X Y : convset) : convset :=  mkCset (@Hpchoice p X Y).

Local Notation "mx <.| p |.> my" := (@pchoice p mx my).

Lemma pchoice0 (a b : convset) : a !=set0 -> a <.| `Pr 0 |.> b = b.
Proof.
move=> a0; apply/val_inj=> /=; rewrite /pchoice' predeqE => d; split.
- move=> [x [xa]] [y [yb ->{d}]]; by rewrite -in_setE ConvexDist.d0.
- move=> bd; case: a0 => d' ad'; exists d'; split; first by rewrite in_setE.
  exists d; split; by [rewrite in_setE | rewrite ConvexDist.d0].
Qed.

Lemma pchoice1 (a b : convset) : b !=set0 -> a <.| `Pr 1 |.> b = a.
Proof.
move=> b0; apply/val_inj => /=; rewrite /pchoice' predeqE => d; split.
- move=> [x [xa]] [y [yb ->{d}]]; by rewrite -in_setE ConvexDist.d1.
- move=> ad; case: b0 => d' bd'; exists d; split; first by rewrite in_setE.
  exists d'; split; by [rewrite in_setE | rewrite ConvexDist.d1].
Qed.

Lemma pchoiceC p (x y : convset) : x <.| p |.> y = y <.| `Pr p.~ |.> x.
Proof.
apply/val_inj/classical_sets.eqEsubset => /=; rewrite /pchoice'.
- move=> d [a [aX [b [bY ->{d}]]]].
  exists b; split => //; exists a; split => //; rewrite ConvexDist.quasi_commute //.
  split; by [apply/onem_ge0/(proj2 (Prob.Op1 p)) | apply/onem_le1/(proj1 (Prob.Op1 p))].
  move=> Hp; by rewrite (ProofIrrelevance.proof_irrelevance _ Hp (Prob.Op1 `Pr p.~)).
- move=> d [a [aY [b [bX ->{d}]]]].
  exists b; split => //; exists a; split => //; rewrite ConvexDist.quasi_commute //.
  rewrite onemK; by case: p.
  rewrite onemK => Hp; by rewrite (ProofIrrelevance.proof_irrelevance _ Hp (Prob.Op1 p)).
Qed.

Lemma pchoicemm p : idempotent (pchoice p).
Proof.
move=> Y; apply/val_inj/classical_sets.eqEsubset => /=.
- move=> d; rewrite /pchoice' => -[x [Hx [y [Hy ->{d}]]]].
  by rewrite -in_setE (asboolW (Hcset Y)).
- apply: classical_sets.subset_trans; last exact: pchoice'_self.
  set Y' := (X in _ `<=` X). suff : Y = Y' :> set (dist A) by move=> <-. rewrite {}/Y'.
  transitivity [set y | y \in Y].
    rewrite predeqE => d; split; by rewrite in_setE.
  rewrite predeqE => d; split.
  - move=> dY; exists d; split => //; by rewrite ConvexDist.idempotent.
  - case=> d' [d'Y ->{d}]; by rewrite (asboolW (Hcset Y)).
Qed.

Lemma pchoiceA (p q r s : prob) (x y z : convset) :
  (p = r * s :> R /\ s.~ = p.~ * q.~)%R ->
  x <.| p |.> (y <.| q |.> z) = (x <.| r |.> y) <.| s |.> z.
Proof.
move=> [H1 H2]; apply/val_inj/classical_sets.eqEsubset => /=.
- move=> d; rewrite /pchoice' => -[a [xa [b []]]].
  rewrite in_setE /= {1}/pchoice' => -[b1 [b1y [b2 [b2z ->{b} ->{d}]]]].
  exists (ConvexDist.d a b1 (Prob.Op1 r)); split.
    rewrite in_setE /= /pchoice'; exists a; split => //; by exists b1.
  exists b2; split => //; rewrite (@ConvexDist.quasi_assoc _ _ _ r s) //.
  by rewrite {H1}; case: r.
  by rewrite {H1 H2}; case: s.
  move=> Hr Hs; rewrite (ProofIrrelevance.proof_irrelevance _ Hr (Prob.Op1 r)).
  by rewrite (ProofIrrelevance.proof_irrelevance _ Hs (Prob.Op1 s)).
- move=> d; rewrite /pchoice' => -[a []].
  rewrite in_setE /= {1}/pchoice' => -[a1 [a1x [a2 [a2y ->{a}]]]] => -[b] [bz ->{d}].
  exists a1; split => //.
  exists (ConvexDist.d a2 b (Prob.Op1 q)); split.
    rewrite in_setE /= /pchoice'; exists a2; split => //; by exists b.
  rewrite (@ConvexDist.quasi_assoc _ _ _ r s) //.
  by rewrite {H1}; case: r.
  by rewrite {H1 H2}; case: s.
  move=> Hr Hs; rewrite (ProofIrrelevance.proof_irrelevance _ Hr (Prob.Op1 r)).
  by rewrite (ProofIrrelevance.proof_irrelevance _ Hs (Prob.Op1 s)).
Qed.

Definition ndchoice' (X Y : set (dist A)) : set (dist A) := hull (X `|` Y).

Lemma Hndchoice (X Y : convset) : convex (ndchoice' X Y).
Proof.
apply/asboolP => x y p.
rewrite /ndchoice' => Hx Hy.
have := convex_hull (X `|` Y).
by move/asboolP => /(_ x y p Hx Hy).
Qed.

Definition ndchoice (X Y : convset) : convset :=  mkCset (@Hndchoice X Y).

Lemma ndchoicemm : idempotent ndchoice.
Proof.
move=> d; apply/val_inj => /=.
rewrite /ndchoice' setUid; exact: hull_convset.
Qed.

End model.
