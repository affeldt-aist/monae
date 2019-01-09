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

(*Section set_eqType.
Local Open Scope classical_set_scope.

Variable A : Type.

Definition eqset (x y : set A) : bool := `[< x `<=>` y >].

Lemma eqsetP : Equality.axiom eqset.
Proof.
move=> ? ?; apply: (iffP idP) => [/asboolP[]|->];
  [exact: eqEsubset |by apply/asboolP; split].
Qed.

Canonical set_eqMixin := EqMixin eqsetP.
Canonical set_eqType := Eval hnf in EqType _ set_eqMixin.

End set_eqType.*)

Module Dist2.
Section dist2.
Variables (A : Type) (p : R) (Op1 : (0 <= p <= 1)%R).

Definition f : 'I_2 -> R := [eta (fun=>R0) with ord0 |-> p, 1 |-> p.~].

Lemma f0 : forall i, (0 <= f i)%R.
Proof.
move=> i; rewrite /f /=; case: ifP => _; first by case: Op1.
case: ifPn => _; [apply onem_ge0; by case: Op1 | exact/leRR].
Qed.

Lemma f1 : \rsum_(i < 2) f i = 1%R.
Proof. by rewrite 2!big_ord_recl big_ord0 addR0 /f /= onemKC. Qed.

Definition d := locked (makeDist f0 f1).

Lemma dE a : d a = [eta (fun=>R0) with ord0 |-> p, 1 |-> p.~] a.
Proof. by rewrite /d; unlock. Qed.

End dist2.
End Dist2.

Section convex_distributions.
Local Open Scope classical_set_scope.
Local Open Scope proba_scope.
Variable A : finType.

Definition convex (X : set (dist A)) : bool :=
  `[< forall x y p, x \in X -> y \in X -> ConvexDist.d x y (Prob.Op1 p) \in X >].

Lemma convex0 : convex set0.
Proof. apply/asboolP => x y p; by rewrite in_setE. Qed.

Lemma convexT : convex setT.
Proof. apply/asboolP => ? ? ? _ _; by rewrite in_setE. Qed.

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
pose g : 'I_2 -> dist A := [eta (fun=>x) with ord0 |-> x, 1 |-> y].
have -> : ConvexDist.d x y (Prob.Op1 p) = FamilyDist.d g (Dist2.d (Prob.Op1 p)).
  rewrite FamilyDist2.
  split; [exact/dist_ge0|exact/dist_max].
  rewrite Dist2.dE /= => H'; congr ConvexDist.d; exact: ProofIrrelevance.proof_irrelevance.
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

Definition convset_eqMixin := Eval hnf in [eqMixin of convset by <:].
Canonical convset_eqType := Eval hnf in EqType convset convset_eqMixin.

Definition convset0 : convset := mkCset convex0.

Lemma convset0P (x : convset) : (x == convset0) = (x == set0 :> set _).
Proof. by case: x. Qed.

Lemma convset0PN (x : convset) : (x != convset0) <-> (x !=set0).
Proof.
rewrite convset0P; case: x => //= x Hx; split; last first.
  case=> a xa; apply/eqP => x0; move: xa; by rewrite x0.
by case/set0P => /= d dx; exists d.
Qed.

Definition hull (X : set (dist A)) : set (dist A) :=
  [set d | exists n, exists g : 'I_n -> dist A, exists e : {dist 'I_n},
    g @` classical_sets.setT `<=` X /\ d = FamilyDist.d g e].

Lemma hull_mem (X : set (dist A)) x : x \in X -> x \in hull X.
Proof.
move=> xX.
rewrite in_setE /hull.
exists 1, (fun i : 'I_1 => x), (Dist1.d ord0); split.
  move=> d -[i _ <-]; by rewrite -in_setE.
apply/dist_ext => a.
by rewrite FamilyDist.dE big_ord_recl big_ord0 addR0 Dist1.dE eqxx mul1R.
Qed.

Lemma hull0 : hull set0 = set0.
Proof.
rewrite funeqE => d; rewrite propeqE; split => //.
case=> n [g [e [gX ->{d}]]].
destruct n as [|n].
  exfalso; move/dist_domain_not_empty : e; by rewrite card_ord ltnn.
exfalso; apply: (gX (g ord0)); exact/imageP.
Qed.

Lemma hull_eq0 (X : set (dist A)) : (hull X == set0) = (X == set0).
Proof.
apply/idP/idP=> [/eqP abs|]; last by move=> /eqP ->; rewrite hull0.
apply/negPn/negP => /set0P[/= d]; rewrite -in_setE => dX.
move: abs; rewrite funeqE => /(_ d); rewrite propeqE /set0 => -[H _]; apply H.
by rewrite -in_setE; apply: hull_mem.
Qed.

Lemma hull_convset (X : convset) : hull X = X.
Proof.
rewrite predeqE => d; split.
- move=> -[n [g [e [gX ->{d}]]]].
  move: (Hcset X);   rewrite convexP /convex_n => /asboolP/(_ _ g e gX).
  by rewrite in_setE.
- by rewrite -in_setE => /hull_mem; rewrite in_setE.
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

Lemma hullI (X : set (dist A)) : hull (hull X) = hull X.
Proof. by rewrite (hull_convset (mkCset (convex_hull _))). Qed.

Lemma mem_hull_setU (x y : set (dist A)) (a0 a1 : dist A) p (Op1 : (0 <= p <= 1)%R) : a0 \in x -> a1 \in y ->
  ConvexDist.d a0 a1 Op1 \in hull (x `|` y).
Proof.
move=> a0x a1y.
rewrite in_setE.
exists 2, [eta (fun=> a0) with ord0 |-> a0, lift ord0 ord0 |-> a1], (Dist2.d Op1); split => /=.
  move=> a2.
  rewrite -in_setE.
  case/imsetP => i _ ->{a2} /=.
  case: ifPn => _.
  by rewrite -in_setE in_setU a0x.
  case: ifPn => _; rewrite -in_setE in_setU.
  apply/orP; by right.
  apply/orP; by left.
apply/dist_ext => a2.
by rewrite ConvexDist.dE FamilyDist.dE 2!big_ord_recl big_ord0 addR0 /= 2!Dist2.dE.
Qed.

Lemma mem_hull_setU_left (x y : set (dist A)) (a : dist A) : a \in x -> a \in hull (x `|` y).
Proof. by move=> ax; apply: hull_mem; rewrite in_setU ax. Qed.

Definition e_restrict_codom_pmf n (g : 'I_n -> dist A) (y : set (dist A)) (e : {dist 'I_n}) :=
  fun i : 'I_n => if g i \in y then e i else 0%R.

Lemma e_restrict_codom_pmf0 n (g : 'I_n -> dist A) y e i : (0 <= e_restrict_codom_pmf g y e i)%R.
Proof.
rewrite /e_restrict_codom_pmf.
case: ifPn => _; [exact/dist_ge0|exact/leRR].
Qed.

Lemma e_restrict_codom_pmf1 n (g : 'I_n -> dist A) (x y : set (dist A)) (e : {dist 'I_n})
  (ge : forall i : 'I_n, g i \in x -> e i = 0%R) (gX : g @` setT `<=` x `|` y) :
  (\rsum_(i < n) e_restrict_codom_pmf g y e i = 1)%R.
Proof.
rewrite /e_restrict_codom_pmf -(pmf1 e) /=.
apply eq_bigr => i _.
case: ifPn => // giy.
rewrite ge //.
have : g i \in x `|` y by rewrite in_setE; apply/gX; by exists i.
rewrite in_setU => /orP[|] //.
by rewrite (negbTE giy).
Qed.

Definition e_restrict_codom n (g : 'I_n -> dist A) (x y : set (dist A)) (e : {dist 'I_n})
  (ge : forall i : 'I_n, g i \in x -> e i = 0%R) (gX : g @` setT `<=` x `|` y) :=
  locked (makeDist
  (e_restrict_codom_pmf0 g y e) (e_restrict_codom_pmf1 ge gX)).

Lemma e_restrict_codomE n (g : 'I_n -> dist A) (x y : set (dist A)) (e : {dist 'I_n})
  (ge : forall i : 'I_n, g i \in x -> e i = 0%R) (gX : g @` setT `<=` x `|` y) i :
  e_restrict_codom ge gX i = if g i \in y then e i else 0%R.
Proof. by rewrite /e_restrict_codom; unlock. Qed.

Lemma e_restrict_codom_pmf1' n (g : 'I_n -> dist A) (x y : set (dist A)) (e : {dist 'I_n})
  (ge : forall i : 'I_n, (g i \in x) && (g i \notin y) -> e i = 0%R) (gX : g @` setT `<=` x `|` y) :
  (\rsum_(i < n) e_restrict_codom_pmf g y e i = 1)%R.
Proof.
rewrite /e_restrict_codom_pmf -(pmf1 e) /=.
apply eq_bigr => i _.
case: ifPn => // giy.
rewrite ge //.
have : g i \in x `|` y by rewrite in_setE; apply/gX; by exists i.
rewrite in_setU => /orP[|].
  by rewrite (negbTE giy) andbT.
by rewrite (negbTE giy).
Qed.

Definition e_restrict_codom' n (g : 'I_n -> dist A) (x y : set (dist A)) (e : {dist 'I_n})
  (ge : forall i : 'I_n, (g i \in x) && (g i \notin y) -> e i = 0%R) (gX : g @` setT `<=` x `|` y) :=
  locked (makeDist
  (e_restrict_codom_pmf0 g y e) (e_restrict_codom_pmf1' ge gX)).

Lemma e_restrict_codomE' n (g : 'I_n -> dist A) (x y : set (dist A)) (e : {dist 'I_n})
  (ge : forall i : 'I_n, (g i \in x) && (g i \notin y) -> e i = 0%R) (gX : g @` setT `<=` x `|` y) i :
  e_restrict_codom' ge gX i = if g i \in y then e i else 0%R.
Proof. by rewrite /e_restrict_codom'; unlock. Qed.

Lemma hull_setU (a : dist A) (x y : convset) : x !=set0 -> y !=set0 -> a \in hull (x `|` y) ->
  exists a1, a1 \in x /\ exists a2, a2 \in y /\ exists p : prob, a = ConvexDist.d a1 a2 (Prob.Op1 p).
Proof.
move=> x0 y0.
rewrite in_setE.
case=> n -[g [e [gX Ha]]].
case: x0 => dx dx_x.
case: y0 => dy dy_y.
set gx := fun i : 'I_n => if g i \in x then g i else dx.
set gy := fun i : 'I_n => if g i \in y then g i else dy.
pose norm_pmf_e1 := \rsum_(i < n | g i \in x) e i.
have norm_pmf_e1_ge0 : (0 <= norm_pmf_e1)%R.
  rewrite /norm_pmf_e1; apply: rsumr_ge0 => i _; exact/dist_ge0.
case/boolP : (norm_pmf_e1 == 0%R) => [norm_pmf_e1_eq0|norm_pmf_e1_neq0].
  have ge (i : 'I_n) : g i \in x -> e i = 0%R.
    move=> gix.
    move/eqP/prsumr_eq0P : norm_pmf_e1_eq0; apply => //= j _.
    exact/dist_ge0.
  exists dx; split; first by rewrite in_setE.
  exists (FamilyDist.d gy (e_restrict_codom ge gX)); split.
    move: (Hcset y); rewrite convexP /convex_n => /asboolP; apply => d.
    rewrite -in_setE => /imsetP[i _ ->{d}].
    rewrite /gy -in_setE; case: ifPn => //; by rewrite in_setE.
  exists (`Pr 0).
  rewrite Ha ConvexDist.d0; apply/dist_ext => a0.
  rewrite 2!FamilyDist.dE; apply eq_bigr => i _.
  rewrite /gy e_restrict_codomE; case: ifPn => // giy.
  have : g i \in x `|` y by rewrite in_setE; apply/gX; by exists i.
  rewrite in_setU (negbTE giy) orbF => /ge ->; by rewrite !mul0R.
have {norm_pmf_e1_neq0}norm_pmf_e1_gt0 : (0 < norm_pmf_e1)%R.
  rewrite ltR_neqAle; split => //; by apply/eqP; by rewrite eq_sym.
set pmf_e1 := fun i : 'I_n => ((if g i \in x then e i else 0) / norm_pmf_e1)%R.
have pmf_e10 : forall i : 'I_n, (0 <= pmf_e1 i)%R.
  move=> i; rewrite /pmf_e1; apply/divR_ge0 => //.
  case: ifPn => _; [exact/dist_ge0|exact/leRR].
have pmf_e11 : \rsum_(i < n) pmf_e1 i = 1%R.
  rewrite /pmf_e1 -big_distrl /= -/norm_pmf_e1 eqR_divr_mulr ?mul1R; last first.
    exact/eqP/gtR_eqF.
  by rewrite /norm_pmf_e1 [in RHS]big_mkcond.
set e1 := makeDist pmf_e10 pmf_e11.
pose norm_pmf_e2 := \rsum_(i < n | (g i \in y) && (g i \notin x)) e i.
have norm_pmf_e2_ge0 : (0 <= norm_pmf_e2)%R.
  rewrite /norm_pmf_e2; apply: rsumr_ge0 => i _; exact/dist_ge0.
case/boolP : (norm_pmf_e2 == 0%R) => [norm_pmf_e2_eq0|norm_pmf_e2_neq0].
  have ge (i : 'I_n) : (g i \in y) && (g i \notin x) -> e i = 0%R.
    move=> gix.
    move/eqP/prsumr_eq0P : norm_pmf_e2_eq0; apply => /=.
      move=> ? _; exact/dist_ge0.
    done.
  rewrite setUC in gX.
  exists (FamilyDist.d gx (e_restrict_codom' ge gX)); split.
    move: (Hcset x); rewrite convexP /convex_n => /asboolP; apply => d.
    rewrite -in_setE => /imsetP[i _ ->{d}].
    rewrite /gx -in_setE; case: ifPn => //; by rewrite in_setE.
  exists dy; split; first by rewrite in_setE.
  exists (`Pr 1).
  rewrite Ha ConvexDist.d1; apply/dist_ext => a0.
  rewrite 2!FamilyDist.dE; apply eq_bigr => i _.
  rewrite /gx e_restrict_codomE'; case: ifPn => // gix.
  have : g i \in y `|` x by rewrite in_setE; apply/gX; by exists i.
  rewrite in_setU (negbTE gix) orbF => giy.
  by rewrite ge ?mul0R // giy.
have {norm_pmf_e2_neq0}norm_pmf_e2_gt0 : (0 < norm_pmf_e2)%R.
  rewrite ltR_neqAle; split => //; by apply/eqP; by rewrite eq_sym.
set pmf_e2 := fun i : 'I_n => ((if (g i \in y) && (g i \notin x) then e i else 0) / norm_pmf_e2)%R.
have pmf_e20 : forall i : 'I_n, (0 <= pmf_e2 i)%R.
  move=> i.
  rewrite /pmf_e2.
  apply divR_ge0 => //.
  case: ifPn => _; [exact/dist_ge0|exact/leRR].
have pmf_e21 : \rsum_(i < n) pmf_e2 i = 1%R.
  rewrite /pmf_e2 -big_distrl /= -/norm_pmf_e2 eqR_divr_mulr ?mul1R; last first.
    exact/eqP/gtR_eqF.
  by rewrite /norm_pmf_e2 [in RHS]big_mkcond /=.
set e2 := makeDist pmf_e20 pmf_e21.
exists (FamilyDist.d gx e1); split.
  move: (Hcset x).
  rewrite convexP /convex_n => /asboolP; apply.
  move=> d.
  rewrite -in_setE.
  case/imsetP => i _ ->{d}.
  rewrite /gx -in_setE.
  case: ifPn => //; by rewrite in_setE.
exists (FamilyDist.d gy e2); split.
  move: (Hcset y).
  rewrite convexP /convex_n => /asboolP; apply.
  move=> d.
  rewrite -in_setE.
  case/imsetP => i _ ->{d}.
  rewrite /gy -in_setE.
  case: ifPn => //; by rewrite in_setE.
set p := norm_pmf_e1.
have p01 : (0 <= norm_pmf_e1 <= 1)%R.
  split => //.
  rewrite -(pmf1 e) /=.
  apply: ler_rsum_l => //= i _; [exact/leRR|exact/dist_ge0].
exists (Prob.mk p01) => /=.
rewrite Ha.
apply/dist_ext => a0.
rewrite FamilyDist.dE ConvexDist.dE.
rewrite (bigID [pred i | (g i \in y) && (g i \notin x)]) /= addRC.
congr (_ + _)%R.
- rewrite FamilyDist.dE big_distrr /= big_mkcond /=; apply eq_bigr => i _.
  rewrite negb_and negbK /pmf_e1.
  rewrite mulRCA -mulRA (mulRA (/ _)%R) mulVR ?mul1R; last exact/eqP/gtR_eqF.
  rewrite /gx.
  case: ifPn.
    case/orP.
      move=> giy.
      have : g i \in x `|` y by rewrite in_setE; apply/gX; by exists i.
      by rewrite in_setU (negbTE giy) orbF => ->.
    by move=> -> //.
  rewrite negb_or negbK => /andP[H1 H2].
  by rewrite (negbTE H2) mul0R.
- rewrite FamilyDist.dE big_distrr /= big_mkcond /=; apply eq_bigr => i _.
  have -> : norm_pmf_e1.~ = norm_pmf_e2.
    apply/eqP.
    rewrite /onem.
    rewrite subR_eq.
    rewrite /norm_pmf_e2 /norm_pmf_e1.
    rewrite [in X in (_ == X + _)%R]big_mkcond /=.
    rewrite [in X in (_ == _ + X)%R]big_mkcond /=.
    rewrite -big_split.
    rewrite -(pmf1 e) /=.
    apply/eqP/eq_bigr => j _.
    case: ifPn.
      case/andP => gjy gjx.
      by rewrite (negbTE gjx) addR0.
    rewrite negb_and => /orP[gjy|].
      have : g j \in x `|` y by rewrite in_setE; apply/gX; by exists j.
      rewrite in_setU (negbTE gjy) orbF => ->; by rewrite add0R.
    rewrite negbK => ->; by rewrite add0R.
  rewrite /pmf_e2.
  rewrite mulRCA -mulRA (mulRA (/ _)%R) mulVR ?mul1R; last exact/eqP/gtR_eqF.
  rewrite /gy.
  case: ifPn.
    by case/andP => ->.
  rewrite negb_and => /orP[_|].
    by rewrite mul0R.
  rewrite negbK => gix.
  by rewrite mul0R.
Qed.

End convex_distributions.

Section model.
Local Open Scope proba_scope.
Local Open Scope classical_set_scope.
Variable A : finType.

Definition P (X : set (dist A)) :=
  [set Y : set (dist A) | (Y `<=` X) /\ (Y !=set0) /\ convex Y].

Definition pchoice' (p : prob) (X Y : convset A) : set (dist A) :=
  [set d | exists x, x \in X /\ exists y, y \in Y /\ d = ConvexDist.d x y (Prob.Op1 p)].

Lemma pchoice'_self (p : prob) (X : convset A) :
  [set d | exists x, x \in car X /\ d = ConvexDist.d x x (Prob.Op1 p)] `<=` pchoice' p X X.
Proof.
move=> d [x [xX ->{d}]]; rewrite /pchoice'.
exists x; split => //; by exists x; split.
Qed.

Lemma Hpchoice (p : prob) (X Y : convset A) : convex (pchoice' p X Y).
Proof.
apply/asboolP => x y q /=; rewrite in_setE => -[d [dX [d' [d'Y ->]]]].
rewrite in_setE => -[e [eX [e' [e'Y ->]]]]; rewrite in_setE ConvexDist.commute.
exists (ConvexDist.d d e (Prob.Op1 q)); split; first exact: (asboolW (Hcset X)).
exists (ConvexDist.d d' e' (Prob.Op1 q)); split => //; exact: (asboolW (Hcset Y)).
Qed.

Definition pchoice (p : prob) (X Y : convset A) : convset A := mkCset (@Hpchoice p X Y).

Local Notation "mx <.| p |.> my" := (@pchoice p mx my).

Lemma pchoice_convset0 x p : x <.|p|.> convset0 A = convset0 A.
Proof.
apply val_inj => /=; rewrite /pchoice'.
rewrite predeqE => d; split => // -[d1 [d1x [d2 []]]]; by rewrite in_setE.
Qed.

Lemma convset0_pchoice x p : convset0 A <.|p|.> x = convset0 A.
Proof.
apply val_inj => /=; rewrite /pchoice'.
rewrite predeqE => d; split => // -[d1 []]; by rewrite in_setE.
Qed.

Lemma pchoice0 (a b : convset A) : a !=set0 -> a <.| `Pr 0 |.> b = b.
Proof.
move=> a0; apply/val_inj=> /=; rewrite /pchoice' predeqE => d; split.
- move=> [x [xa]] [y [yb ->{d}]]; by rewrite -in_setE ConvexDist.d0.
- move=> bd; case: a0 => d' ad'; exists d'; split; first by rewrite in_setE.
  exists d; split; by [rewrite in_setE | rewrite ConvexDist.d0].
Qed.

Lemma pchoice1 (a b : convset A) : b !=set0 -> a <.| `Pr 1 |.> b = a.
Proof.
move=> b0; apply/val_inj => /=; rewrite /pchoice' predeqE => d; split.
- move=> [x [xa]] [y [yb ->{d}]]; by rewrite -in_setE ConvexDist.d1.
- move=> ad; case: b0 => d' bd'; exists d; split; first by rewrite in_setE.
  exists d'; split; by [rewrite in_setE | rewrite ConvexDist.d1].
Qed.

Lemma pchoiceC p (x y : convset A) : x <.| p |.> y = y <.| `Pr p.~ |.> x.
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

Lemma pchoiceA (p q r s : prob) (x y z : convset A) :
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

Lemma Hndchoice (X Y : convset A) : convex (ndchoice' X Y).
Proof.
apply/asboolP => x y p.
rewrite /ndchoice' => Hx Hy.
have := convex_hull (X `|` Y).
by move/asboolP => /(_ x y p Hx Hy).
Qed.

Definition ndchoice (X Y : convset A) : convset A := mkCset (@Hndchoice X Y).

Lemma ndchoice0X (X : convset A) : ndchoice (convset0 A) X = X.
Proof. by apply val_inj => /=; rewrite /ndchoice' set0U hull_convset. Qed.

Lemma ndchoiceX0 (X : convset A) : ndchoice X (convset0 A) = X.
Proof. by apply val_inj => /=; rewrite /ndchoice' setU0 hull_convset. Qed.

Lemma ndchoiceC : commutative ndchoice.
Proof. move=> x y; apply/val_inj => /=; by rewrite /ndchoice' setUC. Qed.

Lemma ndchoicemm : idempotent ndchoice.
Proof.
move=> d; apply/val_inj => /=.
rewrite /ndchoice' setUid; exact: hull_convset.
Qed.

Lemma ndchoiceA : associative ndchoice.
Proof.
move=> x y z; apply/val_inj => /=; rewrite /ndchoice'; apply eqEsubset.
- move=> a; rewrite -in_setE => Ha; rewrite -in_setE.
  case/boolP : (x == convset0 A) => [|/convset0PN H1].
    rewrite convset0P => /eqP x0.
    by move: Ha; rewrite {}x0 2!set0U hullI /= hull_convset.
  set yz := mkCset (convex_hull (y `|` z)).
  case/boolP : (yz == convset0 A) => [|/convset0PN H2].
    rewrite convset0P hull_eq0 => /eqP; rewrite setU_eq0 => -[y0 z0].
    by move: Ha; rewrite y0 z0 2!setU0 hullI hull0 setU0.
  case: (hull_setU H1 H2 Ha) => d1 [d1x [d [dyz [p Hp]]]]; rewrite Hp.
  case/boolP : (y == convset0 A) => [|/convset0PN H3].
    rewrite convset0P => /eqP y0.
    by move: Ha; rewrite y0 set0U setU0 2!hull_convset -Hp.
  case/boolP : (z == convset0 A) => [|/convset0PN H4].
    rewrite convset0P => /eqP z0.
    by move: Ha; rewrite z0 2!setU0 hullI hull_convset -Hp.
  case: (hull_setU H3 H4 dyz) => d2 [d2y [d3 [d3z [q Hq]]]]; rewrite Hq.
  set s := s_of_pq p q.
  set r := r_of_pq p q.
  rewrite (@ConvexDist.quasi_assoc _ _ _ r s); last 2 first.
    exact: p_is_rs.
    exact: s_is_pq.
    by case: r.
    by case: s.
  move=> r01 s01.
  apply mem_hull_setU => //; exact/mem_hull_setU.
- move=> a; rewrite -in_setE => Ha; rewrite -in_setE.
  set xy := mkCset (convex_hull (x `|` y)).
  case/boolP : (xy == convset0 A) => [|/convset0PN H1].
    rewrite convset0P hull_eq0 => /eqP; rewrite setU_eq0 => -[x0 y0].
    by move: Ha; rewrite x0 y0 3!set0U hull0 set0U hullI.
  case/boolP : (z == convset0 A) => [|/convset0PN H2].
    rewrite convset0P => /eqP z0.
    by move: Ha; rewrite z0 2!setU0 hull_convset hullI.
  case: (hull_setU H1 H2 Ha) => d1 [d1xy [d [dz [p Hp]]]]; rewrite Hp.
  case/boolP : (x == convset0 A) => [|/convset0PN H3].
    rewrite convset0P => /eqP x0.
    by move: Ha; rewrite x0 2!set0U hullI hull_convset -Hp.
  case/boolP : (y == convset0 A) => [|/convset0PN H4].
    rewrite convset0P => /eqP y0.
    by move: Ha; rewrite y0 set0U setU0 2!hull_convset -Hp.
  case: (hull_setU H3 H4 d1xy) => d2 [d2y [d3 [d3z [q Hq]]]]; rewrite Hq.
  set s := s_of_pq (`Pr p.~) (`Pr q.~).
  set r := r_of_pq (`Pr p.~) (`Pr q.~).
  rewrite -(@ConvexDist.quasi_assoc _ s.~ r.~); last 2 first.
    by rewrite s_is_pq 2!onemK mulRC.
    rewrite 2!onemK (p_is_rs (`Pr p.~) (`Pr q.~)).
    by rewrite -/s -/r mulRC.
    apply: onem_prob; by case: r.
    apply: onem_prob; by case: s.
  move=> r01 s01.
  apply mem_hull_setU => //; exact/mem_hull_setU.
Qed.

Lemma ndchoiceDr p :
  right_distributive (fun x y : convset A => x <.| p |.> y) (fun x y => ndchoice x y).
Proof.
move=> x y z.
case/boolP : (y == @convset0 A) => [/eqP|/convset0PN] y0.
  by rewrite {}y0 ndchoice0X pchoice_convset0 ndchoice0X.
case/boolP : (z == @convset0 A) => [/eqP|/convset0PN] z0.
  by rewrite {}z0 ndchoiceX0 pchoice_convset0 ndchoiceX0.
case/boolP : (x == @convset0 A) => [/eqP|/convset0PN] x0.
  by rewrite {}x0 !convset0_pchoice ndchoice0X.
have /convset0PN xy0 : (pchoice p x y != @convset0 A).
  case: y0 => b; rewrite -in_setE => yb.
  case: x0 => a; rewrite -in_setE => xa.
  apply/convset0PN.
  exists (ConvexDist.d a b (Prob.O1 p)).
  rewrite /= /pchoice'.
  exists a; split => //; by exists b; split.
have /convset0PN xz0 : (pchoice p x z != @convset0 A).
  case: z0 => c; rewrite -in_setE => zc.
  case: x0 => a; rewrite -in_setE => xa.
  apply/convset0PN.
  exists (ConvexDist.d a c (Prob.O1 p)).
  rewrite /= /pchoice'.
  exists a; split => //.
  by exists c; split.
apply/val_inj => /=; apply eqEsubset.
- move=> a [b [bx [c [xyz ->{a}]]]].
  case: (hull_setU y0 z0 xyz) => c1 [c1y [c2 [c2z [q cq]]]].
  rewrite cq ConvexDist.distribute -in_setE; apply mem_hull_setU.
  rewrite in_setE; exists b; split => //.
  exists c1; split => //.
  rewrite in_setE; exists b; split => //.
  by exists c2; split => //.
- move=> a.
  rewrite /ndchoice' -in_setE.
  case/(hull_setU xy0 xz0) => b [bxy [c [cxz [q ->{a}]]]].
  rewrite /ndchoice /pchoice' /ndchoice' /=.
  move: bxy; rewrite in_setE /pchoice /= /pchoice' => -[a' [xa' [b' [b'y] Hb']]].
  move: cxz; rewrite in_setE /pchoice /= /pchoice' => -[a'' [xa'' [b'' [b''y] Hb'']]].
  exists (ConvexDist.d a' a'' (Prob.Op1 q)); split.
    rewrite in_setE.
    rewrite -(hull_convset x).
    rewrite -in_setE.
    rewrite -(setUid x).
    by apply mem_hull_setU.
  exists (ConvexDist.d b' b'' (Prob.Op1 q)); split.
    by apply mem_hull_setU.
  by rewrite Hb' Hb'' ConvexDist.commute.
Qed.

End model.
