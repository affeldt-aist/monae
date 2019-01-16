Require Import FunctionalExtensionality Coq.Program.Tactics ProofIrrelevance.
Require Classical.
Require Import ssreflect ssrmatching ssrfun ssrbool.
From mathcomp Require Import eqtype ssrnat seq choice fintype tuple.
From mathcomp Require Import finfun finset bigop.
From mathcomp Require Import boolp classical_sets.

Require Import monad monad_composition monad_model.

Require Import Reals Lra.
From infotheo Require Import ssrR Reals_ext Rbigop proba convex.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* wip *)

Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.

Lemma dist_supp1 (d : {dist 'I_1}) : dist_supp d = ([set ord0])%SET.
Proof.
case: d => -[/= f f0] f1; apply/setP => i.
rewrite (ssr_ext.ord1 i) /= !inE /= eqxx.
move: f1; rewrite big_ord_recl big_ord0 addR0 => ->; exact/eqP.
Qed.

Local Open Scope classical_set_scope.

Lemma ConvDist_proj (A : finType) n (g : 'I_n -> dist A) (d : {dist 'I_n})
  (i : 'I_n) (d1 : d i == 1%R) :
  ConvDist.d g d = g i.
Proof.
apply/dist_ext => a.
rewrite ConvDist.dE (bigD1 i) //= (eqP d1) mul1R big1 ?addR0 // => j ij.
rewrite (_ : d _ = 0%R) ?mul0R //; apply/eqP.
move/eqP : d1 => /dist_supp_singleP/eqP/setP/(_ j).
by rewrite !inE => /(congr1 negb); rewrite negbK /= ij.
Qed.

Lemma ConvDist_proj1 (A : finType) (g : 'I_1 -> dist A) (d : {dist 'I_1}) :
  ConvDist.d g d = g ord0.
Proof.
rewrite (@ConvDist_proj _ _ _ _ ord0) //.
apply/eqP/dist_supp_singleP; by rewrite dist_supp1.
Qed.

Local Open Scope convex_scope.

Lemma Conv2DistE (A : finType) (g : 'I_2 -> dist A) (d : {dist 'I_2}) H :
  ConvDist.d g d = g ord0 <| (@Prob.mk (d ord0) H) |> g (lift ord0 ord0).
Proof.
apply/dist_ext => a.
rewrite ConvDist.dE /= 2!big_ord_recl /= big_ord0 addR0.
rewrite Conv2Dist.dE.
congr (_ + _ * _)%R.
move: (pmf1 d); rewrite 2!big_ord_recl big_ord0 addR0 => /eqP.
by rewrite eq_sym addRC -subR_eq => /eqP <-.
Qed.

Module ShrinkDist.
Local Open Scope proba_scope.
Section def.
Variables (n : nat) (P : {dist 'I_n.+1}) (j : 'I_n.+1) (Pj_neq1 : P j != 1%R).
Let D : {dist 'I_n.+1} := D1Dist.d Pj_neq1.
Definition f (i : 'I_n) := if i < j then D (widen_ord (leqnSn _) i) else D (lift ord0 i).
Lemma f0 i : (0 <= f i)%R.
Proof. rewrite /f; case: ifPn => _; exact/dist_ge0. Qed.
Lemma f1 : \rsum_(i < n) f i = 1%R.
Proof.
rewrite -(pmf1 D) /= (bigID (fun i : 'I_n.+1 => i < j)) /=.
rewrite (bigID (fun i : 'I_n => i < j)) /=; congr (_ + _)%R.
  rewrite (@big_ord_narrow_cond _ _ _ j n.+1 xpredT); first by rewrite ltnW.
  move=> jn; rewrite (@big_ord_narrow_cond _ _ _ j n xpredT); first by rewrite -ltnS.
  move=> jn'; apply eq_bigr => i _.
  rewrite /f /= ltn_ord.
  f_equal; exact/val_inj.
rewrite (bigID (pred1 j)) /= [X in _ = (X + _)%R](_ : _ = 0%R) ?add0R; last first.
  rewrite (big_pred1 j).
  by rewrite /D D1Dist.dE eqxx.
  by move=> /= i; rewrite -leqNgt andbC andb_idr // => /eqP ->.
rewrite [in RHS]big_mkcond big_ord_recl.
set X := (X in _ = addR_monoid _ X).
rewrite /= -leqNgt leqn0 eq_sym andbN add0R.
rewrite big_mkcond; apply eq_bigr => i _.
rewrite -2!leqNgt andbC eq_sym -ltn_neqAle ltnS.
case: ifPn => // ji; by rewrite /f ltnNge ji.
Qed.
Definition d : {dist 'I_n} := locked (makeDist f0 f1).
Lemma dE i : d i = if i < j then D (widen_ord (leqnSn _) i) else D (lift ord0 i).
Proof. by rewrite /d; unlock. Qed.
End def.
End ShrinkDist.

Module BelastDist.
Local Open Scope proba_scope.
Section def.
Variables (n : nat) (P : {dist 'I_n.+1}) (Pmax_neq1 : P ord_max != 1%R).
Let D : {dist 'I_n.+1} := D1Dist.d Pmax_neq1.
Definition d : {dist 'I_n} := locked (ShrinkDist.d Pmax_neq1).
Lemma dE i : d i = D (widen_ord (leqnSn _) i).
Proof. by rewrite /d; unlock; rewrite ShrinkDist.dE /= ltn_ord. Qed.
End def.
Section prop.
Variables (A : finType) (n : nat) (g : 'I_n.+1 -> dist A) (P : {dist 'I_n.+1}).
Lemma Convex (H : (0 <= (P ord_max).~ <= 1)%R) (Pmax_neq1 : P ord_max != 1%R) :
  let g' := fun i : 'I_n => g (widen_ord (leqnSn _) i) in
  ConvDist.d g P = ConvDist.d g' (d Pmax_neq1) <| Prob.mk H |> g ord_max.
Proof.
move=> g' /=; apply/dist_ext => a.
rewrite Conv2Dist.dE 2!ConvDist.dE big_ord_recr /= onemK; congr (_ + _)%R.
rewrite big_distrr /=; apply eq_bigr => i _.
rewrite dE D1Dist.dE /= ifF; last first.
  by apply/negP => /eqP/(congr1 val)/=; apply/eqP; rewrite ltn_eqF.
rewrite mulRCA /Rdiv -mulRA; congr (_ * _)%R.
by rewrite mulRA mulVR ?mul1R // subR_eq0 eq_sym.
Qed.
End prop.
End BelastDist.

Module CatDist.
Section catdist.
Local Open Scope proba_scope.
Variables (n m : nat) (d1 : {dist 'I_n}) (d2 : {dist 'I_m}) (p : R) (Hp : (0 <= p <= 1)%R).
Definition f (i : 'I_(n + m)) :=
  match fintype.split i with inl a => (p * d1 a)%R | inr a => (p.~ * d2 a)%R end.
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
Variables (n m : nat) (d1 : {dist 'I_n}) (d2 : {dist 'I_m}) (*(p : R) (Hp : (0 <= p <= 1)%R)*) (p : prob).
Lemma Convex (A : finType) (g : 'I_n -> dist A) (h : 'I_m -> dist A) :
  ConvDist.d
    [ffun i => match fintype.split i with inl a => g a | inr a => h a end]
    (d d1 d2 (Prob.Op1 p)) =
  ConvDist.d g d1 <| p |> ConvDist.d h d2.
Proof.
apply/dist_ext => a.
rewrite !Conv2Dist.dE !ConvDist.dE.
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

Module CodomDDist.
Section def.
Local Open Scope classical_set_scope.
Local Open Scope proba_scope.
Variables (A : finType) (n : nat) (g : 'I_n -> dist A) (e : {dist 'I_n}) (y : set (dist A)).

Definition f : 'I_n -> R := fun i => if g i \in y then e i else 0%R.

Lemma f0 i : (0 <= f i)%R.
Proof. rewrite /f; case: ifPn => _; [exact/dist_ge0|exact/leRR]. Qed.

Lemma f1 (x : set (dist A)) (gX : g @` setT `<=` x `|` y)
  (ge : forall i : 'I_n, g i \in x -> e i = 0%R) :
  (\rsum_(i < n) f i = 1)%R.
Proof.
rewrite /f -(pmf1 e) /=.
apply eq_bigr => i _.
case: ifPn => // giy.
rewrite ge //.
have : g i \in x `|` y by rewrite in_setE; apply/gX; by exists i.
rewrite in_setU => /orP[|] //.
by rewrite (negbTE giy).
Qed.

Definition d (x : set (dist A)) (gX : g @` setT `<=` x `|` y)
  (ge : forall i : 'I_n, g i \in x -> e i = 0%R) : {dist 'I_n} :=
  locked (makeDist f0 (f1 gX ge)).

Lemma dE (x : set (dist A)) (gX : g @` setT `<=` x `|` y)
  (ge : forall i : 'I_n, g i \in x -> e i = 0%R) i :
  d gX ge i = if g i \in y then e i else 0%R.
Proof. by rewrite /d; unlock. Qed.

Lemma f1' (x : set (dist A)) (gX : g @` setT `<=` x `|` y)
  (ge : forall i : 'I_n, (g i \in x) && (g i \notin y) -> e i = 0%R) :
  (\rsum_(i < n) f i = 1)%R.
Proof.
rewrite /f -(pmf1 e) /=.
apply eq_bigr => i _.
case: ifPn => // giy.
rewrite ge //.
have : g i \in x `|` y by rewrite in_setE; apply/gX; by exists i.
rewrite in_setU => /orP[|].
  by rewrite (negbTE giy) andbT.
by rewrite (negbTE giy).
Qed.

Definition d' (x : set (dist A)) (gX : g @` setT `<=` x `|` y)
  (ge : forall i : 'I_n, (g i \in x) && (g i \notin y) -> e i = 0%R) :=
  locked (makeDist f0 (f1' gX ge)).

Lemma dE' (x : set (dist A)) (gX : g @` setT `<=` x `|` y)
  (ge : forall i : 'I_n, (g i \in x) && (g i \notin y) -> e i = 0%R) i :
  d' gX ge i = if g i \in y then e i else 0%R.
Proof. by rewrite /d'; unlock. Qed.

End def.
End CodomDDist.

Local Open Scope proba_scope.

Section convex_set_of_distributions_def.
Variable A : finType.
Definition convex (X : set (dist A)) : bool :=
  `[< forall x y p, x \in X -> y \in X -> x <| p |> y \in X >].
End convex_set_of_distributions_def.

Section convex_set_of_distributions_prop.
Local Open Scope classical_set_scope.
Local Open Scope proba_scope.
Variable A : finType.

Lemma convex0 : convex (@set0 (dist A)).
Proof. apply/asboolP => x y p; by rewrite in_setE. Qed.

Lemma convexT : convex (@setT (dist A)).
Proof. apply/asboolP => ? ? ? _ _; by rewrite in_setE. Qed.

Definition convex_n (X : set (dist A)) : bool :=
  `[< forall n (g : 'I_n -> dist A) (d : {dist 'I_n}),
      g @` setT `<=` X -> ConvDist.d g d \in X >].

Lemma convexP (X : set (dist A)) : convex X = convex_n X.
Proof.
apply/idP/idP => H; apply/asboolP; last first.
  move=> x y p xX yX.
  pose g : 'I_2 -> dist A := [eta (fun=>x) with ord0 |-> x, 1 |-> y].
  have -> : x <| p |> y = ConvDist.d g (Dist2.d (Prob.Op1 p)).
    rewrite Conv2DistE.
    - split; [exact/dist_ge0|exact/dist_max].
    - rewrite Dist2.dE /= => H'; congr Conv2Dist.d.
      destruct p => /=.
      by rewrite (ProofIrrelevance.proof_irrelevance _ Op1 H').
  move/asboolP : H; apply => d -[i _ <-{d}].
  rewrite /g /=; case: ifP => _; first by rewrite -in_setE.
  case: ifP => _; by rewrite -in_setE.
elim => [g d|n IH g d].
  by move: (dist_domain_not_empty d); rewrite card_ord ltnn.
destruct n as [|n] => gX.
  rewrite {IH} ConvDist_proj1 in_setE; exact/gX/classical_sets.imageP.
case/boolP : (d ord_max == 1%R) => dmax1.
  suff -> : ConvDist.d g d = g ord_max by rewrite in_setE; apply gX; exists ord_max.
  exact/ConvDist_proj.
set D : {dist 'I_n.+1} := BelastDist.d dmax1.
pose G : 'I_n.+1 -> dist A := fun i => g (widen_ord (leqnSn _) i).
have : G @` classical_sets.setT `<=` X.
  move=> x -[i _ <-{x}]; by apply gX; exists (widen_ord (leqnSn _) i).
move/(IH _ D) => {IH}IH.
have dmax01 : (0 <= (d ord_max).~ <= 1)%R.
  split; [exact/onem_ge0/dist_max|exact/onem_le1/dist_ge0].
have -> : ConvDist.d g d = ConvDist.d G D <| Prob.mk dmax01 |> g ord_max.
  by rewrite BelastDist.Convex.
move/asboolP : H; apply => //.
rewrite in_setE; apply gX.
exists (lift ord0 ord_max) => //=; congr g; exact/val_inj.
Qed.

Definition hull (X : set (dist A)) : set (dist A) :=
  [set d | exists n, exists g : 'I_n -> dist A, exists e : {dist 'I_n},
    g @` classical_sets.setT `<=` X /\ d = ConvDist.d g e].

Lemma hull_mem (X : set (dist A)) x : x \in X -> x \in hull X.
Proof.
move=> xX.
rewrite in_setE /hull.
exists 1, (fun i : 'I_1 => x), (Dist1.d ord0); split.
  move=> d -[i _ <-]; by rewrite -in_setE.
apply/dist_ext => a.
by rewrite ConvDist.dE big_ord_recl big_ord0 addR0 Dist1.dE eqxx mul1R.
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

Lemma convex_hull (X : set (dist A)) : convex (hull X).
Proof.
apply/asboolP => x y p; rewrite 2!in_setE.
move=> -[n [g [d [gX ->{x}]]]].
move=> -[m [h [e [hX ->{y}]]]].
rewrite in_setE.
exists (n + m).
exists [ffun i => match fintype.split i with inl a => g a | inr a => h a end].
exists (CatDist.d d e (Prob.Op1 p)).
rewrite CatDist.Convex; split => //.
move=> a -[i _].
rewrite ffunE.
case: splitP => j _ <-; by [apply gX; exists j | apply hX; exists j].
Qed.

Lemma mem_hull_setU (x y : set (dist A)) (a0 a1 : dist A) p :
  a0 \in x -> a1 \in y -> a0 <| p |> a1 \in hull (x `|` y).
Proof.
move=> a0x a1y.
rewrite in_setE.
exists 2, [eta (fun=> a0) with ord0 |-> a0, lift ord0 ord0 |-> a1], (Dist2.d (Prob.Op1 p)); split => /=.
  move=> a2.
  rewrite -in_setE.
  case/imsetP => i _ ->{a2} /=.
  case: ifPn => _.
  by rewrite -in_setE in_setU a0x.
  case: ifPn => _; rewrite -in_setE in_setU.
  apply/orP; by right.
  apply/orP; by left.
apply/dist_ext => a2.
by rewrite Conv2Dist.dE ConvDist.dE 2!big_ord_recl big_ord0 addR0 /= 2!Dist2.dE.
Qed.

Lemma mem_hull_setU_left (x y : set (dist A)) (a : dist A) : a \in x -> a \in hull (x `|` y).
Proof. by move=> ax; apply: hull_mem; rewrite in_setU ax. Qed.

Lemma hullI (X : set (dist A)) : hull (hull X) = hull X.
Proof.
rewrite predeqE => d; split.
- move=> -[n [g [e [gX ->{d}]]]].
  move: (convex_hull X); rewrite convexP /convex_n => /asboolP/(_ _ g e gX).
  by rewrite in_setE.
- by rewrite -in_setE => /hull_mem; rewrite in_setE.
Qed.

End convex_set_of_distributions_prop.

Module CSet.
Section def.
Local Open Scope classical_set_scope.
Local Open Scope proba_scope.
Variable A : finType.
Record t : Type := mk {
  car :> set (dist A) ;
  H : convex car }.
End def.
End CSet.
Notation cset := CSet.t.
Coercion CSet.car : cset >-> set.

Section cset_canonical.
Variable (A : finType).
Canonical cset_subType := [subType for @CSet.car A].
Canonical cset_predType :=
  Eval hnf in mkPredType (fun t : cset A => (fun x => x \in CSet.car t)).
Definition cset_eqMixin := Eval hnf in [eqMixin of cset A by <:].
Canonical cset_eqType := Eval hnf in EqType (cset A) cset_eqMixin.
End cset_canonical.

Section CSet_prop.
Local Open Scope classical_set_scope.
Local Open Scope proba_scope.
Variable A : finType.

Definition cset0 : cset A := CSet.mk (convex0 A).

Lemma cset0P (x : cset A) : (x == cset0) = (x == set0 :> set _).
Proof. by case: x. Qed.

Lemma cset0PN (x : cset A) : (x != cset0) <-> (x !=set0).
Proof.
rewrite cset0P; case: x => //= x Hx; split; last first.
  case=> a xa; apply/eqP => x0; move: xa; by rewrite x0.
by case/set0P => /= d dx; exists d.
Qed.

Lemma hull_cset (x : cset A) : hull x = x.
Proof.
rewrite predeqE => d; split.
- move=> -[n [g [e [gX ->{d}]]]].
  move: (CSet.H x);   rewrite convexP /convex_n => /asboolP/(_ _ g e gX).
  by rewrite in_setE.
- by rewrite -in_setE => /hull_mem; rewrite in_setE.
Qed.

Lemma hull_setU (a : dist A) (x y : cset A) : x !=set0 -> y !=set0 -> a \in hull (x `|` y) ->
  exists a1, a1 \in x /\ exists a2, a2 \in y /\ exists p : prob, a = a1 <| p |> a2.
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
  exists (ConvDist.d gy (CodomDDist.d gX ge)); split.
    move: (CSet.H y); rewrite convexP /convex_n => /asboolP; apply => d.
    rewrite -in_setE => /imsetP[i _ ->{d}].
    rewrite /gy -in_setE; case: ifPn => //; by rewrite in_setE.
  exists (`Pr 0).
  rewrite Ha conv0; apply/dist_ext => a0.
  rewrite 2!ConvDist.dE; apply eq_bigr => i _.
  rewrite /gy CodomDDist.dE; case: ifPn => // giy.
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
  exists (ConvDist.d gx (CodomDDist.d' gX ge)); split.
    move: (CSet.H x); rewrite convexP /convex_n => /asboolP; apply => d.
    rewrite -in_setE => /imsetP[i _ ->{d}].
    rewrite /gx -in_setE; case: ifPn => //; by rewrite in_setE.
  exists dy; split; first by rewrite in_setE.
  exists (`Pr 1).
  rewrite Ha conv1; apply/dist_ext => a0.
  rewrite 2!ConvDist.dE; apply eq_bigr => i _.
  rewrite /gx CodomDDist.dE'; case: ifPn => // gix.
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
exists (ConvDist.d gx e1); split.
  move: (CSet.H x).
  rewrite convexP /convex_n => /asboolP; apply.
  move=> d.
  rewrite -in_setE.
  case/imsetP => i _ ->{d}.
  rewrite /gx -in_setE.
  case: ifPn => //; by rewrite in_setE.
exists (ConvDist.d gy e2); split.
  move: (CSet.H y).
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
rewrite ConvDist.dE Conv2Dist.dE.
rewrite (bigID [pred i | (g i \in y) && (g i \notin x)]) /= addRC.
congr (_ + _)%R.
- rewrite ConvDist.dE big_distrr /= big_mkcond /=; apply eq_bigr => i _.
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
- rewrite ConvDist.dE big_distrr /= big_mkcond /=; apply eq_bigr => i _.
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

End CSet_prop.

Require proba_monad (*NB: for s_od_pq *).

Section probabilistic_choice_nondeterministic_choice.
Local Open Scope proba_scope.
Local Open Scope classical_set_scope.
Variable A : finType.

Definition pchoice' (p : prob) (X Y : cset A) : set (dist A) :=
  [set d | exists x, x \in X /\ exists y, y \in Y /\ d = x <| p |> y].

Lemma pchoice'_self (p : prob) (X : cset A) :
  [set d | exists x, x \in X /\ d = x <| p |> x] `<=` pchoice' p X X.
Proof.
move=> d [x [xX ->{d}]]; rewrite /pchoice'.
exists x; split => //; by exists x; split.
Qed.

Lemma Hpchoice (p : prob) (X Y : cset A) : convex (pchoice' p X Y).
Proof.
apply/asboolP => x y q /=; rewrite in_setE => -[d [dX [d' [d'Y ->]]]].
rewrite in_setE => -[e [eX [e' [e'Y ->]]]]; rewrite in_setE Conv2DistProp.commute.
exists (Conv2Dist.d d e q); split; first exact: (asboolW (CSet.H X)).
exists (Conv2Dist.d d' e' q); split => //; exact: (asboolW (CSet.H Y)).
Qed.

Definition pchoice (p : prob) (X Y : cset A) : cset A := CSet.mk (@Hpchoice p X Y).

Local Notation "mx <.| p |.> my" := (@pchoice p mx my).

Lemma pchoice_cset0 x p : x <.|p|.> cset0 A = cset0 A.
Proof.
apply val_inj => /=; rewrite /pchoice'.
rewrite predeqE => d; split => // -[d1 [d1x [d2 []]]]; by rewrite in_setE.
Qed.

Lemma cset0_pchoice x p : cset0 A <.|p|.> x = cset0 A.
Proof.
apply val_inj => /=; rewrite /pchoice'.
rewrite predeqE => d; split => // -[d1 []]; by rewrite in_setE.
Qed.

Lemma pchoice_eq0 p a b :
  a <.| p |.> b == cset0 A -> (a == cset0 A) || (b == cset0 A).
Proof.
case/boolP : (a == cset0 A) => //= /cset0PN[da Hda].
case/boolP : (b == cset0 A) => //= /cset0PN[db Hdb].
case/eqP; rewrite /pchoice' => H.
suff : set0 (da <| p |> db) by [].
rewrite -H; exists da; split; first by rewrite in_setE.
exists db; split => //; by rewrite in_setE.
Qed.

Lemma pchoice0 (a b : cset A) : a !=set0 -> a <.| `Pr 0 |.> b = b.
Proof.
move=> a0; apply/val_inj=> /=; rewrite /pchoice' predeqE => d; split.
- move=> [x [xa]] [y [yb ->{d}]]; by rewrite -in_setE conv0.
- move=> bd; case: a0 => d' ad'; exists d'; split; first by rewrite in_setE.
  exists d; split; by [rewrite in_setE | rewrite conv0].
Qed.

Lemma pchoice1 (a b : cset A) : b !=set0 -> a <.| `Pr 1 |.> b = a.
Proof.
move=> b0; apply/val_inj => /=; rewrite /pchoice' predeqE => d; split.
- move=> [x [xa]] [y [yb ->{d}]]; by rewrite -in_setE conv1.
- move=> ad; case: b0 => d' bd'; exists d; split; first by rewrite in_setE.
  exists d'; split; by [rewrite in_setE | rewrite conv1].
Qed.

Lemma pchoiceC p (x y : cset A) : x <.| p |.> y = y <.| `Pr p.~ |.> x.
Proof.
apply/val_inj/classical_sets.eqEsubset => /=; rewrite /pchoice'.
- move=> d [a [aX [b [bY ->{d}]]]].
  by exists b; split => //; exists a; split => //; rewrite convC.
- move=> d [a [aY [b [bX ->{d}]]]].
  exists b; split => //; exists a; split => //; rewrite convC.
  by apply/dist_ext => a0; rewrite !Conv2Dist.dE /= !onemK.
Qed.

Lemma pchoicemm p : idempotent (pchoice p).
Proof.
move=> Y; apply/val_inj/classical_sets.eqEsubset => /=.
- move=> d; rewrite /pchoice' => -[x [Hx [y [Hy ->{d}]]]].
  by rewrite -in_setE (asboolW (CSet.H Y)).
- apply: classical_sets.subset_trans; last exact: pchoice'_self.
  set Y' := (X in _ `<=` X). suff : Y = Y' :> set (dist A) by move=> <-. rewrite {}/Y'.
  transitivity [set y | y \in Y].
    rewrite predeqE => d; split; by rewrite in_setE.
  rewrite predeqE => d; split.
  - move=> dY; exists d; split => //; by rewrite convmm.
  - case=> d' [d'Y ->{d}]; by rewrite (asboolW (CSet.H Y)).
Qed.

Lemma nepchoiceA (p q r s : prob) (x y z : cset A) :
  (p = r * s :> R /\ s.~ = p.~ * q.~)%R ->
  x <.| p |.> (y <.| q |.> z) = (x <.| r |.> y) <.| s |.> z.
Proof.
move=> [H1 H2]; apply/val_inj/classical_sets.eqEsubset => /=.
- move=> d; rewrite /pchoice' => -[a [xa [b []]]].
  rewrite in_setE /= {1}/pchoice' => -[b1 [b1y [b2 [b2z ->{b} ->{d}]]]].
  exists (a <| r |> b1); split.
    rewrite in_setE /= /pchoice'; exists a; split => //; by exists b1.
  by exists b2; split => //; rewrite (@convA _ _ _ r s).
- move=> d; rewrite /pchoice' => -[a []].
  rewrite in_setE /= {1}/pchoice' => -[a1 [a1x [a2 [a2y ->{a}]]]] => -[b] [bz ->{d}].
  exists a1; split => //.
  exists (a2 <| q |> b); split.
    rewrite in_setE /= /pchoice'; exists a2; split => //; by exists b.
  by rewrite (@convA _ _ _ r s).
Qed.

Definition nchoice' (X Y : set (dist A)) : set (dist A) := hull (X `|` Y).

Lemma Hnchoice (X Y : cset A) : convex (nchoice' X Y).
Proof.
apply/asboolP => x y p; rewrite /nchoice' => Hx Hy.
have := convex_hull (X `|` Y).
by move/asboolP => /(_ x y p Hx Hy).
Qed.

Definition nchoice (X Y : cset A) : cset A := CSet.mk (@Hnchoice X Y).

Lemma nchoice0X (X : cset A) : nchoice (cset0 A) X = X.
Proof. by apply val_inj => /=; rewrite /nchoice' set0U hull_cset. Qed.

Lemma nchoiceX0 (X : cset A) : nchoice X (cset0 A) = X.
Proof. by apply val_inj => /=; rewrite /nchoice' setU0 hull_cset. Qed.

Lemma nchoice_eq0 a b :
  nchoice a b == cset0 A -> (a == cset0 A) || (b == cset0 A).
Proof.
case/boolP : (a == cset0 A) => // /cset0PN a0.
case/boolP : (b == cset0 A) => //= /cset0PN b0 H.
suff : hull (a `|` b) == set0.
  move/eqP : H => /(congr1 val) /= /eqP.
  rewrite /nchoice' hull_eq0 => /eqP; rewrite setU_eq0 => -[Ha _] _.
  by case: a0 => a0; rewrite Ha.
by move/eqP : H => /(congr1 val) /=; rewrite /nchoice /nchoice' => ->.
Qed.

Lemma nchoiceC : commutative nchoice.
Proof. move=> x y; apply/val_inj => /=; by rewrite /nchoice' setUC. Qed.

Lemma nchoicemm : idempotent nchoice.
Proof.
move=> d; apply/val_inj => /=; rewrite /nchoice' setUid; exact: hull_cset.
Qed.

Lemma nchoiceA : associative nchoice.
Proof.
move=> x y z; apply/val_inj => /=; rewrite /nchoice'; apply eqEsubset.
- move=> a; rewrite -in_setE => Ha; rewrite -in_setE.
  case/boolP : (x == cset0 A) => [|/cset0PN H1].
    rewrite cset0P => /eqP x0.
    by move: Ha; rewrite {}x0 2!set0U hullI /= hull_cset.
  set yz := CSet.mk (convex_hull (y `|` z)).
  case/boolP : (yz == cset0 A) => [|/cset0PN H2].
    rewrite cset0P hull_eq0 => /eqP; rewrite setU_eq0 => -[y0 z0].
    by move: Ha; rewrite y0 z0 2!setU0 hullI hull0 setU0.
  case: (hull_setU H1 H2 Ha) => d1 [d1x [d [dyz [p Hp]]]]; rewrite Hp.
  case/boolP : (y == cset0 A) => [|/cset0PN H3].
    rewrite cset0P => /eqP y0.
    by move: Ha; rewrite y0 set0U setU0 2!hull_cset -Hp.
  case/boolP : (z == cset0 A) => [|/cset0PN H4].
    rewrite cset0P => /eqP z0.
    by move: Ha; rewrite z0 2!setU0 hullI hull_cset -Hp.
  case: (hull_setU H3 H4 dyz) => d2 [d2y [d3 [d3z [q Hq]]]]; rewrite Hq.
  set s := proba_monad.s_of_pq p q.
  set r := proba_monad.r_of_pq p q.
  rewrite (@convA _ _ _ r s); last 2 first.
    exact: proba_monad.p_is_rs.
    exact: proba_monad.s_is_pq.
  apply mem_hull_setU => //; exact/mem_hull_setU.
- move=> a; rewrite -in_setE => Ha; rewrite -in_setE.
  set xy := CSet.mk (convex_hull (x `|` y)).
  case/boolP : (xy == cset0 A) => [|/cset0PN H1].
    rewrite cset0P hull_eq0 => /eqP; rewrite setU_eq0 => -[x0 y0].
    by move: Ha; rewrite x0 y0 3!set0U hull0 set0U hullI.
  case/boolP : (z == cset0 A) => [|/cset0PN H2].
    rewrite cset0P => /eqP z0.
    by move: Ha; rewrite z0 2!setU0 hull_cset hullI.
  case: (hull_setU H1 H2 Ha) => d1 [d1xy [d [dz [p Hp]]]]; rewrite Hp.
  case/boolP : (x == cset0 A) => [|/cset0PN H3].
    rewrite cset0P => /eqP x0.
    by move: Ha; rewrite x0 2!set0U hullI hull_cset -Hp.
  case/boolP : (y == cset0 A) => [|/cset0PN H4].
    rewrite cset0P => /eqP y0.
    by move: Ha; rewrite y0 set0U setU0 2!hull_cset -Hp.
  case: (hull_setU H3 H4 d1xy) => d2 [d2y [d3 [d3z [q Hq]]]]; rewrite Hq.
  set s := proba_monad.s_of_pq (`Pr p.~) (`Pr q.~).
  set r := proba_monad.r_of_pq (`Pr p.~) (`Pr q.~).
  rewrite -(@convA _ (`Pr s.~) (`Pr r.~)); last 2 first.
    by rewrite /= proba_monad.s_is_pq /= 2!onemK mulRC.
    rewrite 2!onemK (proba_monad.p_is_rs (`Pr p.~) (`Pr q.~)).
    by rewrite -/s -/r mulRC.
  apply mem_hull_setU => //; exact/mem_hull_setU.
Qed.

Lemma nchoiceDr p :
  right_distributive (fun x y => x <.| p |.> y) (fun x y => nchoice x y).
Proof.
move=> x y z.
case/boolP : (y == @cset0 A) => [/eqP|/cset0PN] y0.
  by rewrite {}y0 nchoice0X pchoice_cset0 nchoice0X.
case/boolP : (z == @cset0 A) => [/eqP|/cset0PN] z0.
  by rewrite {}z0 nchoiceX0 pchoice_cset0 nchoiceX0.
case/boolP : (x == @cset0 A) => [/eqP|/cset0PN] x0.
  by rewrite {}x0 !cset0_pchoice nchoice0X.
have /cset0PN xy0 : (pchoice p x y != @cset0 A).
  apply/negP => /pchoice_eq0 /orP[]; exact/negP/cset0PN.
have /cset0PN xz0 : (pchoice p x z != @cset0 A).
  apply/negP => /pchoice_eq0 /orP[]; exact/negP/cset0PN.
apply/val_inj => /=; apply eqEsubset.
- move=> a [b [bx [c [xyz ->{a}]]]].
  case: (hull_setU y0 z0 xyz) => c1 [c1y [c2 [c2z [q cq]]]].
  rewrite cq Conv2DistProp.distribute -in_setE; apply mem_hull_setU.
  rewrite in_setE; exists b; split => //.
  exists c1; split => //.
  rewrite in_setE; exists b; split => //.
  by exists c2; split => //.
- move=> a.
  rewrite /nchoice' -in_setE.
  case/(hull_setU xy0 xz0) => b [bxy [c [cxz [q ->{a}]]]].
  rewrite /nchoice /pchoice' /nchoice' /=.
  move: bxy; rewrite in_setE /pchoice /= /pchoice' => -[a' [xa' [b' [b'y] Hb']]].
  move: cxz; rewrite in_setE /pchoice /= /pchoice' => -[a'' [xa'' [b'' [b''y] Hb'']]].
  exists (a' <| q |> a''); split.
    rewrite in_setE.
    rewrite -(hull_cset x).
    rewrite -in_setE.
    rewrite -(setUid x).
    by apply mem_hull_setU.
  exists (b' <| q |> b''); split.
    by apply mem_hull_setU.
  by rewrite Hb' Hb'' Conv2DistProp.commute.
Qed.

End probabilistic_choice_nondeterministic_choice.

(* non-empty convex sets *)
Module NECSet.
Section def.
Local Open Scope classical_set_scope.
Local Open Scope proba_scope.
Variable A : finType.
Record t : Type := mk {
  car : cset A ;
  H : car != @cset0 A }.
End def.
End NECSet.
Notation necset := NECSet.t.

Section necset_canonical.
Variable (A : finType).

Canonical necset_subType := [subType for @NECSet.car A].
Canonical necset_predType :=
  Eval hnf in mkPredType (fun t : necset A => (fun x => x \in NECSet.car t)).
Definition necset_eqMixin := Eval hnf in [eqMixin of (@necset A) by <:].
Canonical necset_eqType := Eval hnf in EqType (@necset A) necset_eqMixin.

End necset_canonical.

Section necset_prop.

Lemma pchoice_ne (A : finType) (p : prob) (m1 m2 : necset A) :
  (@pchoice _ p (NECSet.car m1) (NECSet.car m2)) != cset0 A.
Proof.
move: m1 m2 => -[m1 H1] -[m2 H2] /=.
by apply/negP => /pchoice_eq0; rewrite (negbTE H1) (negbTE H2).
Qed.

Lemma nchoice_ne (A : finType) (m1 m2 : necset A) :
  (@nchoice _ (NECSet.car m1) (NECSet.car m2)) != cset0 A.
Proof.
move: m1 m2 => -[m1 H1] -[m2 H2] /=.
by apply/negP => /nchoice_eq0; rewrite (negbTE H1) (negbTE H2).
Qed.

End necset_prop.

Require Import relmonad.

Module ModelAltProb.
Section modelaltprob.

Local Obligation Tactic := idtac.

Let F := necset.

(* we assume the existence of appropriate BIND and RET *)
Axiom BIND : forall (A B : finType) (m : F A) (f : A -> F B), F B.
Axiom RET : forall A : finType, A -> F A.
Axiom BINDretf : relLaws.left_neutral BIND RET.
Axiom BINDmret : relLaws.right_neutral BIND RET.
Axiom BINDA : relLaws.associative BIND.

Program Definition apmonad : relMonad.t := @relMonad.Pack F
  (@relMonad.Class _ (@RET) BIND _ _ _ ).
Next Obligation. exact: BINDretf. Qed.
Next Obligation. exact: BINDmret. Qed.
Next Obligation. exact: BINDA. Qed.

Let nepchoice : prob -> forall A, F A -> F A -> F A :=
  fun p A m1 m2 => NECSet.mk (pchoice_ne p m1 m2).

Local Notation "mx <.| p |.> my" := (@nepchoice p _ mx my).

Let nepchoice0 A (mx my : F A) : mx <.| `Pr 0 |.> my = my.
Proof. apply val_inj => /=; rewrite pchoice0 //; by case: mx => ? /= /cset0PN. Qed.
Let nepchoice1 A (mx my : F A) : mx <.| `Pr 1 |.> my = mx.
Proof. apply val_inj => /=; rewrite pchoice1 //; by case: my => ? /= /cset0PN. Qed.
Let nepchoiceC A p (mx my : F A) : mx <.| p |.> my = my <.| `Pr p.~ |.> mx.
Proof. apply val_inj => /=; by rewrite pchoiceC. Qed.
Let nepchoicemm A p : idempotent (@nepchoice p A).
Proof. move=> x; apply val_inj => /=; exact: pchoicemm. Qed.
Lemma nepchoiceA A (p q r s : prob) (mx my mz : F A) :
  (p = r * s :> R /\ s.~ = p.~ * q.~)%R ->
  mx <.| p |.> (my <.| q |.> mz) = (mx <.| r |.> my) <.| s |.> mz.
Proof. move=> H; apply val_inj => /=; exact: nepchoiceA. Qed.

Axiom nepchoice_bindDl : forall p, relLaws.bind_left_distributive BIND (nepchoice p).

Let nenchoice : forall A, F A -> F A -> F A := fun A m1 m2 => NECSet.mk (nchoice_ne m1 m2).

Let nenchoiceA A : associative (@nenchoice A).
Proof. move=> a b c; apply val_inj => /=; by rewrite nchoiceA. Qed.

Axiom nenchoice_bindDl : relLaws.bind_left_distributive BIND nenchoice.

Let nenchoicemm A : idempotent (@nenchoice A).
Proof. move=> a; apply val_inj => /=; by rewrite nchoicemm. Qed.
Let nenchoiceC A : commutative (@nenchoice A).
Proof. move=> a b; apply val_inj => /=; by rewrite nchoiceC. Qed.
Let nenchoiceDr A p : right_distributive (fun x y : F A => x <.| p |.> y) (fun x y => nenchoice x y).
Proof. move=> a b c; apply val_inj => /=; by rewrite nchoiceDr. Qed.

Program Let nepprob_mixin : relMonadProb.mixin_of apmonad :=
  @relMonadProb.Mixin apmonad (fun p (A : finType) (m1 m2 : F A) =>
    (@nepchoice p _ m1 m2 )) _ _ _ _ _ _.
Next Obligation. exact: nepchoice0. Qed.
Next Obligation. exact: nepchoice1. Qed.
Next Obligation. exact: nepchoiceC. Qed.
Next Obligation. exact: nepchoicemm. Qed.
Next Obligation. exact: nepchoiceA. Qed.
Next Obligation. exact: nepchoice_bindDl. Qed.

Let nepprob_class : relMonadProb.class_of F := @relMonadProb.Class _ _ nepprob_mixin.

Definition nepprob : relMonadProb.t := relMonadProb.Pack nepprob_class.

Program Definition nepalt : relaltMonad := @relMonadAlt.Pack _
  (@relMonadAlt.Class _ (relMonad.class apmonad)
    (@relMonadAlt.Mixin apmonad nenchoice _ _)).
Next Obligation. exact: nenchoiceA. Qed.
Next Obligation. exact: nenchoice_bindDl. Qed.

Program Definition apaltci := @relMonadAltCI.Pack _
  (@relMonadAltCI.Class _ (relMonadAlt.class nepalt) (@relMonadAltCI.Mixin _ _ _ _)).
Next Obligation. exact: nenchoicemm. Qed.
Next Obligation. exact: nenchoiceC. Qed.

Program Definition altprob := @relMonadAltProb.Pack F
  (@relMonadAltProb.Class _ (relMonadAltCI.class apaltci) (relMonadProb.mixin (relMonadProb.class nepprob)) (@relMonadAltProb.Mixin _ _ _)).
Next Obligation. exact: nenchoiceDr. Qed.

End modelaltprob.
End ModelAltProb.
