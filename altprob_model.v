Require Import FunctionalExtensionality Coq.Program.Tactics ProofIrrelevance.
Require Classical.
Require Import ssreflect ssrmatching ssrfun ssrbool.
From mathcomp Require Import eqtype ssrnat seq choice fintype tuple.
From mathcomp Require Import finfun finset bigop.
From mathcomp Require Import boolp classical_sets.
Require Import Reals Lra.
From infotheo Require Import ssrR Reals_ext Rbigop proba convex.
Require Import monad monad_composition monad_model.

Reserved Notation "mx <.| p |.> my" (format "mx  <.| p |.>  my", at level 50).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* wip *)

Local Open Scope convex_scope.
Local Open Scope proba_scope.
Local Open Scope classical_set_scope.
Local Open Scope reals_ext_scope.

(* more lemmas about Conv2Dist.d that use the convex space interface *)
Module Conv2DistProp.
Section prop.
Variables (A : finType).
(* TODO: the R version is here because of lra, etc. *)
Lemma commute' (x1 y1 x2 y2 : dist A) p q (Hp : (0 <= p <= 1)%R) (Hq : (0 <= q <= 1)%R) :
  (x1 <|Prob.mk Hq|> y1) <|Prob.mk Hp|> (x2 <|Prob.mk Hq|> y2) =
  (x1 <|Prob.mk Hp|> x2) <|Prob.mk Hq|> (y1 <|Prob.mk Hp|> y2).
Proof.
case/boolP : (p == R0 :> R) => [|]/eqP p0.
  by subst p; rewrite !(ProofIrrelevance.proof_irrelevance _ Hp OO1) !conv0.
case/boolP : (q == R0 :> R) => [|]/eqP q0.
  by subst q; rewrite !(ProofIrrelevance.proof_irrelevance _ Hq OO1) !conv0.
case/boolP : (p == R1 :> R) => [|]/eqP p1.
  by subst p; rewrite !(ProofIrrelevance.proof_irrelevance _ Hp O11) !conv1.
case/boolP : (q == R1 :> R) => [|]/eqP q1.
  by subst q; rewrite !(ProofIrrelevance.proof_irrelevance _ Hq O11) !conv1.
set r := (p * q)%R.
have pq1 : (p * q != 1)%R.
  apply/eqP => pq1; have {p1} : (p < 1)%R by lra.
  rewrite -pq1 mulRC -ltR_pdivr_mulr; last lra.
  rewrite divRR; [lra | exact/eqP].
have r1 : (r < 1)%R.
  rewrite ltR_neqAle; split; [exact/eqP|rewrite -(mulR1 1%R); apply/leR_pmul; tauto].
set s := ((p - r) / (1 - r))%R.
rewrite /Conv /= (* TODO *).
rewrite -(@Conv2Dist.quasi_assoc' _ r s _ _ x1); last 2 first.
  by rewrite mulRC.
  rewrite /onem {}/s; field; by apply/eqP; rewrite subR_eq0 eq_sym.
  split.
  - apply divR_ge0; last by rewrite subR_gt0.
    rewrite subR_ge0 /r -{2}(mulR1 p); apply/leR_wpmul2l; tauto.
  - rewrite /s leR_pdivr_mulr ?subR_gt0 // mul1R leR_add2r; tauto.
  split; by [apply/mulR_ge0; tauto | rewrite leR_eqVlt; right].
move=> Hs Hr.
rewrite (Conv2Dist.skewed_commute y1).
set t := (s.~ * q)%R.
have t01 : (0 <= t <= 1)%R.
  split; first by apply/mulR_ge0; [apply onem_ge0; tauto|tauto].
  rewrite /t -(mulR1 1%R); apply leR_pmul;
    [apply onem_ge0; tauto | tauto | apply onem_le1; tauto | tauto].
have t1 : (t < 1)%R.
  rewrite ltR_neqAle; split; last tauto.
  move=> t1; subst t.
  have {q1} : (q < 1)%R by lra.
    rewrite -t1 -ltR_pdivr_mulr; last by lra.
    rewrite divRR; [rewrite /onem; lra | exact/eqP].
rewrite -(@Conv2Dist.quasi_assoc' _ t p.~ _ _ x2) => //; last 2 first.
  by rewrite mulRC.
  rewrite /= !onemK /t /s /r /onem; field.
  by apply/eqP; rewrite subR_eq0 eq_sym.
  split; [apply onem_ge0; tauto | apply onem_le1; tauto].
move=> Hp'.
rewrite (@Conv2Dist.quasi_assoc' _ _ _ p.~.~ q x1); last 2 first.
  by rewrite onemK.
  rewrite /t /onem /s /r; field; by apply/eqP; rewrite subR_eq0 eq_sym.
  by rewrite onemK.
rewrite !onemK => Hp''.
rewrite (Conv2Dist.skewed_commute y2 y1) /=.
congr (Conv2Dist.d x1 x2 _ <| Prob.mk Hq |> _).
  exact/prob_ext.
apply/dist_ext => a /=.
by rewrite !Conv2Dist.dE /= !onemK.
Qed.

Lemma commute (x1 y1 x2 y2 : dist A) p q :
  (x1 <|q|> y1) <|p|> (x2 <|q|> y2) = (x1 <|p|> x2) <|q|> (y1 <|p|> y2).
Proof. by move: p q => -[p Hp] [q Hq]; rewrite commute'. Qed.

Lemma distribute (x y z : dist A) (p q : prob) :
  x <| p |> (y <| q |> z) = (x <| p |> y) <| q |> (x <| p |> z).
Proof. by rewrite -{1}(convmm x q) commute. Qed.

End prop.
End Conv2DistProp.

(* TODO: generalization in progress *)
Section convex_set_of_distributions_prop.
Variable A : finType.

Lemma convex_hull (X : set (dist A)) : is_convex_set (hull X).
Proof.
apply/asboolP => x y p; rewrite 2!in_setE.
move=> -[n [g [d [gX ->{x}]]]].
move=> -[m [h [e [hX ->{y}]]]].
rewrite in_setE.
exists (n + m).
exists [ffun i => match fintype.split i with inl a => g a | inr a => h a end].
exists (AddDist.d d e p).
rewrite !convn_convdist.
rewrite ConvDist_Add; split => //.
move=> a -[i _].
rewrite ffunE.
case: splitP => j _ <-; by [apply gX; exists j | apply hX; exists j].
Qed.

Lemma hullI (X : set (dist A)) : hull (hull X) = hull X.
Proof.
rewrite predeqE => d; split.
- move=> -[n [g [e [gX ->{d}]]]].
  move: (convex_hull X); rewrite is_convex_setP /is_convex_set_n => /asboolP/(_ _ g e gX).
  by rewrite in_setE.
- by rewrite -in_setE => /hull_mem; rewrite in_setE.
Qed.
End convex_set_of_distributions_prop.

Section CSet_prop.
Variable A : finType.

Lemma hull_setU (a : dist A) (x y : {convex_set (dist A)}) :
  x !=set0 -> y !=set0 -> a \in hull (x `|` y) ->
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
  exists (Convn gy (CodomDDist.d gX ge)); split.
    move: (CSet.H y); rewrite is_convex_setP /is_convex_set_n => /asboolP.
    apply => d.
    rewrite -in_setE => /imsetP[i _ ->{d}].
    rewrite /gy -in_setE; case: ifPn => //; by rewrite in_setE.
  exists (`Pr 0).
  rewrite Ha conv0; apply/dist_ext => a0.
  rewrite 2!convn_convdist 2!ConvDist.dE; apply eq_bigr => i _.
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
    move: (CSet.H x); rewrite is_convex_setP /is_convex_set_n => /asboolP.
    rewrite -convn_convdist; apply => d.
    rewrite -in_setE => /imsetP[i _ ->{d}].
    rewrite /gx -in_setE; case: ifPn => //; by rewrite in_setE.
  exists dy; split; first by rewrite in_setE.
  exists (`Pr 1).
  rewrite Ha conv1; apply/dist_ext => a0.
  rewrite convn_convdist 2!ConvDist.dE; apply eq_bigr => i _.
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
exists (Convn gx e1); split.
  move: (CSet.H x).
  rewrite is_convex_setP /is_convex_set_n => /asboolP; apply.
  move=> d.
  rewrite -in_setE.
  case/imsetP => i _ ->{d}.
  rewrite /gx -in_setE.
  case: ifPn => //; by rewrite in_setE.
exists (Convn gy e2); split.
  move: (CSet.H y).
  rewrite is_convex_setP /is_convex_set_n => /asboolP; apply.
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
rewrite convn_convdist ConvDist.dE Conv2Dist.dE.
rewrite (bigID [pred i | (g i \in y) && (g i \notin x)]) /= addRC.
congr (_ + _)%R.
- rewrite convn_convdist ConvDist.dE big_distrr /= big_mkcond /=; apply eq_bigr => i _.
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
- rewrite convn_convdist ConvDist.dE big_distrr /= big_mkcond /=; apply eq_bigr => i _.
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

Section probabilistic_choice_nondeterministic_choice.
Local Open Scope proba_scope.
Local Open Scope classical_set_scope.
Variable A : finType.

Definition pchoice' (p : prob) (X Y : {convex_set (dist A)}) : set (dist A) :=
  [set d | exists x, x \in X /\ exists y, y \in Y /\ d = x <| p |> y].

Lemma pchoice'_self (p : prob) (X : {convex_set (dist A)}) :
  [set d | exists x, x \in X /\ d = x <| p |> x] `<=` pchoice' p X X.
Proof.
move=> d [x [xX ->{d}]]; rewrite /pchoice'.
exists x; split => //; by exists x; split.
Qed.

Lemma Hpchoice (p : prob) (X Y : {convex_set (dist A)}) : is_convex_set (pchoice' p X Y).
Proof.
apply/asboolP => x y q /=; rewrite in_setE => -[d [dX [d' [d'Y ->]]]].
rewrite in_setE => -[e [eX [e' [e'Y ->]]]]; rewrite in_setE Conv2DistProp.commute.
exists (Conv2Dist.d d e q); split; first exact: (asboolW (CSet.H X)).
exists (Conv2Dist.d d' e' q); split => //; exact: (asboolW (CSet.H Y)).
Qed.

Definition pchoice (p : prob) (X Y : {convex_set (dist A)}) : {convex_set (dist A)} :=
  CSet.mk (@Hpchoice p X Y).

Local Notation "mx <.| p |.> my" := (@pchoice p mx my).

Lemma pchoice_cset0 (x : {convex_set (dist A)}) p : x <.|p|.> cset0 _ = cset0 _.
Proof.
apply val_inj => /=; rewrite /pchoice'.
rewrite predeqE => d; split => // -[d1 [d1x [d2 []]]]; by rewrite in_setE.
Qed.

Lemma cset0_pchoice x p : cset0 _ <.|p|.> x = cset0 _.
Proof.
apply val_inj => /=; rewrite /pchoice'.
rewrite predeqE => d; split => // -[d1 []]; by rewrite in_setE.
Qed.

Lemma pchoice_eq0 p a b :
  a <.| p |.> b == cset0 _ -> (a == cset0 _) || (b == cset0 _).
Proof.
case/boolP : (a == cset0 _) => //= /cset0PN[da Hda].
case/boolP : (b == cset0 _) => //= /cset0PN[db Hdb].
case/eqP; rewrite /pchoice' => H.
suff : set0 (da <| p |> db) by [].
rewrite -H; exists da; split; first by rewrite in_setE.
exists db; split => //; by rewrite in_setE.
Qed.

Lemma pchoice0 (a b : {convex_set (dist A)}) : a !=set0 -> a <.| `Pr 0 |.> b = b.
Proof.
move=> a0; apply/val_inj=> /=; rewrite /pchoice' predeqE => d; split.
- move=> [x [xa]] [y [yb ->{d}]]; by rewrite -in_setE conv0.
- move=> bd; case: a0 => d' ad'; exists d'; split; first by rewrite in_setE.
  exists d; split; by [rewrite in_setE | rewrite conv0].
Qed.

Lemma pchoice1 (a b : {convex_set (dist A)}) : b !=set0 -> a <.| `Pr 1 |.> b = a.
Proof.
move=> b0; apply/val_inj => /=; rewrite /pchoice' predeqE => d; split.
- move=> [x [xa]] [y [yb ->{d}]]; by rewrite -in_setE conv1.
- move=> ad; case: b0 => d' bd'; exists d; split; first by rewrite in_setE.
  exists d'; split; by [rewrite in_setE | rewrite conv1].
Qed.

Lemma pchoiceC p (x y : {convex_set (dist A)}) : x <.| p |.> y = y <.| `Pr p.~ |.> x.
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

Lemma nepchoiceA (p q r s : prob) (x y z : {convex_set (dist A)}) :
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

Lemma Hnchoice (X Y : {convex_set (dist A)}) : is_convex_set (nchoice' X Y).
Proof.
apply/asboolP => x y p; rewrite /nchoice' => Hx Hy.
have := convex_hull (X `|` Y).
by move/asboolP => /(_ x y p Hx Hy).
Qed.

Definition nchoice (X Y : {convex_set (dist A)}) : {convex_set (dist A)} :=
  CSet.mk (@Hnchoice X Y).

Lemma nchoice0X (X : {convex_set (dist A)}) : nchoice (cset0 _) X = X.
Proof. by apply val_inj => /=; rewrite /nchoice' set0U hull_cset. Qed.

Lemma nchoiceX0 (X : {convex_set (dist A)}) : nchoice X (cset0 _) = X.
Proof. by apply val_inj => /=; rewrite /nchoice' setU0 hull_cset. Qed.

Lemma nchoice_eq0 a b :
  nchoice a b == cset0 _ -> (a == cset0 _) || (b == cset0 _).
Proof.
case/boolP : (a == cset0 _) => // /cset0PN a0.
case/boolP : (b == cset0 _) => //= /cset0PN b0 H.
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
  case/boolP : (x == cset0 _) => [|/cset0PN H1].
    rewrite cset0P => /eqP x0.
    by move: Ha; rewrite {}x0 2!set0U hullI /= hull_cset.
  set yz := CSet.mk (convex_hull (y `|` z)).
  case/boolP : (yz == cset0 _) => [|/cset0PN H2].
    rewrite cset0P hull_eq0 => /eqP; rewrite setU_eq0 => -[y0 z0].
    by move: Ha; rewrite y0 z0 2!setU0 hullI hull0 setU0.
  case: (hull_setU H1 H2 Ha) => d1 [d1x [d [dyz [p Hp]]]]; rewrite Hp.
  case/boolP : (y == cset0 _) => [|/cset0PN H3].
    rewrite cset0P => /eqP y0.
    by move: Ha; rewrite y0 set0U setU0 2!hull_cset -Hp.
  case/boolP : (z == cset0 _) => [|/cset0PN H4].
    rewrite cset0P => /eqP z0.
    by move: Ha; rewrite z0 2!setU0 hullI hull_cset -Hp.
  case: (hull_setU H3 H4 dyz) => d2 [d2y [d3 [d3z [q Hq]]]]; rewrite Hq.
  set s := Conv2Dist.s_of_pq p q.
  set r := Conv2Dist.r_of_pq p q.
  rewrite (@convA _ _ _ r s); last 2 first.
    exact: Conv2Dist.p_is_rs.
    exact: Conv2Dist.s_is_pq.
  apply mem_hull_setU => //; exact/mem_hull_setU.
- move=> a; rewrite -in_setE => Ha; rewrite -in_setE.
  set xy := CSet.mk (convex_hull (x `|` y)).
  case/boolP : (xy == cset0 _) => [|/cset0PN H1].
    rewrite cset0P hull_eq0 => /eqP; rewrite setU_eq0 => -[x0 y0].
    by move: Ha; rewrite x0 y0 3!set0U hull0 set0U hullI.
  case/boolP : (z == cset0 _) => [|/cset0PN H2].
    rewrite cset0P => /eqP z0.
    by move: Ha; rewrite z0 2!setU0 hull_cset hullI.
  case: (hull_setU H1 H2 Ha) => d1 [d1xy [d [dz [p Hp]]]]; rewrite Hp.
  case/boolP : (x == cset0 _) => [|/cset0PN H3].
    rewrite cset0P => /eqP x0.
    by move: Ha; rewrite x0 2!set0U hullI hull_cset -Hp.
  case/boolP : (y == cset0 _) => [|/cset0PN H4].
    rewrite cset0P => /eqP y0.
    by move: Ha; rewrite y0 set0U setU0 2!hull_cset -Hp.
  case: (hull_setU H3 H4 d1xy) => d2 [d2y [d3 [d3z [q Hq]]]]; rewrite Hq.
  set s := Conv2Dist.s_of_pq (`Pr p.~) (`Pr q.~).
  set r := Conv2Dist.r_of_pq (`Pr p.~) (`Pr q.~).
  rewrite -(@convA _ (`Pr s.~) (`Pr r.~)); last 2 first.
    by rewrite /= Conv2Dist.s_is_pq /= 2!onemK mulRC.
    rewrite 2!onemK (Conv2Dist.p_is_rs (`Pr p.~) (`Pr q.~)).
    by rewrite -/s -/r mulRC.
  apply mem_hull_setU => //; exact/mem_hull_setU.
Qed.

Lemma nchoiceDr p :
  right_distributive (fun x y => x <.| p |.> y) (fun x y => nchoice x y).
Proof.
move=> x y z.
case/boolP : (y == cset0 _) => [/eqP|/cset0PN] y0.
  by rewrite {}y0 nchoice0X pchoice_cset0 nchoice0X.
case/boolP : (z == cset0 _) => [/eqP|/cset0PN] z0.
  by rewrite {}z0 nchoiceX0 pchoice_cset0 nchoiceX0.
case/boolP : (x == cset0 _) => [/eqP|/cset0PN] x0.
  by rewrite {}x0 !cset0_pchoice nchoice0X.
have /cset0PN xy0 : (pchoice p x y != cset0 _).
  apply/negP => /pchoice_eq0 /orP[]; exact/negP/cset0PN.
have /cset0PN xz0 : (pchoice p x z != cset0 _).
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
  car : {convex_set (dist A)} ;
  H : car != cset0 _ }.
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
  (@pchoice _ p (NECSet.car m1) (NECSet.car m2)) != cset0 _.
Proof.
move: m1 m2 => -[m1 H1] -[m2 H2] /=.
by apply/negP => /pchoice_eq0; rewrite (negbTE H1) (negbTE H2).
Qed.

Lemma nchoice_ne (A : finType) (m1 m2 : necset A) :
  (@nchoice _ (NECSet.car m1) (NECSet.car m2)) != cset0 _.
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
