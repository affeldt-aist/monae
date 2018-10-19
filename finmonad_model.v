Require Import FunctionalExtensionality Reals.
Require Import ssreflect ssrmatching ssrfun ssrbool.
From mathcomp Require Import eqtype ssrnat seq choice fintype tuple finset.

From infotheo Require Import proba ssr_ext.

Require Import proba_monad (* TODO(rei): essentially to use Prob.t *)
  finmonad.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*
  This file provides models:
  - for the nondeterministic-state monad
  - for the probability monad.
      depends on the formalization of distributions from the infotheo library
      (https://github.com/affeldt-aist/infotheo).
*)

Module ModelBacktrackableState.

Section monad.
Variable S : finType.
Local Obligation Tactic := try by [].

Program Definition _monad : finmonad := @finMonad.Pack _
(@finMonad.Class _
(fun A (a : A) (s : S) => [set (a, s)]) (* ret *)
(fun A B m (f : A -> S -> {set (B * S)}) =>
     fun s => \bigcup_(i in (fun x => f x.1 x.2) @: (m s)) i) (* bind *)
_ _ _).
Next Obligation.
move=> A B /= m f; extensionality s; by rewrite imset_set1 /= big_set1.
Qed.
Next Obligation.
move=> A B /=; extensionality s.
apply/setP => /= x; apply/bigcupP; case: ifPn => xBs.
  exists [set x]; by [apply/imsetP; exists x | rewrite inE].
case => /= SA /imsetP[] /= sa saBs ->{SA}; rewrite inE => /eqP Hx.
move: xBs; rewrite Hx; apply/negP; rewrite negbK; by case: sa saBs Hx.
Qed.
Next Obligation.
move=> A B C /= m f g; extensionality s.
apply/setP => /= x; apply/bigcupP/bigcupP; case => /= CS /imsetP[/=].
- move=> bs /bigcupP[/= BS] /imsetP[/= sa] sams ->{BS} bsfsa ->{CS} xgbs.
  exists (\bigcup_(i in [set g x0.1 x0.2 | x0 in f sa.1 sa.2]) i).
    by apply/imsetP => /=; exists sa.
  apply/bigcupP; exists (g bs.1 bs.2) => //; by apply/imsetP => /=; exists bs.
- move=> sa sams ->{CS} /bigcupP[/= CS] /imsetP[/= bs] bsfsa ->{CS} xgbs.
  exists (g bs.1 bs.2) => //; apply/imsetP => /=; exists bs => //.
  apply/bigcupP => /=; exists (f sa.1 sa.2) => //; by apply/imsetP => /=; exists sa.
Qed.
End monad.

Section state.
Variable S : finType.
Local Obligation Tactic := try by [].

Program Definition _state : finstateMonad S :=
(@finMonadState.Pack _ _
  (@finMonadState.Class _ _ (finMonad.class (_monad S)) (@finMonadState.Mixin _ _
(fun s => [set (s, s)]) (* get *)
(fun s _ => [set (tt, s)]) (* put *)
_ _ _ _))).
Next Obligation.
move=> s s'; extensionality s''.
rewrite /Bind /=; apply/setP => /= x; rewrite inE; apply/bigcupP/eqP.
- by case => /= x0 /imsetP[/= x1]; rewrite inE => /eqP _ ->; rewrite inE => /eqP.
- move=> -> /=; exists [set (tt, s')]; last by rewrite inE.
  by apply/imsetP => /=; exists (tt, s) => //; rewrite inE.
Qed.
Next Obligation.
move=> s; extensionality s'.
rewrite /Bind /=; apply/setP => /= x; apply/bigcupP/bigcupP.
- case => /= x0 /imsetP[/= x1]; rewrite inE => /eqP -> ->; rewrite inE /= => /eqP ->.
  exists [set (s, s)]; last by rewrite inE.
  apply/imsetP => /=; exists (tt, s) => //; by rewrite inE.
- case => /= x0 /imsetP[/= x1]; rewrite inE => /eqP -> ->; rewrite inE => /eqP ->.
  exists [set (s ,s)]; last by rewrite inE.
  by apply/imsetP => /=; exists (tt, s) => //; rewrite inE.
Qed.
Next Obligation.
extensionality s.
rewrite /Bind /skip /= /Ret; apply/setP => /= x; apply/bigcupP/idP.
- by case => /= x0 /imsetP[/= x1]; rewrite inE => /eqP -> ->; rewrite inE.
- rewrite inE => /eqP ->; exists [set (tt, s)]; last by rewrite inE.
  apply/imsetP; exists (s, s) => //; by rewrite inE.
Qed.
Next Obligation.
move=> k; extensionality s; rewrite /Bind /=; apply/setP => x; apply/bigcupP/bigcupP.
- case => /= x0 /imsetP[/= x1]; rewrite inE => /eqP -> -> /bigcupP[/= x2] /imsetP[/= x3].
  rewrite inE => /eqP -> /= -> xkss.
  exists (k s s s) => //; apply/imsetP; exists (s, s) => //; by rewrite inE.
- case => /= x0 /imsetP[/= x1]; rewrite inE => /eqP -> -> /= xksss.
  exists (\bigcup_(i in [set k (s, s).1 x2.1 x2.2 | x2 in [set ((s, s).2, (s, s).2)]]) i).
    apply/imsetP; exists (s, s) => //; by rewrite inE.
  apply/bigcupP; exists (k s s s) => //; apply/imsetP; exists (s, s) => //=; by rewrite inE.
Qed.

End state.

Section fail.
Variable S : finType.
Program Definition _fail : finfailMonad := @finMonadFail.Pack _
  (@finMonadFail.Class _ (finMonad.class (_monad S))
    (@finMonadFail.Mixin _ (fun (A : finType) (_ : S) => set0) _)).
Next Obligation.
move=> A B g; extensionality s; apply/setP => x; rewrite inE /Bind; apply/negbTE.
apply/bigcupP; case => /= x0 /imsetP[/= sa]; by rewrite inE.
Qed.

End fail.

Section alt.

Variable S : finType.
Local Obligation Tactic := try by [].
Program Definition _alt : finaltMonad := @finMonadAlt.Pack _
  (@finMonadAlt.Class _ (@finMonad.class (_monad S))
    (@finMonadAlt.Mixin (_monad S)
      (fun (A : finType) (a b : S -> {set A * S}) (s : S) => a s :|: b s) _ _)).
Next Obligation. by move=> A a b c; extensionality s; rewrite setUA. Qed.
Next Obligation.
move=> A B /= m1 m2 k; extensionality s; rewrite /Bind /=.
apply/setP => /= bs; rewrite !inE; apply/bigcupP/orP.
- case => /= BS /imsetP[/= sa]; rewrite inE => /orP[sam1s ->{BS} Hbs|sam2s ->{BS} Hbs].
  + left; apply/bigcupP => /=; exists (k sa.1 sa.2) => //; apply/imsetP; by exists sa.
  + right; apply/bigcupP => /=; exists (k sa.1 sa.2) => //; apply/imsetP; by exists sa.
- case => /bigcupP[/= BS /imsetP[/= sa sams ->{BS} bsksa]].
  by exists (k sa.1 sa.2) => //; apply/imsetP; exists sa => //; rewrite inE sams.
  by exists (k sa.1 sa.2) => //; apply/imsetP; exists sa => //; rewrite inE sams orbT.
Qed.

End alt.

Section nondet.

Variable S : finType.
Local Obligation Tactic := try by [].
Program Definition nondetbase : finnondetMonad :=
  @finMonadNondet.Pack _ (@finMonadNondet.Class _ (@finMonadFail.class (_fail S))
    (@finMonadAlt.mixin (_alt S) _) (@finMonadNondet.Mixin _ _ _ _)).
Next Obligation. move=> A /= m; extensionality s; by rewrite set0U. Qed.
Next Obligation. move=> A /= m; extensionality s; by rewrite setU0. Qed.
End nondet.

Section nondetstate.

Variable S : finType.
Local Obligation Tactic := try by [].
Program Definition nondetstate : finnondetStateMonad S :=
  @finMonadNondetState.Pack _ _
    (@finMonadNondetState.Class _ _ (finMonadNondet.class (nondetbase S))
      (finMonadState.mixin (finMonadState.class (_state S))) (@finMonadNondetState.Mixin _ _ _)).
Next Obligation.
move=> A B /= g; rewrite /Bind /=; extensionality s; apply/setP => /= sa.
apply/bigcupP/idP.
- case => /= SA /imsetP[/= bs bsgs ->{SA}]; by rewrite inE.
- by rewrite inE.
Qed.
Next Obligation.
move=> A B /= m k1 k2; extensionality s; rewrite /Bind /=; apply/setP => /= bs.
apply/bigcupP/idP.
- case => /= BS /imsetP[/= sa sams ->{BS}]; rewrite inE => /orP[bsk1|bsk2].
  + rewrite inE; apply/orP; left; apply/bigcupP; exists (k1 sa.1 sa.2) => //.
    apply/imsetP; by exists sa.
  + rewrite inE; apply/orP; right; apply/bigcupP; exists (k2 sa.1 sa.2) => //.
    apply/imsetP; by exists sa.
- rewrite inE => /orP[|] /bigcupP[/= BS] /imsetP[/= sa sams ->{BS}] bsk.
  exists (k1 sa.1 sa.2 :|: k2 sa.1 sa.2).
    apply/imsetP; by exists sa.
  by rewrite inE bsk.
  exists (k1 sa.1 sa.2 :|: k2 sa.1 sa.2).
    apply/imsetP; by exists sa.
  by rewrite inE bsk orbT.
Qed.

End nondetstate.

End ModelBacktrackableState.

Module finMonadProbModel.
Local Obligation Tactic := idtac.

Program Definition monad : finMonad.t := @finMonad.Pack proba.dist
  (@finMonad.Class _ Dist1.d DistBind.d _ _ _ ).
Next Obligation. move=> ? ? ? ?; exact: DistBind1f. Qed.
Next Obligation. move=> ? ?; exact: DistBindp1. Qed.
Next Obligation. move=> ? ? ? ? ?; exact: DistBindA. Qed.

Program Definition prob_mixin : finMonadProb.mixin_of monad :=
  @finMonadProb.Mixin monad (fun p (A : finType) (m1 m2 : proba.dist A) =>
    (@ConvexDist.d A m1 m2 _ (Prob.O1 p))) _ _ _ _ _ _.
Next Obligation. move=> ? ? ?; exact: ConvexDist.d0. Qed.
Next Obligation. move=> ? ? ?; exact: ConvexDist.d1. Qed.
Next Obligation. move=> ? ? ? ?; exact: ConvexDist.quasi_commute. Qed.
Next Obligation. move=> ? ? ?; exact: ConvexDist.idempotent. Qed.
Next Obligation. move=> ? ? ? ? ? ? ? ? [? ?] /=; exact: ConvexDist.quasi_assoc. Qed.
Next Obligation. move=> ? ? ? ? ? ?; exact: ConvexDist.bind_left_distr. Qed.

Definition prob_class : finMonadProb.class_of proba.dist :=
  @finMonadProb.Class _ _ prob_mixin.

Definition prob : finMonadProb.t := finMonadProb.Pack prob_class.

End finMonadProbModel.
