From mathcomp Require Import all_ssreflect.
From mathcomp Require boolp.
From HB Require Import structures.
Require Import monad_transformer hierarchy delay_monad_model delayexcept_model.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.
Local Open Scope do_notation.

Notation M := (MX unit Delay).
HB.instance Definition _ := Monad.on M.
Check (M : delayMonad).
Check whileDE.
Check delayExceptMonad.
Check wBisimDE.
Variable (Y : UU0) (p' : pred Y).
Check (bassert p' fail).
Variable (f : Y -> M (Y + Y)) (y : Y).
About sum_rect.
Definition sum_f A B (f : A -> B) := sum_rect (fun => B) f f.
Check steps.

Check wBisims.
Check TerminatesP.
Print whileDE.
(*Definition whileDE {A B} (body : A -> DE (B + A)) (x : A) : DE B := while (DEA \o body) x.*)
Check DEA.
(*Equality between hierarchy.while and delay_monad_model.while*)
Lemma whileDEE {A B} (body : A -> M (B + A)) (x : A) : whileDE body x = while (@DEA Delay _ _ \o body) x.
Proof. by []. Qed.

Lemma partial_correctness_terminates' X n (p : pred X) (body : X -> M (X + X)) (x x' : X) :
   (forall x, assert p x ≈ @ret M _ x -> body x >>= sum_f (assert p) ≈ body x >>= sum_f Ret) ->
   assert p x ≈ @ret M _ x  ->
   steps n (whileDE body x) = (@ret M _ x') ->
   bassert p (whileDE body x) ≈ whileDE body x.
Proof.
move => Hbody.
move: x x'.
elim: n => [/=|n IH] x x' H0.
  rewrite whileDEE.
  rewrite whileE.
  rewrite/DEA/=.
  rewrite fmapE.
  case Hb: (body x) => [uxx|].
    case: uxx Hb => [u //|[y /=|y /=]] Hb.
    - rewrite bindretf/=bindretf => _.
      by rewrite/bassert bindXE bindretf.
    - rewrite bindretf/=bindretf.
      rewrite/bassert bindXE bindretf => _.
      move: (Hbody x H0).
      by rewrite Hb !bindretf /=.
    - rewrite bindretf/=bindretf/retX => contr.
      inversion contr.
  rewrite !bindDmf/retX => contr.
  inversion contr.
rewrite whileDEE.
rewrite whileE.
rewrite/DEA.
rewrite functions.compE.
rewrite fmapE.
set d := body x.
have: d ≈ body x.
by [].
move: d.
cofix CIH => d.
case Hb: d => [uxx|d'].
  case: uxx Hb => [u //|[y /= Hd|y /= Hd]] Hb.
  - rewrite bindretf/=bindretf.
    rewrite/bassert bindXE bindretf => _.
    move: (Hbody x H0).
    rewrite -Hb.
    by rewrite !bindretf /=.
  - move: (Hbody x H0).
    rewrite !bindXE.
    rewrite -Hb.
    rewrite !bindretf/=.
    move/IH => IH'.
    move/IH'.
    rewrite {1}whileDEE.
    rewrite/DEA.
    rewrite/bassert !bindXE.
    rewrite !bindDmf.
    rewrite -!bindXE.
    by rewrite !wBisim_DLater.
move => Hd' HH.
rewrite/bassert.
rewrite bindXE.
rewrite !bindA.
rewrite !bindDmf.
apply wBLater.
rewrite -!bindA.
rewrite -bindXE.
rewrite -/(bassert p _).
apply CIH.
  rewrite -Hd'.
  by rewrite wBisim_DLater.
apply monotonicity_steps'.
by rewrite -bindDmf -bindDmf.
Qed.

Lemma partial_correctness_terminates X (x : X) (p : pred X) (body : X -> M (X + X)) (x' : X) :
   assert p x ≈ @ret M _ x  ->
   (forall x, assert p x ≈ @ret M _ x -> body x >>= sum_f (assert p) ≈ body x >>= sum_f Ret) ->
   wBisimDE (whileDE body x) (@ret M _ x') ->
   bassert p (whileDE body x) ≈ whileDE body x.
Proof.
move => H0 Hbody.
move/iff_wBisims_wBisim.
move => [n H].
rewrite steps_Dnow in H.
exact: (partial_correctness_terminates' Hbody H0 H).
Qed.
