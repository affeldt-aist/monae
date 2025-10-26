From mathcomp Require Import all_ssreflect.
From HB Require Import structures.
Require Import monad_transformer hierarchy delay_monad_model elgotexcept_model.

(**md**************************************************************************)
(* # Model for elgotAssertMonad.                                              *)
(*                                                                            *)
(* This monad is an Elgot monad satisfying equalities to prove partial        *)
(* correctness. It is the transformed Elgot monad using exception monad       *)
(* transformer.                                                               *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.
Local Open Scope do_notation.

Notation M := (MX unit Delay).
Notation "a '≈e' b" := (wBisimDE a b) (at level 70).
Hint Extern 0 (wBisimDE _ _) => setoid_reflexivity.

(*Equality between hierarchy.while and elgot_monad_model.while*)
Lemma whileDEE A B (body : A -> M (B + A)) x :
  whileDE body x = while (@DEA Delay _ _ \o body) x.
Proof. by []. Qed.

Lemma assertE X x (p : pred X) : @assert M _ p x ≈e Ret x <-> (p x) = true.
Proof.
split.
  rewrite/assert.
  case: (p x) => //.
  rewrite guardF bindfailf /wBisimDE.
  move/wBisims_wBisim.
  move/Stop_wBisimsRet => contr.
  inversion contr.
rewrite/assert => ->.
by rewrite guardT bindskipf.
Qed.
Lemma pcorrect X A x (p : pred (A + X)) (f : X -> M (A + X)) :
   p (inr x)  ->
   (forall x, p (inr x) ->
          f x >>= sum_rect (fun => M (A + X)) ((assert p) \o inl) ((assert p) \o inr) ≈e
    f x >>= sum_rect (fun => M (A + X)) (Ret \o inl) (Ret \o inr)) ->
   bassert p ((whileDE f x) >>= (Ret \o inl)) ≈e whileDE f x >>= (Ret \o inl).
Proof.
move => Hx HInv.
case: (StopP (whileDE f x)) =>
  [[[u' /Stop_wBisimsRet/wBisims_wBisim Hs
    |x' /Stop_wBisimsRet [n Hs]]]|/Diverge_wBisim_spinP Hs].
- by rewrite/bassert bindXE Hs !bindretf bindXE !bindretf.
- rewrite steps_Now in Hs.
  move: x x' Hx Hs.
  elim: n => [/=|n IH] x x' Hx;
             rewrite whileDEE whileE /DEA functions.compE fmapE.
    case Hb: (f x) => [uxx|d].
      case: uxx Hb => [u//|[y/=|y/=]] Hb;
                      rewrite bindretf/=bindretf.
      - by rewrite/bassert bindXE bindretf.
      - rewrite/bassert bindXE bindretf => _.
        move: (HInv x Hx).
        by rewrite Hb !bindretf/retX /=.
      - by rewrite /retX => contr.
    by rewrite !bind_Later => contr.
  set d := f x.
  have : d ≈ f x by [].
  move: d.
  cofix CIH => d.
  case Hb: d => [uxx|d'].
    case: uxx Hb => [u//|[y/= Hd|y/= Hd]] Hb;
                    rewrite bindretf/=bindretf.
      rewrite/bassert bindXE bindretf => _.
      move: (HInv x Hx).
      by rewrite -Hb !bindretf /=.
    move: (HInv x Hx).
    rewrite !bindXE -Hb !bindretf/=.
    move => HH.
    move/IH => IH'.
    rewrite -!whileDEE.
    rewrite /bassert !bind_Later.
    rewrite wBisim_Later -bindXE.
    rewrite -{2}IH' /bassert.
    by rewrite /retX.
    move: HH.
    by move/assertE.
    rewrite/bassert !bindXE !bindA !bind_Later /= => Hd' Hs.
    apply wBLater.
  rewrite -!bindA -bindXE -/(bassert p _).
  apply: CIH.
  by rewrite -Hd' wBisim_Later.
  apply: monotonicity_steps'.
  by rewrite /= /bassert bindA Hs.
rewrite !bindXE /bassert Hs.
apply: wBisim_trans.
apply Diverge_wBisim_spinP.
  rewrite bindA.
  by apply: Diverge_bindspinf.
apply: wBisim_sym.
apply Diverge_wBisim_spinP.
by apply Diverge_bindspinf.
Qed.

HB.instance Definition _ := @isMonadElgotAssert.Build M (@pcorrect).
