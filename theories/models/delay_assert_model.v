From mathcomp Require Import all_ssreflect.
Require Import monad_transformer hierarchy delay_monad_model delayexcept_model.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.
Local Open Scope do_notation.

Notation M := (MX unit Delay).
Notation "a '≈e' b" := (wBisimDE a b) (at level 70).
Hint Extern 0 (wBisimDE _ _) => setoid_reflexivity.

Definition sum_f A B (f : A -> B) := sum_rect (fun => B) f f.

(*Equality between hierarchy.while and delay_monad_model.while*)
Lemma whileDEE A B (body : A -> M (B + A)) x :
  whileDE body x = while (@DEA Delay _ _ \o body) x.
Proof. by []. Qed.

Lemma partial_correctness X x p (body : X -> M (X + X)) :
   assert p x ≈e @ret M _ x  ->
   (forall x, assert p x ≈e @ret M _ x ->
          body x >>= sum_f (assert p) ≈e body x >>= sum_f Ret) ->
   bassert p (whileDE body x) ≈e whileDE body x.
Proof.
move => Hx HInv.
case: (TerminatesP (whileDE body x)) =>
  [[[u' /iff_Terminates_wBret/iff_wBisims_wBisim Hs
    |x' /iff_Terminates_wBret [n Hs]]]|/iff_Diverges_wBisimspin Hs].
- by rewrite/bassert bindXE Hs bindretf.
- rewrite steps_Dnow in Hs.
  move: x x' Hx Hs.
  elim: n => [/=|n IH] x x' Hx;
             rewrite whileDEE whileE /DEA functions.compE fmapE.
    case Hb: (body x) => [uxx|].
      case: uxx Hb => [u//|[y/=|y/=]] Hb;
                      rewrite bindretf/=bindretf.
      - by rewrite/bassert bindXE bindretf.
      - rewrite/bassert bindXE bindretf => _.
        move: (HInv x Hx).
        by rewrite Hb !bindretf /=.
      - by rewrite /retX => contr.
    by rewrite !bindDmf/retX => contr.
  set d := body x.
  have : d ≈ body x by [].
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
    move/IH => IH'.
    move/IH'.
    by rewrite {1}whileDEE /DEA /bassert !bindXE
         !bindDmf -!bindXE !wBisim_DLater.
  move => Hd' HH.
  rewrite/bassert bindXE !bindA !bindDmf.
  apply: wBLater.
  rewrite -!bindA -bindXE -/(bassert p _).
  apply: CIH.
    by rewrite -Hd' wBisim_DLater.
  apply: monotonicity_steps'.
  by rewrite -bindDmf -bindDmf.
rewrite/bassert bindXE Hs.
by apply/iff_Diverges_wBisimspin/Diverges_bindspinf.
Qed.
