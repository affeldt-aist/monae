From mathcomp Require Import all_ssreflect.
From HB Require Import structures.
Require Import monad_transformer hierarchy delay_monad_model delayexcept_model.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.
Local Open Scope do_notation.

Notation M := (MX unit Delay).
Notation "a '≈e' b" := (wBisimDE a b) (at level 70).
Hint Extern 0 (wBisimDE _ _) => setoid_reflexivity.

(*Equality between hierarchy.while and delay_monad_model.while*)
Lemma whileDEE A B (body : A -> M (B + A)) x :
  whileDE body x = while (@DEA Delay _ _ \o body) x.
Proof. by []. Qed.
Check assert.
Lemma pcorrect X x p (f : X -> M (X + X)) :
   assert p x ≈e @ret M _ x  ->
   (forall x, assert p x ≈e @ret M _ x ->
          f x >>= sum_rect (fun => M X) (assert p) (assert p) ≈e f x >>= sum_rect (fun => M X) Ret Ret) ->
   bassert p (whileDE f x) ≈e whileDE f x.
Proof.
move => Hx HInv.
case: (TerminatesP (whileDE f x)) =>
  [[[u' /iff_Terminates_wBret/iff_wBisims_wBisim Hs
    |x' /iff_Terminates_wBret [n Hs]]]|/iff_Diverges_wBisimspin Hs].
- by rewrite/bassert bindXE Hs bindretf.
- rewrite steps_Dnow in Hs.
  move: x x' Hx Hs.
  elim: n => [/=|n IH] x x' Hx;
             rewrite whileDEE whileE /DEA functions.compE fmapE.
    case Hb: (f x) => [uxx|].
      case: uxx Hb => [u//|[y/=|y/=]] Hb;
                      rewrite bindretf/=bindretf.
      - by rewrite/bassert bindXE bindretf.
      - rewrite/bassert bindXE bindretf => _.
        move: (HInv x Hx).
        by rewrite Hb !bindretf /=.
      - by rewrite /retX => contr.
    by rewrite !bindDmf/retX => contr.
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

HB.instance Definition _ := @isMonadDelayAssert.Build M (@pcorrect).

Section bubblesort.
Let testseq := 8::4::3::7::6::5::2::1::nil.
Fixpoint sortl (l : seq nat) :=
  match l with
  | nil => nil
  | n :: tl => match tl with
              | nil => l
              | m :: tl' => if m < n then m :: n :: sortl tl'
                                    else n :: sortl tl
              end
  end.
Compute (sortl testseq).
Definition bubblesort_body (l : seq nat) : M (seq nat + seq nat) :=
  if l == sortl l then Ret (inl l) else Ret (inr (sortl l)).
Definition bubblesort l := whileDE bubblesort_body l.
Compute (steps 100 (bubblesort testseq)).
End bubblesort.
