From mathcomp Require Import all_ssreflect.
From HB Require Import structures.
Require Import monad_transformer hierarchy elgot_monad_model elgotexcept_model.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.
Local Open Scope do_notation.

Notation M := (MX unit Elgot).
Notation "a '≈e' b" := (wBisimDE a b) (at level 70).
Hint Extern 0 (wBisimDE _ _) => setoid_reflexivity.

(*Equality between hierarchy.while and elgot_monad_model.while*)
Lemma whileDEE A B (body : A -> M (B + A)) x :
  whileDE body x = while (@DEA Elgot _ _ \o body) x.
Proof. by []. Qed.

Lemma assertE X x (p : pred X) : @assert M _ p x ≈e Ret x <-> (p x) = true.
Proof.
split.
  rewrite/assert.
  case: (p x) => //.
  rewrite guardF bindfailf /wBisimDE.
  move/iff_wBisims_wBisim.
  move/iff_Terminates_wBret => contr.
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
case: (TerminatesP (whileDE f x)) =>
  [[[u' /iff_Terminates_wBret/iff_wBisims_wBisim Hs
    |x' /iff_Terminates_wBret [n Hs]]]|/iff_Diverges_wBisimspin Hs].
- by rewrite/bassert bindXE Hs !bindretf bindXE !bindretf.
- rewrite steps_Dnow in Hs.
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
    by rewrite !bindDmf => contr.
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
    rewrite /bassert !bindDmf.
    rewrite wBisim_DLater -bindXE.
    rewrite -{2}IH' /bassert.
    by rewrite /retX.
    move: HH.
    by move/assertE.
    rewrite/bassert !bindXE !bindA !bindDmf /= => Hd' Hs.
    apply wBLater.
  rewrite -!bindA -bindXE -/(bassert p _).
  apply: CIH.
  by rewrite -Hd' wBisim_DLater.
  apply: monotonicity_steps'.
  by rewrite /= /bassert bindA Hs.
rewrite !bindXE /bassert Hs.
apply: wBisim_trans.
apply iff_Diverges_wBisimspin.
  rewrite bindA.
  by apply: Diverges_bindspinf.
apply: wBisim_sym.
apply iff_Diverges_wBisimspin.
by apply Diverges_bindspinf.
Qed.

HB.instance Definition _ := @isMonadElgotAssert.Build M (@pcorrect).

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
