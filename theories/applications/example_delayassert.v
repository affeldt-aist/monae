(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2025 monae authors, license: LGPL-2.1-or-later               *)
From mathcomp Require Import all_ssreflect.
Require Import hierarchy.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.
Local Open Scope do_notation.

Section bubblesort.
Variable M : delayAssertMonad.

Fixpoint sortl (l : seq nat) :=
  match l with
  | nil => nil
  | n :: tl => match tl with
              | nil => l
              | m :: tl' => if m < n then m :: n :: sortl tl'
                                    else n :: sortl tl
              end
  end.

Definition bubblesort_body (l : seq nat) : M (seq nat + seq nat)%type :=
  if l == sortl l then Ret (inl l) else Ret (inr (sortl l)).

Definition bubblesort l := while bubblesort_body l.

Definition sizelE (l : seq nat) : pred (seq nat) := fun l' => size l == size l'.

Lemma sizeE (n : nat) l : size (n :: l) = (size l).+1.
Proof. by []. Qed.

Lemma sortl_length (l : seq nat) : size l = size (sortl l).
Proof.
move Hlen: (size l) => n.
elim: n {-2}n (leqnn n) l Hlen => n.
  rewrite leqn0 => /eqP H0 l.
  rewrite H0.
  move/size0nil => -> //.
move => IH m Hmn l.
case: l => [|h tl] //=.
case: tl => [|k tl] // Hs.
have [Hhk|Hkh] := (leqP h k).
  rewrite sizeE -Hs.
  apply: eq_S.
  rewrite -(IH (size (k :: tl))) //.
    by rewrite -(leq_add2r 1 _ _) !addn1 Hs.
rewrite -Hs !sizeE -(IH (size tl)) //.
move: Hmn.
rewrite -Hs -addn1 -(addn1 n) (leq_add2r 1 _ _)/=.
exact: ltnW.
Qed.

Theorem bubblesort_length l : bassert (sizelE l) (bubblesort l) ≈ bubblesort l.
Proof.
apply: pcorrect.
  by rewrite assertE /sizelE eq_refl guardT bindskipf.
move => l' Inv.
rewrite/bubblesort_body.
case: ifP => /eqP H.
  by rewrite bindretf/= bindretf/=.
move: Inv.
rewrite !bindretf/= !assertE !/sizelE (sortl_length l') /guard.
case: ifP => _.
  by rewrite !bindskipf.
rewrite !bindfailf => contr.
pose f := fun (_ :seq nat) => @ret M _ (sortl l').
by rewrite -(bindfailf _ _ f) contr bindretf.
Qed.

End bubblesort.
