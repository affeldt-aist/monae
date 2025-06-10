(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2025 monae authors, license: LGPL-2.1-or-later               *)
From mathcomp Require Import all_ssreflect.
Require Import hierarchy.

(**md**************************************************************************)
(* # Applications of the Delay-assert monad                                   *)
(*                                                                            *)
(* ```                                                                        *)
(*   bubblesort == TODO                                                       *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.
Local Open Scope do_notation.

Section bubblesort.
Variable M : delayAssertMonad.

Fixpoint sortl (l : seq nat) :=
  if l is n :: tl then
    (if tl is m :: tl' then
       (if m < n then
          m :: n :: sortl tl'
        else n :: sortl tl)
     else l)
  else nil.

Definition bubblesort_body (l : seq nat) : M (seq nat + seq nat)%type :=
  if l == sortl l then Ret (inl l) else Ret (inr (sortl l)).

Definition bubblesort l := while bubblesort_body l.

Lemma sortl_length l : size l = size (sortl l).
Proof.
move Hlen: (size l) => n.
elim: n {-2}n (leqnn n) l Hlen => n.
  rewrite leqn0 => /eqP -> l.
  by move/size0nil => ->.
move=> IH m Hmn.
move=> [|h] //=.
move=> [|k tl] // Hs.
have [hk|kh] := leqP h k.
  rewrite [k :: tl]lock/= -lock -Hs.
  congr S.
  rewrite -(IH (size (k :: tl))) //.
  by rewrite -(leq_add2r 1 _ _) !addn1 Hs.
rewrite -Hs [k :: tl]lock/= -lock -(IH (size tl)) //.
by move: Hmn; rewrite -Hs/= ltnS; exact: ltnW.
Qed.

Definition sizelE (l : seq nat) : pred (seq nat) := fun l' => size l == size l'.

Theorem bubblesort_length l : bassert (sizelE l) (bubblesort l) ≈ bubblesort l.
Proof.
apply: pcorrect.
  by rewrite assertE /sizelE eq_refl guardT bindskipf.
move=> l' Inv.
rewrite /bubblesort_body.
case: ifP => /eqP H.
  by rewrite bindretf/= bindretf.
move: Inv.
rewrite !bindretf/= !assertE !/sizelE (sortl_length l').
rewrite /guard; case: ifP => _.
  by rewrite !bindskipf.
rewrite !bindfailf => contr.
pose f := fun (_ : seq nat) => @ret M _ (sortl l').
by rewrite -(bindfailf _ _ f) contr bindretf.
Qed.

End bubblesort.
