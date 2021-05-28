Require Import ssreflect ssrmatching ssrfun ssrbool.
From mathcomp Require Import eqtype ssrnat seq choice fintype tuple.
Require Import monae_lib hierarchy monad_lib.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* wip (fischer2011jfp) *)

(* mzero <-> Fail, `mplus` <-> [~i] *)

Section section_22.

Local Open Scope monae.

Section coin_def.
Variable M : nondetMonad.

Definition coin : M bool := Ret false [~] Ret true.

Definition coin' := (do x <- coin ; do y <- coin ; guard (x + y > 0) >> Ret x)%Do.

(* proof of p.419 *)
Lemma coin'E : coin' = (@Fail M _ [~] Ret false) [~] (Ret true [~] Ret true) :> M bool.
Proof.
rewrite /coin' {1}/coin alt_bindDl 2!bindretf /coin 2!alt_bindDl !bindretf.
by rewrite /guard /= bindfailf.
Qed.

End coin_def.

End section_22.
Arguments coin {M}.

Module MonadShare.
Record mixin_of (M : nondetMonad) : Type := Mixin {
  op_share : forall A, M A -> M (M A) ;
  _ : forall A (a b : M A), op_share (a [~] b) = op_share a [~] op_share b
}.
Record class_of (m : Type -> Type) : Type := Class {
  base : MonadNondet.class_of m ;
  mixin : mixin_of (MonadNondet.Pack base)
}.
Structure t : Type := Pack { m : Type -> Type ; class : class_of m }.
Definition share M : forall A, m M A -> m M (m M A) :=
  let: Pack _ (Class _ (Mixin x _)) := M
  return forall A, m M A -> m M (m M A) in x.
Arguments share {M A} : simpl never.
Definition baseType (M : t) := MonadNondet.Pack (base (class M)).
Module Exports.
Notation Share := share.
Notation shareMonad := t.
Coercion baseType : shareMonad >-> nondetMonad.
Canonical baseType.
End Exports.
End MonadShare.
Export MonadShare.Exports.

Section monadshare_lemmas.
Variable M : shareMonad.
Lemma share_choice A (a b : M A) : Share (a [~] b) = (Share a : M (M A)) [~] Share b.
Proof. by case: M A a b => m [? []]. Qed.
End monadshare_lemmas.

Section section_32.

Definition duplicate {M : monad} {A} a : M (A * A)%type :=
  do u <- a ; do v <- a ; Ret (u, v).

Definition dup_coin_let {M : nondetMonad} : M _ := let x := coin in duplicate x.

Lemma dup_coin_letE M : @dup_coin_let M =
  (Ret (false, false) [~] Ret (false, true)) [~]
  (Ret (true, false) [~] Ret (true, true)).
Proof. by rewrite /dup_coin_let /duplicate /coin !(alt_bindDl,bindretf). Qed.

Definition dup_coin_bind {M : nondetMonad} : M _ :=
  do x <- coin; duplicate (Ret x).

Lemma dup_coin_bindE M : @ dup_coin_bind M =
  Ret (false, false) [~] Ret (true, true).
Proof.
rewrite /dup_coin_bind /coin /duplicate.
do 2 rewrite_ bindretf.
by rewrite alt_bindDl !bindretf.
Qed.

Definition dup_coin_share {M : shareMonad} :=
  do x <- (Share coin : M _) ; @duplicate M _ x.

Hypothesis Share_Ret_true : forall M : shareMonad, Share (Ret true : M _) = Ret (Ret true) :> M (M _).
Hypothesis Share_Ret_false : forall M : shareMonad, Share (Ret false : M _) = Ret (Ret false) :> M (M _).

Lemma dup_coin_shareE {M : shareMonad} : dup_coin_share = dup_coin_bind :> M _.
Proof.
rewrite /dup_coin_share /coin dup_coin_bindE share_choice.
rewrite alt_bindDl Share_Ret_true Share_Ret_false.
by rewrite 2!bindretf /duplicate !bindretf.
Qed.

Section zeros.

Variables (M : shareMonad).

Fail CoFixpoint zeros : M _ := do x : M _ <- Share zeros : M _; Ret 0 [~] x.

End zeros.

End section_32.
