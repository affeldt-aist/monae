(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2020 monae authors, license: LGPL-2.1-or-later               *)
From mathcomp Require Import all_ssreflect.
Require ProofIrrelevance FunctionalExtensionality.

Definition funext := @FunctionalExtensionality.functional_extensionality.

Definition proof_irr := @ProofIrrelevance.proof_irrelevance.

Definition eq_rect_eq := @ProofIrrelevance.ProofIrrelevanceTheory.Eq_rect_eq.eq_rect_eq.

Definition funext_dep := @FunctionalExtensionality.functional_extensionality_dep.

(******************************************************************************)
(*      Shared notations and easy definitions/lemmas of general interest      *)
(*                                                                            *)
(*    curry/uncurry == currying for pairs                                     *)
(*  curry3/uncurry3 == currying for triples                                   *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* notations common to hierarchy.v and category.v *)

Reserved Notation "m >>= f" (at level 49).
Reserved Notation "'do' x <- m ; e"
  (at level 60, x name, m at level 200, e at level 60).
Reserved Notation "'do' x : T <- m ; e"
  (at level 60, x name, m at level 200, e at level 60).
Reserved Notation "m >=> n" (at level 50).
Reserved Notation "n <=< m" (at level 50).
Reserved Notation "F # g" (at level 11).
Reserved Notation "f ~> g" (at level 51).
Reserved Notation "f \O g" (at level 50, format "f  \O  g").
Reserved Notation "F -| G" (at level 51, G at next level).
Reserved Notation "f \v g" (at level 50, format "'[v' f '/' \v  g ']'", left associativity).
Reserved Notation "f \h g" (at level 50, format "f  \h  g").
Reserved Notation "l \\ p" (at level 50).

(* generic Haskell-like functions and notations *)

Notation "l \\ p" := ([seq x <- l | x \notin p]).

Definition foldr1 (A : Type) (def : A) (f : A -> A -> A) (s : seq A) :=
  match s with
    | [::] => def
    | [:: h] => h
    | h :: h' :: t => foldr f h [:: h' & t]
  end.

Definition cp {A B} (x : seq A) (y : seq B) := [seq (x', y') | x' <- x, y' <- y].

Lemma cp1 A B (a : A) (s : seq B) : cp [:: a] s = map (fun b => (a, b)) s.
Proof. by  elim: s => // h t /= <-. Qed.

Definition zipWith {A B C} (op : A -> B -> C) a b : seq C :=
  map (fun x => op x.1 x.2) (zip a b).

Section fold.
Variables (T R : Type) (f : T -> R -> R) (r : R).

Section universal.
Variable (g : seq T -> R).
Hypothesis H1 : g nil = r.
Hypothesis H2 : forall h t, g (h :: t) = f h (g t).
Lemma foldr_universal : g = foldr f r.
Proof. apply funext; elim => // h t ih /=; by rewrite H2 ih. Qed.
Lemma foldr_universal_ext x : g x = foldr f r x.
Proof. by rewrite -(foldr_universal). Qed.
End universal.

Section fusion_law.
Variables (U : Type) (h : U -> R) (w : U) (g : T -> U -> U).
Hypothesis H1 : h w = r.
Hypothesis H2 : forall x y, h (g x y) = f x (h y).
Lemma foldr_fusion : h \o foldr g w = foldr f r.
Proof. apply funext; elim => // a b /= ih; by rewrite H2 ih. Qed.
Lemma foldr_fusion_ext x : (h \o foldr g w) x = foldr f r x.
Proof. by rewrite -foldr_fusion. Qed.
End fusion_law.

End fold.

Lemma foldl_revE (T R : Type) (f : R -> T -> R) (z : R) :
  foldl f z \o rev = foldr (fun x : T => f^~ x) z.
Proof. by apply funext => s; rewrite -foldl_rev. Qed.

Section curry.
Variables A B C : Type.
Implicit Types f : A -> B -> C.

Lemma uncurryE f a b : (uncurry f) (a, b) = f a b. Proof. by []. Qed.

Lemma curryE D a b (g : A * B -> C) (h : _ -> D) :
  h (curry g a b) = (h \o g) (a, b).
Proof. by []. Qed.

Lemma curryK : cancel (@curry A B C) uncurry.
Proof. by move=> f; apply funext => -[]. Qed.

Lemma uncurryK f : cancel (@uncurry A B C) curry.
Proof. by []. Qed.
End curry.

Section curry3.
Variables A B C D : Type.

Definition uncurry3 (f : A -> B -> C -> D) (x : A * B * C) :=
  let '(a, b, c) := x in f a b c.

Definition curry3 (f : A * B * C -> D) := fun a b c => f (a, b, c).
End curry3.

Definition ucat {A} := uncurry (@cat A).

Definition uaddn := uncurry addn.

Lemma uaddnE n m : uaddn (n, m) = n + m. Proof. by rewrite /uaddn uncurryE. Qed.

Definition const A B (b : B) := fun _ : A => b.

Definition wrap {A} (a : A) := [:: a].

Fixpoint scanl A B (op : B -> A -> B) (b : B) (s : seq A) : seq B :=
  if s isn't x :: xs then [::] else (op b x) :: scanl op (op b x) xs.

Lemma compA {A B C D} (f : C -> D) (g : B -> C) (h : A -> B) :
  f \o (g \o h) = (f \o g) \o h.
Proof. by []. Qed.

Lemma compfid A B (f : A -> B) : f \o id = f. Proof. by []. Qed.

Lemma compidf A B (f : A -> B) : id \o f = f. Proof. by []. Qed.

Lemma compE A B C (g : B -> C) (f : A -> B) a : (g \o f) a = g (f a).
Proof. by []. Qed.
