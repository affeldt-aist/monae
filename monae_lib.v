From mathcomp Require Import all_ssreflect.
From mathcomp Require boolp.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* notations common to monad.v and category.v *)

Reserved Notation "m >>= f" (at level 49).
Reserved Notation "'do' x <- m ; e"
  (at level 60, x ident, m at level 200, e at level 60).
Reserved Notation "'do' x : T <- m ; e"
  (at level 60, x ident, m at level 200, e at level 60).
Reserved Notation "m >=> n" (at level 50).
Reserved Notation "n <=< m" (at level 50).
Reserved Notation "F # g" (at level 11).
Reserved Notation "f ~> g" (at level 51).
Reserved Notation "f \O g" (at level 50, format "f  \O  g").
Reserved Notation "F -| G" (at level 51, G at next level).
Reserved Notation "f \v g" (at level 50, format "'[v' f '/' \v  g ']'", left associativity).
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
Proof. rewrite boolp.funeqE; elim => // h t ih /=; by rewrite H2 ih. Qed.
Lemma foldr_universal_ext x : g x = foldr f r x.
Proof. by rewrite -(foldr_universal). Qed.
End universal.

Section fusion_law.
Variables (U : Type) (h : U -> R) (w : U) (g : T -> U -> U).
Hypothesis H1 : h w = r.
Hypothesis H2 : forall x y, h (g x y) = f x (h y).
Lemma foldr_fusion : h \o foldr g w = foldr f r.
Proof. rewrite boolp.funeqE; elim => // a b /= ih; by rewrite H2 ih. Qed.
Lemma foldr_fusion_ext x : (h \o foldr g w) x = foldr f r x.
Proof. by rewrite -foldr_fusion. Qed.
End fusion_law.

End fold.

Section curry.
Variables A B C : Type.
Implicit Types f : A -> B -> C.

Definition uncurry f := prod_curry f.

Lemma uncurryE f a b : (uncurry f) (a, b) = f a b. Proof. by []. Qed.

Definition curry (g : A * B -> C) : A -> B -> C := fun a b => g (a, b).

Lemma curryK : cancel curry uncurry.
Proof. by move=> f; rewrite boolp.funeqE; case. Qed.

Lemma uncurryK f : cancel uncurry curry.
Proof. by []. Qed.
End curry.

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
