(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2020 monae authors, license: LGPL-2.1-or-later               *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require boolp.
Require ProofIrrelevance.

Definition proof_irr := boolp.Prop_irrelevance.

Definition eq_rect_eq :=
  @ProofIrrelevance.ProofIrrelevanceTheory.Eq_rect_eq.eq_rect_eq.

Definition funext_dep := boolp.functional_extensionality_dep.

(******************************************************************************)
(*      Shared notations and easy definitions/lemmas of general interest      *)
(*                                                                            *)
(*                foldr1                                                      *)
(*         curry/uncurry == currying for pairs                                *)
(*       curry3/uncurry3 == currying for triples                              *)
(*       comparePc, eqPc == computable version of equality axioms             *)
(*  coerce T1 (v : f T1) == some (f T2) if T1 = T2 and None o.w.              *)
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
Proof. by apply boolp.funext; elim => // h t ih /=; rewrite H2 ih. Qed.
Lemma foldr_universal_ext x : g x = foldr f r x.
Proof. by rewrite -(foldr_universal). Qed.
End universal.

Section fusion_law.
Variables (U : Type) (h : U -> R) (w : U) (g : T -> U -> U).
Hypothesis H1 : h w = r.
Hypothesis H2 : forall x y, h (g x y) = f x (h y).
Lemma foldr_fusion : h \o foldr g w = foldr f r.
Proof. by apply boolp.funext; elim => // a b /= ih; rewrite H2 ih. Qed.
Lemma foldr_fusion_ext x : (h \o foldr g w) x = foldr f r x.
Proof. by rewrite -foldr_fusion. Qed.
End fusion_law.

End fold.

Lemma foldl_revE (T R : Type) (f : R -> T -> R) (z : R) :
  foldl f z \o rev = foldr (fun x : T => f^~ x) z.
Proof. by apply boolp.funext => s; rewrite -foldl_rev. Qed.

Section curry.
Variables A B C : Type.
Implicit Types f : A -> B -> C.

Lemma uncurryE f a b : (uncurry f) (a, b) = f a b. Proof. by []. Qed.

Lemma curryE D a b (g : A * B -> C) (h : _ -> D) :
  h (curry g a b) = (h \o g) (a, b).
Proof. by []. Qed.

Lemma curryK : cancel (@curry A B C) uncurry.
Proof. by move=> f; apply boolp.funext => -[]. Qed.

Lemma uncurryK f : cancel (@uncurry A B C) curry.
Proof. by []. Qed.

Lemma eq_uncurry f g : f =1 g -> uncurry f = uncurry g.
Proof. by move=> fg; apply/boolp.funext => -[a b]/=; rewrite fg. Qed.

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

Lemma if_pair A B b (x : A) y (u : A) (v : B) :
  (if b then (x, y) else (u, v)) = (if b then x else u, if b then y else v).
Proof. by case: ifPn. Qed.

Lemma iteriSr T n (f : nat -> T -> T) x :
  iteri n.+1 f x = iteri n (f \o succn) (f 0 x).
Proof. by elim: n x => // n IH x /=; rewrite -IH. Qed.

Lemma iteriD T n m (f : nat -> T -> T) x :
  iteri (n + m) f x = iteri m (f \o addn n) (iteri n f x).
Proof. by elim: n x f => // n IH x f; rewrite addSn iteriSr IH iteriSr. Qed.

Section nth_error.
Context [T : Type] (def : T) (st : seq T).

(* Basic lemmas for standard library's nth_error *)
Local Notation nth_error := List.nth_error.

Lemma nth_error_set_nth n x : nth_error (set_nth def st n x) n = Some x.
Proof.
elim: n st => [|z IH] [] // {IH}.
elim: z.+1 => [|n <-] //=.
by rewrite set_nth_nil.
Qed.

Lemma nth_error_rcons_size b : nth_error (rcons st b) (size st) = Some b.
Proof. by elim: st. Qed.

Lemma nth_error_rcons_some n a b :
  nth_error st n = Some a -> nth_error (rcons st b) n = Some a.
Proof. by elim: n st => [|n IH] []. Qed.

Lemma nth_error_set_nth_id n a :
  nth_error st n = Some a -> set_nth def st n a = st.
Proof. by elim: n st => [|n IH] [] //= b st'; [case=> -> | move/IH ->]. Qed.

Lemma nth_error_set_nth_other m n a b :
  m != n ->
  nth_error st m = Some a ->
  nth_error (set_nth def st n b) m = Some a.
Proof.
elim: m st n => [|m IH] [|c st'] [|n] //=; rewrite eqSS => *; exact: IH.
Qed.

Lemma nth_error_set_nth_none m n a b :
  nth_error st m = None ->
  nth_error st n = Some a ->
  nth_error (set_nth def st n b) m = None.
Proof. by elim: m st n => [|m IH] [|c st'] [|n] //=; apply IH. Qed.

Lemma nth_error_size n a : nth_error st n = Some a -> n < size st.
Proof. by elim: n st => [|n IH] [|c st'] //= /IH. Qed.

Lemma nth_error_size_set_nth n a b :
  nth_error st n = Some a -> size (set_nth def st n b) = size st.
Proof. by rewrite size_set_nth => /nth_error_size /maxn_idPr. Qed.

Lemma set_nth_rcons a b : set_nth def (rcons st a) (size st) b = rcons st b.
Proof. by elim: st => //= c st' ->. Qed.

Lemma nth_error_set_nth_rcons n a b c :
  nth_error st n = Some a ->
  set_nth def (rcons st c) n b = rcons (set_nth def st n b) c.
Proof. by elim: n st => [|n IH] [|d st'] //= /IH ->. Qed.
End nth_error.
Arguments nth_error_size {T st n a}.

(* Computable equality axioms *)
Section computable_eqtype.
Definition comparePc T (eq_dec : comparable T) : Equality.axiom eq_dec :=
  fun x y => match eq_dec x y as s return reflect (x = y) s with
  | left a => ReflectT (x = y) a
  | right b => ReflectF (x = y) b
  end.
Definition eqPc (E : eqType) : Equality.axiom (@eq_op E) :=
  match E with EqType sort (EqMixin op a) => a end.
End computable_eqtype.

Section coerce.
Variables (X : eqType) (f : X -> Type).

Definition coerce (T1 T2 : X) (v : f T1) : option (f T2) :=
  if @eqPc _ T1 T2 is ReflectT H then Some (eq_rect _ _ v _ H) else None.

Lemma coerce_sym (T T' : X) (s : f T) (s' : f T') : coerce T' s -> coerce T s'.
Proof.
by rewrite /coerce; case: eqPc => //= h; case: eqPc => //; rewrite h; auto.
Qed.

Lemma coerce_Some (T : X) (s : f T) : coerce T s = Some s.
Proof.
by rewrite /coerce; case: eqPc => /= [?|]; [rewrite -eq_rect_eq|auto].
Qed.

Lemma coerce_eq (T T' : X) (s : f T) : coerce T' s -> T = T'.
Proof. by rewrite /coerce; case: eqPc. Qed.

Lemma coerce_None (T T' : X) (s : f T) : T != T' -> coerce T' s = None.
Proof. by rewrite /coerce; case: eqPc. Qed.

End coerce.
