Require Import FunctionalExtensionality Reals.
Require Import ssreflect ssrmatching ssrfun ssrbool.
From mathcomp Require Import eqtype ssrnat seq choice fintype tuple finset.

From infotheo Require Import proba ssr_ext.

Require Import proba_monad. (* TODO(rei): essentially to use Prob.t *)

(*
  This file duplicated the hierarchy of monads using
  functor of type finType -> Type instead of Type -> Type.
  The intent is to be able to use MathComp-compatible libraries
  (MathComp's finset, infotheo's proba) to build concrete models
  (see finmonad_model.v).

  Contents:
  - Module finLaws.
      the algebraic laws from monad.v for monads with a finite type
  - Module finMonad.
  - Module finMonadProb.
  - Module finMonadFail.
  - Module finMonadAlt.
  - Module finMonadNondet.
  - Module finMonadState.
  - Module finMonadNondetState.

*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "m >>= f" (at level 50).
Reserved Notation "'do' x <- m ; e"
  (at level 60, x ident, m at level 200, e at level 60).
Reserved Notation "x '[~]' y" (at level 50).

Module finLaws.
Section finlaws.
Variable M : finType -> Type.

Variable b : forall A B, M A -> (A -> M B) -> M B.

Local Notation "m >>= f" := (b m f).

Definition associative := forall A B C (m : M A) (f : A -> M B) (g : B -> M C),
  (m >>= f) >>= g = m >>= (fun x => (f x >>= g)).

Definition bind_right_distributive (add : forall B, M B -> M B -> M B) := forall A B,
  forall (m : M A) (k1 k2 : A -> M B),
    m >>= (fun x => add _ (k1 x) (k2 x)) = add _ (m >>= k1) (m >>= k2).

Definition bind_left_distributive (add : forall B, M B -> M B -> M B) := forall A B,
  forall (m1 m2 : M A) (k : A -> M B),
    (add _ m1 m2) >>= k = add _ (m1 >>= k) (m2 >>= k).

Definition right_zero (f : forall A, M A) :=
  forall A B (g : M B), g >>= (fun _ => f A) = f A.

Definition left_zero (f : forall A, M A) := forall A B g, f A >>= g = f B.

Definition left_neutral (r : forall A : finType, A -> M A) := forall (A B : finType) (x : A) (f : A -> M B),
  r _ x >>= f = f x.

Definition right_neutral (r : forall A : finType, A -> M A) := forall A (m : M A),
  m >>= r _ = m.

Definition left_id (r : forall A, M A) (add : forall B, M B -> M B -> M B) := forall A (m : M A),
  add _ (r _) m = m.

Definition right_id (r : forall A, M A) (add : forall B, M B -> M B -> M B) := forall A (m : M A),
  add _ m (r _) = m.

End finlaws.
End finLaws.

Module finMonad.
Record class_of (m : finType -> Type) : Type := Class {
  ret : forall A : finType, A -> m A;
  bind : forall A B : finType, m A -> (A -> m B) -> m B ;
  _ : finLaws.left_neutral bind ret ;
  _ : finLaws.right_neutral bind ret ;
  _ : finLaws.associative bind }.
Record t : Type := Pack { m : finType -> Type; class : class_of m }.
Module Exports.
Definition Bind (M : t) A B : m M A -> (A -> m M B) -> m M B :=
  let: Pack _ (Class _ x _ _ _) := M in x A B.
Arguments Bind {M A B} : simpl never.
Definition Ret (M : t) (A : finType) : A -> m M A :=
  let: Pack _ (Class x _ _ _ _) := M in x A.
Arguments Ret {M A} : simpl never.
Notation "m >>= f" := (Bind m f).
Notation finmonad := t.
Coercion m : finmonad >-> Funclass.
End Exports.
End finMonad.
Export finMonad.Exports.

Notation "'do' x <- m ; e" := (m >>= (fun x => e)).
Notation "m >> f" := (m >>= fun _ => f) (at level 50).
Definition skip M := @Ret M _ tt.
Arguments skip {M} : simpl never.

Module finMonadProb.
Record mixin_of (m : finMonad.t) : Type := Mixin {
  choice : forall (p : prob) (A : finType), m A -> m A -> m A
           where "mx <| p |> my" := (choice p mx my) ;
  (* identity laws *)
  _ : forall (A : finType) (mx my : m A), mx <| `Pr 0 |> my = my ;
  _ : forall (A : finType) (mx my : m A), mx <| `Pr 1 |> my = mx ;
  (* skewed commutativity law *)
  _ : forall (A : finType) p (mx my : m A), mx <| p |> my = my <| `Pr p.~ |> mx ;
  _ : forall A p, idempotent (@choice p A) ;
  (* quasi associativity *)
  _ : forall (A : finType) (p q r s : prob) (mx my mz : m A),
    (p = r * s :> R /\ s.~ = p.~ * q.~)%R ->
    mx <| p |> (my <| q |> mz) = (mx <| r |> my) <| s |> mz ;
  (* composition distributes leftwards over [probabilistic] choice *)
  _ : forall p, finLaws.bind_left_distributive (@Bind m) (choice p) ;
} .
Record class_of (m : finType -> Type) := Class {
  base : finMonad.class_of m ; mixin : mixin_of (finMonad.Pack base) }.
Structure t := Pack { m : finType -> Type ; class : class_of m }.
End finMonadProb.

Module finMonadFail.
Record mixin_of (M : finmonad) : Type := Mixin {
  fail : forall A, M A ;
  (* exceptions are left-zeros of sequential composition *)
  _ : finLaws.left_zero (@Bind M) fail (* fail A >>= f = fail B *)
}.
Record class_of (m : finType -> Type) := Class {
  base : finMonad.class_of m ; mixin : mixin_of (finMonad.Pack base) }.
Structure t := Pack { m : finType -> Type ; class : class_of m }.
Definition baseType (M : t) := finMonad.Pack (base (class M)).
Module Exports.
Definition Fail (M : t) : forall A, m M A :=
  let: Pack _ (Class _ (Mixin x _)) := M return forall A, m M A in x.
Arguments Fail {M A} : simpl never.
Notation finfailMonad := t.
Coercion baseType : finfailMonad >-> finmonad.
Canonical baseType.
End Exports.
End finMonadFail.
Export finMonadFail.Exports.

Module finMonadAlt.
Record mixin_of (M : finmonad) : Type := Mixin {
  alt : forall A, M A -> M A -> M A ;
  _ : forall A, associative (@alt A) ;
  (* composition distributes leftwards over choice *)
  _ : finLaws.bind_left_distributive (@Bind M) alt
  (* in general, composition does not distribute rightwards over choice *)
  (* NB: no bindDr to accommodate both angelic and demonic interpretations of nondeterminism *)
}.
Record class_of (m : finType -> Type) : Type := Class {
  base : finMonad.class_of m ; mixin : mixin_of (finMonad.Pack base) }.
Structure t := Pack { m : finType -> Type ; class : class_of m }.
Definition baseType (M : t) := finMonad.Pack (base (class M)).
Module Exports.
Definition Alt M : forall A, m M A -> m M A -> m M A :=
  let: Pack _ (Class _ (Mixin x _ _)) := M
  return forall A, m M A -> m M A -> m M A in x.
Arguments Alt {M A} : simpl never.
Notation "'[~p]'" := (@Alt _). (* postfix notation *)
Notation "x '[~]' y" := (Alt x y). (* infix notation *)
Notation finaltMonad := t.
Coercion baseType : finaltMonad >-> finmonad.
Canonical baseType.
End Exports.
End finMonadAlt.
Export finMonadAlt.Exports.

Module finMonadNondet.
Record mixin_of (M : finfailMonad) (a : forall A, M A -> M A -> M A) : Type :=
  Mixin { _ : finLaws.left_id (@Fail M) a ;
          _ : finLaws.right_id (@Fail M) a
}.
Record class_of (m : finType -> Type) : Type := Class {
  base : finMonadFail.class_of m ;
  base2 : finMonadAlt.mixin_of (finMonad.Pack (finMonadFail.base base)) ;
  mixin : @mixin_of (finMonadFail.Pack base) (finMonadAlt.alt base2)
}.
Structure t : Type := Pack { m : finType -> Type ; class : class_of m }.
Definition baseType (M : t) := finMonadFail.Pack (base (class M)).
Module Exports.
Notation finnondetMonad := t.
Coercion baseType : finnondetMonad >-> finfailMonad.
Canonical baseType.
Definition alt_of_nondet (M : finnondetMonad) : finaltMonad :=
  finMonadAlt.Pack (finMonadAlt.Class (base2 (class M))).
Canonical alt_of_nondet.
End Exports.
End finMonadNondet.
Export finMonadNondet.Exports.

Module finMonadState.
Record mixin_of (S : finType) (M : finmonad) : Type := Mixin {
  get : M S ;
  put : S -> M unit_finType ;
  _ : forall s s', put s >> put s' = put s' ;
  _ : forall s, put s >> get = put s >> Ret s ;
  _ : get >>= put = skip ;
  _ : forall k : S -> S -> M S,
    get >>= (fun s => get >>= k s) = get >>= fun s => k s s
}.
Record class_of S (m : finType -> Type) := Class {
  base : finMonad.class_of m ; mixin : mixin_of S (finMonad.Pack base) }.
Structure t S : Type := Pack { m : finType -> Type ; class : class_of S m }.
(* inheritance *)
Definition baseType S (M : t S) := finMonad.Pack (base (class M)).
Module Exports.
Definition Get S (M : t S) : m M S :=
  let: Pack _ (Class _ (Mixin x _ _ _ _ _)) := M return m M S in x.
Arguments Get {S M} : simpl never.
Definition Put S (M : t S) : S -> m M unit_finType :=
  let: Pack _ (Class _ (Mixin _ x _ _ _ _)) := M return S -> m M unit_finType in x.
Arguments Put {S M} : simpl never.
Notation finstateMonad := t.
Coercion baseType : finstateMonad >-> finmonad.
Canonical baseType.
End Exports.
End finMonadState.
Export finMonadState.Exports.

Module finMonadNondetState.
Record mixin_of (M : finnondetMonad) : Type := Mixin {
  (* backtrackable state *)
  _ : finLaws.right_zero (@Bind M) (@Fail _) ;
  (* composition distributes rightwards over choice *)
  _ : finLaws.bind_right_distributive (@Bind M) [~p]
}.
Record class_of S (m : finType -> Type) : Type := Class {
  base : finMonadNondet.class_of m ;
  base2 : finMonadState.mixin_of S (finMonadFail.baseType (finMonadNondet.baseType (finMonadNondet.Pack base))) ;
  mixin : mixin_of (finMonadNondet.Pack base)
}.
Structure t S : Type := Pack { m : finType -> Type ; class : class_of S m }.
Definition baseType S (M : t S) := finMonadNondet.Pack (base (class M)).
Module Exports.
Notation finnondetStateMonad := t.
Coercion baseType : finnondetStateMonad >-> finnondetMonad.
Canonical baseType.
Definition state_of_nondetstate S (M : finnondetStateMonad S) :=
  finMonadState.Pack (finMonadState.Class (base2 (class M))).
Canonical state_of_nondetstate.
End Exports.
End finMonadNondetState.
Export finMonadNondetState.Exports.
