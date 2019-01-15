Require Import FunctionalExtensionality Reals.
Require Import ssreflect ssrmatching ssrfun ssrbool.
From mathcomp Require Import eqtype ssrnat seq choice fintype tuple finset.

From infotheo Require Import proba ssr_ext ssrR Reals_ext.

Require Import proba_monad. (* TODO(rei): essentially to use Prob.t *)

(*
  This file duplicates the hierarchy of monads using
  functor of type finType -> Type instead of Type -> Type.
  The intent is to be able to use MathComp-compatible libraries
  (MathComp's finset, infotheo's proba) to build concrete models
  (see relmonad_model.v).

  Contents:
  - Module relLaws.
      the algebraic laws from monad.v for monads with a finite type
  - Module relMonad.
  - Module relMonadProb.
  - Module relMonadFail.
  - Module relMonadAlt.
  - Module relMonadAltCI.
  - Module relMonadNondet.
  - Module relMonadAltProb.
  - Module relMonadState.
  - Module relMonadNondetState.

*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "m >>= f" (at level 50).
Reserved Notation "'do' x <- m ; e"
  (at level 60, x ident, m at level 200, e at level 60).
Reserved Notation "x '[~]' y" (at level 50).

Module relLaws.
Section rellaws.
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

End rellaws.
End relLaws.

Module relMonad.
Record class_of (m : finType -> Type) : Type := Class {
  ret : forall A : finType, A -> m A;
  bind : forall A B : finType, m A -> (A -> m B) -> m B ;
  _ : relLaws.left_neutral bind ret ;
  _ : relLaws.right_neutral bind ret ;
  _ : relLaws.associative bind }.
Record t : Type := Pack { m : finType -> Type; class : class_of m }.
Module Exports.
Definition Bind (M : t) A B : m M A -> (A -> m M B) -> m M B :=
  let: Pack _ (Class _ x _ _ _) := M in x A B.
Arguments Bind {M A B} : simpl never.
Definition Ret (M : t) (A : finType) : A -> m M A :=
  let: Pack _ (Class x _ _ _ _) := M in x A.
Arguments Ret {M A} : simpl never.
Notation "m >>= f" := (Bind m f).
Notation relmonad := t.
Coercion m : relmonad >-> Funclass.
End Exports.
End relMonad.
Export relMonad.Exports.

Notation "'do' x <- m ; e" := (m >>= (fun x => e)).
Notation "m >> f" := (m >>= fun _ => f) (at level 50).
Definition skip M := @Ret M _ tt.
Arguments skip {M} : simpl never.

Local Open Scope reals_ext_scope.

Module relMonadProb.
Record mixin_of (m : relMonad.t) : Type := Mixin {
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
  _ : forall p, relLaws.bind_left_distributive (@Bind m) (choice p) ;
} .
Record class_of (m : finType -> Type) := Class {
  base : relMonad.class_of m ; mixin : mixin_of (relMonad.Pack base) }.
Structure t := Pack { m : finType -> Type ; class : class_of m }.
End relMonadProb.

Module relMonadFail.
Record mixin_of (M : relmonad) : Type := Mixin {
  fail : forall A, M A ;
  (* exceptions are left-zeros of sequential composition *)
  _ : relLaws.left_zero (@Bind M) fail (* fail A >>= f = fail B *)
}.
Record class_of (m : finType -> Type) := Class {
  base : relMonad.class_of m ; mixin : mixin_of (relMonad.Pack base) }.
Structure t := Pack { m : finType -> Type ; class : class_of m }.
Definition baseType (M : t) := relMonad.Pack (base (class M)).
Module Exports.
Definition Fail (M : t) : forall A, m M A :=
  let: Pack _ (Class _ (Mixin x _)) := M return forall A, m M A in x.
Arguments Fail {M A} : simpl never.
Notation relfailMonad := t.
Coercion baseType : relfailMonad >-> relmonad.
Canonical baseType.
End Exports.
End relMonadFail.
Export relMonadFail.Exports.

Module relMonadAlt.
Record mixin_of (M : relmonad) : Type := Mixin {
  alt : forall A, M A -> M A -> M A ;
  _ : forall A, associative (@alt A) ;
  (* composition distributes leftwards over choice *)
  _ : relLaws.bind_left_distributive (@Bind M) alt
  (* in general, composition does not distribute rightwards over choice *)
  (* NB: no bindDr to accommodate both angelic and demonic interpretations of nondeterminism *)
}.
Record class_of (m : finType -> Type) : Type := Class {
  base : relMonad.class_of m ; mixin : mixin_of (relMonad.Pack base) }.
Structure t := Pack { m : finType -> Type ; class : class_of m }.
Definition baseType (M : t) := relMonad.Pack (base (class M)).
Module Exports.
Definition Alt M : forall A, m M A -> m M A -> m M A :=
  let: Pack _ (Class _ (Mixin x _ _)) := M
  return forall A, m M A -> m M A -> m M A in x.
Arguments Alt {M A} : simpl never.
Notation "'[~p]'" := (@Alt _). (* postfix notation *)
Notation "x '[~]' y" := (Alt x y). (* infix notation *)
Notation relaltMonad := t.
Coercion baseType : relaltMonad >-> relmonad.
Canonical baseType.
End Exports.
End relMonadAlt.
Export relMonadAlt.Exports.

Module relMonadAltCI.
Record mixin_of (M : finType -> Type) (op : forall A, M A -> M A -> M A) : Type := Mixin {
  _ : forall A, idempotent (op A) ;
  _ : forall A, commutative (op A)
}.
Record class_of (m : finType -> Type) : Type := Class {
  base : relMonadAlt.class_of m ;
  mixin : mixin_of (@Alt (relMonadAlt.Pack base)) }.
Structure t := Pack { m : finType -> Type ; class : class_of m }.
Definition baseType (M : t) := relMonadAlt.Pack (base (class M)).
Module Exports.
Notation relaltCIMonad := t.
Coercion baseType : relaltCIMonad >-> relaltMonad.
Canonical baseType.
End Exports.
End relMonadAltCI.
Export relMonadAltCI.Exports.

Module relMonadNondet.
Record mixin_of (M : relfailMonad) (a : forall A, M A -> M A -> M A) : Type :=
  Mixin { _ : relLaws.left_id (@Fail M) a ;
          _ : relLaws.right_id (@Fail M) a
}.
Record class_of (m : finType -> Type) : Type := Class {
  base : relMonadFail.class_of m ;
  base2 : relMonadAlt.mixin_of (relMonad.Pack (relMonadFail.base base)) ;
  mixin : @mixin_of (relMonadFail.Pack base) (relMonadAlt.alt base2)
}.
Structure t : Type := Pack { m : finType -> Type ; class : class_of m }.
Definition baseType (M : t) := relMonadFail.Pack (base (class M)).
Module Exports.
Notation relnondetMonad := t.
Coercion baseType : relnondetMonad >-> relfailMonad.
Canonical baseType.
Definition alt_of_nondet (M : relnondetMonad) : relaltMonad :=
  relMonadAlt.Pack (relMonadAlt.Class (base2 (class M))).
Canonical alt_of_nondet.
End Exports.
End relMonadNondet.
Export relMonadNondet.Exports.

Module relMonadAltProb.
Record mixin_of (M : relaltCIMonad) (a : prob -> forall A, M A -> M A -> M A) := Mixin {
  _ : forall A (p : prob),
    right_distributive (fun x y : M A => a p _ x y) (fun x y => Alt x y)
}.
Record class_of (m : finType -> Type) := Class {
  base : relMonadAltCI.class_of m ;
  base2 : relMonadProb.mixin_of (relMonad.Pack (relMonadAlt.base (relMonadAltCI.base base))) ;
  mixin : @mixin_of (relMonadAltCI.Pack base) (@relMonadProb.choice _ base2)
}.
Structure t : Type := Pack { m : finType -> Type ; class : class_of m }.
Definition baseType (M : t) : relaltCIMonad := relMonadAltCI.Pack (base (class M)).
Definition altType (M : t) : relaltMonad := relMonadAlt.Pack (relMonadAltCI.base (base (class M))).
Module Exports.
Notation relaltProbMonad := t.
Coercion baseType : relaltProbMonad >-> relaltCIMonad.
Canonical baseType.
Definition altprob_is_prob M :=
  relMonadProb.Pack (relMonadProb.Class (base2 (class M))).
Canonical altprob_is_prob.
Canonical altType.
End Exports.
End relMonadAltProb.
Export relMonadAltProb.Exports.

Module relMonadState.
Record mixin_of (S : finType) (M : relmonad) : Type := Mixin {
  get : M S ;
  put : S -> M unit_finType ;
  _ : forall s s', put s >> put s' = put s' ;
  _ : forall s, put s >> get = put s >> Ret s ;
  _ : get >>= put = skip ;
  _ : forall k : S -> S -> M S,
    get >>= (fun s => get >>= k s) = get >>= fun s => k s s
}.
Record class_of S (m : finType -> Type) := Class {
  base : relMonad.class_of m ; mixin : mixin_of S (relMonad.Pack base) }.
Structure t S : Type := Pack { m : finType -> Type ; class : class_of S m }.
(* inheritance *)
Definition baseType S (M : t S) := relMonad.Pack (base (class M)).
Module Exports.
Definition Get S (M : t S) : m M S :=
  let: Pack _ (Class _ (Mixin x _ _ _ _ _)) := M return m M S in x.
Arguments Get {S M} : simpl never.
Definition Put S (M : t S) : S -> m M unit_finType :=
  let: Pack _ (Class _ (Mixin _ x _ _ _ _)) := M return S -> m M unit_finType in x.
Arguments Put {S M} : simpl never.
Notation relstateMonad := t.
Coercion baseType : relstateMonad >-> relmonad.
Canonical baseType.
End Exports.
End relMonadState.
Export relMonadState.Exports.

Module relMonadNondetState.
Record mixin_of (M : relnondetMonad) : Type := Mixin {
  (* backtrackable state *)
  _ : relLaws.right_zero (@Bind M) (@Fail _) ;
  (* composition distributes rightwards over choice *)
  _ : relLaws.bind_right_distributive (@Bind M) [~p]
}.
Record class_of S (m : finType -> Type) : Type := Class {
  base : relMonadNondet.class_of m ;
  base2 : relMonadState.mixin_of S (relMonadFail.baseType (relMonadNondet.baseType (relMonadNondet.Pack base))) ;
  mixin : mixin_of (relMonadNondet.Pack base)
}.
Structure t S : Type := Pack { m : finType -> Type ; class : class_of S m }.
Definition baseType S (M : t S) := relMonadNondet.Pack (base (class M)).
Module Exports.
Notation relnondetStateMonad := t.
Coercion baseType : relnondetStateMonad >-> relnondetMonad.
Canonical baseType.
Definition state_of_nondetstate S (M : relnondetStateMonad S) :=
  relMonadState.Pack (relMonadState.Class (base2 (class M))).
Canonical state_of_nondetstate.
End Exports.
End relMonadNondetState.
Export relMonadNondetState.Exports.
