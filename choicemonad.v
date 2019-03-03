Require Import FunctionalExtensionality Reals.
Require Import ssreflect ssrmatching ssrfun ssrbool.
From mathcomp Require Import eqtype ssrnat seq choice fintype tuple finset.

From infotheo Require Import ssr_ext ssrR Reals_ext dist.

Reserved Notation "x <| p |> y" (format "x  <| p |>  y", at level 50).

(* wip:
  This file duplicates the hierarchy of monads using
  functor of type choiceType -> choiceType instead of Type -> Type.
  The intent is to be able to use MathComp-compatible libraries
  (MathComp's finmap, infotheo's dist) to build concrete models
  (see choicemonad_model.v).

  Contents:
  - Module choiceBindLaws.
      the algebraic laws from monad.v for monads with a choice type
  - Module choiceMonad.
  - Module choiceMonadProb.
  - Module choiceMonadFail.
  - Module choiceMonadAlt.
  - Module choiceMonadAltCI.
  - Module choiceMonadNondet.
  - Module choiceMonadAltProb.
  - Module relMonadState. TODO
  - Module relMonadNondetState. TODO

*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "m >>= f" (at level 50).
Reserved Notation "'do' x <- m ; e"
  (at level 60, x ident, m at level 200, e at level 60).
Reserved Notation "x '[~]' y" (at level 50).

Module choiceBindLaws.
Section choicebindlaws.
Variable M : choiceType -> choiceType.

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

Definition left_neutral (r : forall A : choiceType, A -> M A) := forall (A B : choiceType) (x : A) (f : A -> M B),
  r _ x >>= f = f x.

Definition right_neutral (r : forall A : choiceType, A -> M A) := forall A (m : M A),
  m >>= r _ = m.

Definition left_id (r : forall A, M A) (add : forall B, M B -> M B -> M B) := forall A (m : M A),
  add _ (r _) m = m.

Definition right_id (r : forall A, M A) (add : forall B, M B -> M B -> M B) := forall A (m : M A),
  add _ m (r _) = m.

End choicebindlaws.
End choiceBindLaws.

Module choiceMonad.
Record class_of (m : choiceType -> choiceType) : Type := Class {
  ret : forall A : choiceType, A -> m A;
  bind : forall A B : choiceType, m A -> (A -> m B) -> m B ;
  _ : choiceBindLaws.left_neutral bind ret ;
  _ : choiceBindLaws.right_neutral bind ret ;
  _ : choiceBindLaws.associative bind }.
Record t : Type := Pack { m : choiceType -> choiceType; class : class_of m }.
Module Exports.
Definition Bind (M : t) A B : m M A -> (A -> m M B) -> m M B :=
  let: Pack _ (Class _ x _ _ _) := M in x A B.
Arguments Bind {M A B} : simpl never.
Definition Ret (M : t) (A : choiceType) : A -> m M A :=
  let: Pack _ (Class x _ _ _ _) := M in x A.
Arguments Ret {M A} : simpl never.
Notation "m >>= f" := (Bind m f).
Notation choicemonad := t.
Coercion m : choicemonad >-> Funclass.
End Exports.
End choiceMonad.
Export choiceMonad.Exports.

Notation "'do' x <- m ; e" := (m >>= (fun x => e)).
Notation "m >> f" := (m >>= fun _ => f) (at level 50).
Definition skip M := @Ret M _ tt.
Arguments skip {M} : simpl never.

Local Open Scope reals_ext_scope.

Module choiceMonadProb.
Record mixin_of (m : choiceMonad.t) : Type := Mixin {
  choice : forall (p : prob) (A : choiceType), m A -> m A -> m A
           where "mx <| p |> my" := (choice p mx my) ;
  (* identity laws *)
  _ : forall (A : choiceType) (mx my : m A), mx <| `Pr 0 |> my = my ;
  _ : forall (A : choiceType) (mx my : m A), mx <| `Pr 1 |> my = mx ;
  (* skewed commutativity law *)
  _ : forall (A : choiceType) p (mx my : m A), mx <| p |> my = my <| `Pr p.~ |> mx ;
  _ : forall A p, idempotent (@choice p A) ;
  (* quasi associativity *)
  _ : forall (A : choiceType) (p q r s : prob) (mx my mz : m A),
    (p = r * s :> R /\ s.~ = p.~ * q.~)%R ->
    mx <| p |> (my <| q |> mz) = (mx <| r |> my) <| s |> mz ;
  (* composition distributes leftwards over [probabilistic] choice *)
  _ : forall p, choiceBindLaws.bind_left_distributive (@Bind m) (choice p) ;
} .
Record class_of (m : choiceType -> choiceType) := Class {
  base : choiceMonad.class_of m ; mixin : mixin_of (choiceMonad.Pack base) }.
Structure t := Pack { m : choiceType -> choiceType ; class : class_of m }.
End choiceMonadProb.

Module choiceMonadFail.
Record mixin_of (M : choicemonad) : Type := Mixin {
  fail : forall A, M A ;
  (* exceptions are left-zeros of sequential composition *)
  _ : choiceBindLaws.left_zero (@Bind M) fail (* fail A >>= f = fail B *)
}.
Record class_of (m : choiceType -> choiceType) := Class {
  base : choiceMonad.class_of m ; mixin : mixin_of (choiceMonad.Pack base) }.
Structure t := Pack { m : choiceType -> choiceType ; class : class_of m }.
Definition baseType (M : t) := choiceMonad.Pack (base (class M)).
Module Exports.
Definition Fail (M : t) : forall A, m M A :=
  let: Pack _ (Class _ (Mixin x _)) := M return forall A, m M A in x.
Arguments Fail {M A} : simpl never.
Notation choicefailMonad := t.
Coercion baseType : choicefailMonad >-> choicemonad.
Canonical baseType.
End Exports.
End choiceMonadFail.
Export choiceMonadFail.Exports.

Module choiceMonadAlt.
Record mixin_of (M : choicemonad) : Type := Mixin {
  alt : forall A, M A -> M A -> M A ;
  _ : forall A, associative (@alt A) ;
  (* composition distributes leftwards over choice *)
  _ : choiceBindLaws.bind_left_distributive (@Bind M) alt
  (* in general, composition does not distribute rightwards over choice *)
  (* NB: no bindDr to accommodate both angelic and demonic interpretations of nondeterminism *)
}.
Record class_of (m : choiceType -> choiceType) : Type := Class {
  base : choiceMonad.class_of m ; mixin : mixin_of (choiceMonad.Pack base) }.
Structure t := Pack { m : choiceType -> choiceType ; class : class_of m }.
Definition baseType (M : t) := choiceMonad.Pack (base (class M)).
Module Exports.
Definition Alt M : forall A, m M A -> m M A -> m M A :=
  let: Pack _ (Class _ (Mixin x _ _)) := M
  return forall A, m M A -> m M A -> m M A in x.
Arguments Alt {M A} : simpl never.
Notation "'[~p]'" := (@Alt _). (* postfix notation *)
Notation "x '[~]' y" := (Alt x y). (* infix notation *)
Notation choicealtMonad := t.
Coercion baseType : choicealtMonad >-> choicemonad.
Canonical baseType.
End Exports.
End choiceMonadAlt.
Export choiceMonadAlt.Exports.

Module choiceMonadAltCI.
Record mixin_of (M : choiceType -> choiceType) (op : forall A, M A -> M A -> M A) : Type := Mixin {
  _ : forall A, idempotent (op A) ;
  _ : forall A, commutative (op A)
}.
Record class_of (m : choiceType -> choiceType) : Type := Class {
  base : choiceMonadAlt.class_of m ;
  mixin : mixin_of (@Alt (choiceMonadAlt.Pack base)) }.
Structure t := Pack { m : choiceType -> choiceType ; class : class_of m }.
Definition baseType (M : t) := choiceMonadAlt.Pack (base (class M)).
Module Exports.
Notation choicealtCIMonad := t.
Coercion baseType : choicealtCIMonad >-> choicealtMonad.
Canonical baseType.
End Exports.
End choiceMonadAltCI.
Export choiceMonadAltCI.Exports.

Module choiceMonadNondet.
Record mixin_of (M : choicefailMonad) (a : forall A, M A -> M A -> M A) : Type :=
  Mixin { _ : choiceBindLaws.left_id (@Fail M) a ;
          _ : choiceBindLaws.right_id (@Fail M) a
}.
Record class_of (m : choiceType -> choiceType) : Type := Class {
  base : choiceMonadFail.class_of m ;
  base2 : choiceMonadAlt.mixin_of (choiceMonad.Pack (choiceMonadFail.base base)) ;
  mixin : @mixin_of (choiceMonadFail.Pack base) (choiceMonadAlt.alt base2)
}.
Structure t : Type := Pack { m : choiceType -> choiceType ; class : class_of m }.
Definition baseType (M : t) := choiceMonadFail.Pack (base (class M)).
Module Exports.
Notation choicenondetMonad := t.
Coercion baseType : choicenondetMonad >-> choicefailMonad.
Canonical baseType.
Definition alt_of_nondet (M : choicenondetMonad) : choicealtMonad :=
  choiceMonadAlt.Pack (choiceMonadAlt.Class (base2 (class M))).
Canonical alt_of_nondet.
End Exports.
End choiceMonadNondet.
Export choiceMonadNondet.Exports.

Module choiceMonadAltProb.
Record mixin_of (M : choicealtCIMonad) (a : prob -> forall A, M A -> M A -> M A) := Mixin {
  _ : forall A (p : prob),
    right_distributive (fun x y : M A => a p _ x y) (fun x y => Alt x y)
}.
Record class_of (m : choiceType -> choiceType) := Class {
  base : choiceMonadAltCI.class_of m ;
  base2 : choiceMonadProb.mixin_of (choiceMonad.Pack (choiceMonadAlt.base (choiceMonadAltCI.base base))) ;
  mixin : @mixin_of (choiceMonadAltCI.Pack base) (@choiceMonadProb.choice _ base2)
}.
Structure t : Type := Pack { m : choiceType -> choiceType ; class : class_of m }.
Definition baseType (M : t) : choicealtCIMonad := choiceMonadAltCI.Pack (base (class M)).
Definition altType (M : t) : choicealtMonad := choiceMonadAlt.Pack (choiceMonadAltCI.base (base (class M))).
Module Exports.
Notation choicealtProbMonad := t.
Coercion baseType : choicealtProbMonad >-> choicealtCIMonad.
Canonical baseType.
Definition altprob_is_prob M :=
  choiceMonadProb.Pack (choiceMonadProb.Class (base2 (class M))).
Canonical altprob_is_prob.
Canonical altType.
End Exports.
End choiceMonadAltProb.
Export choiceMonadAltProb.Exports.

(* TODO Module relMonadState.
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
  _ : relBindLaws.right_zero (@Bind M) (@Fail _) ;
  (* composition distributes rightwards over choice *)
  _ : relBindLaws.bind_right_distributive (@Bind M) [~p]
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
*)