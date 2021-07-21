(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2020 monae authors, license: LGPL-2.1-or-later               *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require boolp.
Require Import monae_lib hierarchy monad_lib fail_lib state_lib example_quicksort.
From infotheo Require Import ssr_ext.

(*******************************************************************************)
(*                                   wip                                       *)
(*******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope order_scope.
Import Order.Theory.
Local Open Scope monae_scope.
Local Open Scope tuple_ext_scope.

From infotheo Require Import ssrZ.
Require Import ZArith.

Section marray.
(* Variables (E : UU0) (M : arrayMonad E Z_eqType).
Variables (d : unit) (T : porderType d). *)

Variable (d : unit) (E : porderType d) (M : arrayMonad E Z_eqType).

Fixpoint readList (i : Z) (n : nat) : M (seq E) :=
  if n isn't k.+1 then Ret [::] else liftM2 cons (aget i) (readList (i + 1) k).

Fixpoint writeList (i : Z) (s : seq E) : M unit :=
  if s isn't x :: xs then Ret tt else aput i x >> writeList (i + 1) xs.

Definition writeL (i : Z) (s : seq E) := writeList i s >> Ret (size s).

Definition write2L (i : Z) '(s1, s2) :=
  writeList i (s1 ++ s2) >> Ret (size s1, size s2).

Definition write3L (i : Z) '(xs, ys, zs) :=
  writeList i (xs ++ ys ++ zs) >> Ret (size xs, size ys, size zs).

Definition swap (i j : Z) : M unit := 
  aget i >>= (fun x => aget j >>= (fun y => aput i y >> aput j x)).

Fixpoint partl (p : E) (s : (seq E * seq E)%type) (xs : seq E): (seq E * seq E)%type :=
  match xs with
  | [::] => s
  | x :: xs => if x <= p then partl p (s.1 ++ [:: x], s.2) xs
                         else partl p (s.1, s.2 ++ [:: x]) xs
  end.

Definition second {A B C} (f : B -> M C) (xy : (A * B)%type) := f xy.2 >>= (fun y' => Ret (xy.1, y')).

(* Program Fixpoint partl' (p : E) (s : (seq E * seq E * seq E)) : M (seq E * seq E)%type :=
  match s with
  | (ys, zs, [::]) => Ret (ys, zs)
  | (ys, zs, x :: xs) => if x <= p then (@qperm _ _ zs) >>= (fun zs' => partl' p (ys ++ [:: x], zs', xs))
                         else partl' p (ys, zs ++ [:: x], xs)
  end. *)

(* Definition dispatch (x p : E) '(ys, zs, xs) := 
  if x <= p then perm zs >>= (fun zs' => Ret (ys ++ [:: x], zs', xs))
            else perm (zs ++ [:: x]) >>= (fun zs' => Ret (ys, zs', zs)). *)

(* Lemma ipartl_spec (i : Z) (p : E) (ys zs xs : seq E) (ipartl : E -> Z -> (nat * nat * nat)%type -> M (nat * nat)%type): 
  writeList i (ys ++ zs ++ xs) >> ipartl p i (size ys, size zs, size xs)
    `<=` second perm (partl p (ys, zs) xs) >>= write2L i. *)

Local Open Scope zarith_ext_scope.

Lemma writeList_cat (i : Z) (xs ys : seq E) :
  writeList i (xs ++ ys) = writeList i xs >> writeList (i + (size xs)%:Z) ys.
Proof.
elim: xs i => [|h t ih] i /=; first by rewrite bindretf addZ0.
by rewrite ih bindA -addZA add1Z natZS.
Qed.

Fixpoint ipartl (p : E) (i : Z) (ny nz : nat) (nx : nat) : M (nat * nat)%type := 
  match nx with
  | 0 => Ret (ny, nz)
  | k.+1 => aget ((* i + *) (ny + nz)%:Z) >>= (fun x => (* TODO *)
         if x <= p then swap (i + ny%:Z) (i + ny%:Z + nz%:Z) >> ipartl p i (ny + 1) nz k
                   else ipartl p i ny (nz.+1) k)
  end.

(* Program Fixpoint iqsort (i : Z) (n : nat) : M unit := 
  match n with
  | 0 => Ret tt
  | n.+1 => aget i >>= (fun p =>
         ipartl p (i) 0 0 n >>= (fun '(ny, nz) =>
         swap i (i + ny%:Z) >>
         iqsort i ny >> iqsort (ny%:Z) nz))
  end. *)

(* Lemma lemma12 {i : Z} {xs : seq E} {p : E} : 
  writeList i xs >> iqsort i (size xs) `<=` _.
Proof. *)

(* Lemma lemma13 {i : Z} {ys : seq E} {p : E} : 
  perm ys >>= (fun ys' => writeList i (ys' ++ [:: p])) `>=` 
  writeList i (p :: ys) >> swap i (i + (size ys)%:Z).
Proof. *)
  
(* Qed. *)

End marray.


