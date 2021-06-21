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
Import Order.TTheory.
Local Open Scope monae_scope.
Local Open Scope tuple_ext_scope.

From infotheo Require Import ssrZ.
Require Import ZArith.

Section marray.
Variables (E : UU0) (M : arrayMonad E Z_eqType).
Variables (d : unit) (T : porderType d).

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
  aGet i >>= (fun x => aGet j >>= (fun y => aPut i y >> aPut j x)).

Fixpoint partl (p : T) (s : (seq T * seq T)%type) (xs : seq T): (seq T * seq T)%type :=
  match xs with
  | [::] => s
  | x :: xs => if x <= p then partl p (s.1 ++ [:: x], s.2) xs
                                   else partl p (s.1, s.2 ++ [:: x]) xs
  end.

Definition second {A B C} (f : B -> M C) (xy : (A * B)%type) := f xy.2 >>= (fun y' => Ret (xy.1, y')).

Program Fixpoint partl' (p : T) (s : (seq T * seq T)) (xs : seq T): M (seq T * seq T)%type :=
  match xs with
  | [::] => Ret s
  | x :: xs => if x <= p then qperm s.2 >>= (fun zs' => partl' p (s.1 ++ [:: x], s.2) xs)
                         else partl' p (s.1, s.2 ++ [:: x]) xs
  end.

Lemma ipartl_spec (i : Z) (p : E) (ys zs xs : seq E) (ipartl : E -> Z -> (nat * nat * nat)%type -> M (nat * nat)%type): 
  writeList i (ys ++ zs ++ xs) >> ipartl p i (size ys, size zs, size xs)
    `<=` second perm (partl p (ys, zs) xs) >>= write2L i.

Local Open Scope zarith_ext_scope.

Lemma writeList_cat (i : Z) (xs ys : seq E) :
  writeList i (xs ++ ys) = writeList i xs >> writeList (i + (size xs)%:Z) ys.
Proof.
elim: xs i => [|h t ih] i /=; first by rewrite bindretf addZ0.
by rewrite ih bindA -addZA add1Z natZS.
Qed.

End marray.
