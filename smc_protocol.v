From mathcomp Require Import all_ssreflect.
From mathcomp Require boolp.

Require Import Bvector.
Require Import ZArith.
Require Import Zdigits.
Require Export Zpower.
Require Import Lia.
Require Import Basics.
Require Import hierarchy.

Definition bvectorCapacity := 32.

Inductive smcfull : Set :=
| Int of Z.

Definition smcpartial : UU0 := Bvector (S bvectorCapacity).

Definition smclocalval : UU0 := (smcfull * smcpartial).

(* Ra, Rb, ra, rb *)
(* Assume that:
   1. Ra, Rb are random vectors
   2. ra is a random number
   3. rb = Ra x Rb^t - ra
*)
Definition commodity : UU0 := (smcpartial * smcpartial * Z * Z).

Definition get_Ra (c : commodity ) : smcpartial :=
	match c with
	| (Ra, _, _, _) => Ra
	end.
	
Definition get_Rb (c : commodity ) : smcpartial :=
	match c with
	| (_, Rb, _, _) => Rb
	end.

Definition get_ra (c : commodity ) : Z :=
	match c with
	| (_, _, ra, _) => ra
	end.

Definition get_rb (c : commodity ) : Z :=
	match c with
	| (_, _, _, rb) => rb
	end.

Definition get_full (s : smclocalval) : smcfull := fst s.
Definition get_partial (s : smclocalval) : smcpartial := snd s.

Definition build_partial (s : smclocalval) : smclocalval :=
	(get_full s,
		match (get_full s) with
		| Int i => Z_to_two_compl bvectorCapacity i
		end
	).

Definition add_partial (a : smcpartial) (b : smcpartial) : smcpartial :=
	Z_to_two_compl bvectorCapacity (Z.add (two_compl_value bvectorCapacity a) (two_compl_value bvectorCapacity b)).


(* Dot product of two bit vectors and the result is a Z,
   and then still return the result as a bit vector by the `Z_to_two_compl`
   per the SMC requirement that computation parties hold partial results of SMC computations .
*)
Definition dot_product (a : smcpartial) (b : smcpartial) : smcpartial :=
	a.  (*TODO: define it later*)

Definition only_partial (p : smcpartial) : smclocalval :=
	(Int 0, p).