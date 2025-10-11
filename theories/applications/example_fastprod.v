(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2025 monae authors, license: LGPL-2.1-or-later               *)
From mathcomp Require Import all_ssreflect ssralg ssrint.
From mathcomp Require boolp.
Require Import preamble hierarchy monad_lib alt_lib fail_lib state_lib.

(**md**************************************************************************)
(* # Fast product example                                                     *)
(*                                                                            *)
(* references:                                                                *)
(* - J. Gibbons, R. Hinze, Just do it: simple monadic equational reasoning,   *)
(* ICFP 2011                                                                  *)
(******************************************************************************)

Local Open Scope ring_scope.
Local Open Scope monae_scope.

Section fastprod.
Variable M : exceptMonad.
Local Open Scope mprog.

Let next n (mx : M _) := if n == 0 then fail else fmap (muln n) mx.
Definition fastprod s := catch (foldr next (Ret 1) s) (Ret 0).
Definition failprod s : M _ := if 0 \in s then fail else Ret (product s).

Lemma fmap_ret (A B : UU0) (f : A -> B) a : (M # f) (Ret a) = Ret (f a).
Proof. by rewrite fmapE bindretf. Qed.

Lemma fastprodE s : fastprod s = Ret (product s).
Proof.
rewrite /fastprod /work.
rewrite -(foldr_universal (g:=failprod)) //=.
  rewrite /failprod.
  rewrite fun_if if_arg.
  rewrite catchfailm catchret.
  case: ifPn => // s0.
  by rewrite product0.
rewrite /failprod /next => n s'.
rewrite inE eq_sym.
case: (n == 0) => //=.
by rewrite [RHS]fun_if fmap_fail fmap_ret.
Qed.
End fastprod.
