(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2025 monae authors, license: LGPL-2.1-or-later               *)
From mathcomp Require Import all_ssreflect ssralg ssrint.
Require Import ipreamble ihierarchy imonad_lib ialt_lib ifail_lib.

(**md**************************************************************************)
(* # Fast product example                                                     *)
(*                                                                            *)
(******************************************************************************)

Local Open Scope ring_scope.
Local Open Scope monae_scope.

Section work.
Variable M : failMonad.
Local Open Scope mprog.

Definition work s : M nat := if O \in s then fail else Ret (product s).

Definition next n (mx : M _) := if n == 0 then fail else fmap (muln n) mx.

(* work refined to eliminate multiple traversals *)
Lemma workE : work = foldr next (Ret 1%N).
Proof.
apply foldr_universal => // h tl; rewrite /next; case: ifPn => [/eqP -> //| h0].
by rewrite /work inE eq_sym (negbTE h0) [_ || _]/= fmap_if fmap_fail.
Qed.

End work.
Arguments work {M}.

(* same presentation as:                                                      *)
(* - J. Gibbons, R. Hinze, Just do it: simple monadic equational reasoning,   *)
(* ICFP 2011                                                                  *)
Section fastproductICFP2011.
Variable M : exceptMonad.

Definition fastprod s : M _ := catch (work s) (Ret O).

(* fastprod is pure, never throwing an unhandled exception *)
Lemma fastprodE s : fastprod s = Ret (product s).
Proof.
rewrite /fastprod /work fun_if if_arg catchfailm.
by rewrite catchret; case: ifPn => // /product0 <-.
Qed.

End fastproductICFP2011.

Section fastprod.
Variable M : exceptMonad.
Local Open Scope mprog.

Definition fastprod' s := catch (foldr (next M) (Ret 1%N) s) (Ret 0%N).
Definition failprod s : M _ := if 0 \in s then fail else Ret (product s).

Lemma fastprod'E s : fastprod' s = Ret (product s).
Proof.
rewrite /fastprod' /work.
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
