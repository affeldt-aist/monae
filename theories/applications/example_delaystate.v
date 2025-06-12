(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2025 monae authors, license: LGPL-2.1-or-later               *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require boolp.
Require Import preamble hierarchy monad_lib Morphisms fail_lib state_lib.

(**md**************************************************************************)
(* # Example of use of the Delay-state monad                                  *)
(*                                                                            *)
(* ```                                                                        *)
(*     factds == factorial                                                    *)
(*   collatz1 == TODO                                                         *)
(*   collatz2 == TODO                                                         *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.
Local Open Scope do_notation.

Section factorial.
Variable M : delayStateMonad nat.

Definition factds_body m : M (unit + nat)%type :=
  do s <- get;
  match m with
  | O => do _ <- put s; Ret (inl tt)
  | m'.+1 => do _<- put (m * s); Ret (inr m')
  end.

Definition factds := while factds_body.

Lemma factdswB n : factds n ≈ do s <- get; do _ <- put (n`! * s); Ret tt.
Proof.
rewrite/factds/factds_body.
elim: n => /= [|n' IH].
rewrite fixpointwB/= !bindA.
apply: bindfwB => a.
by rewrite bindA bindretf/= mul1n.
rewrite/factds/factds_body fixpointwB/= bindA.
under eq_bind do rewrite bindA bindretf/=.
setoid_rewrite IH.
by under eq_bind do rewrite -!bindA putget !bindA bindretf -bindA
                            putput mulnA (mulnC n'`! _).
Qed.

End factorial.

Section collatz.
Variable M : delayStateMonad (seq nat).

Definition collatzs1_body nml
    : M ((nat * nat + nat * nat * nat) + nat * nat * nat)%type :=
  match nml with (n, m, l) =>
    do s' <- get;
    do _ <- put (n :: s');
    if n == 1 then if (l %% 4 == 1)
            then Ret (inl (inl (m, l)))
                 else do _ <- put [::]; Ret (inl (inr (m.+1, m.+1, 0)))
    else if (n %% 2 == 0) then Ret (inr (n./2, m, l.+1))
         else Ret (inr ((3 * n).+1, m, l.+1))
  end.

Definition collatzs1 n := while (while collatzs1_body) (n, n, 0).

Definition collatzs2_body nml : M ((nat * nat + nat * nat * nat))%type :=
  match nml with (n, m, l) =>
    do s' <- get;
    do _ <- put (n :: s');
    if (l %% 4 == 1) && (n == 1) then Ret (inl (m, l))
    else if (n == 1) then do _ <- put [::]; Ret (inr (m.+1, m.+1, 0))
         else if (n %% 2) == 0 then Ret (inr (n./2, m, l.+1))
              else Ret (inr ((3 * n).+1, m, l.+1))
  end.

Definition collatzs2 n := while collatzs2_body (n, n, 0).

Lemma collatzs1wB n : collatzs1 n ≈ collatzs2 n.
Proof.
rewrite /collatzs1 /collatzs2 -codiagonalwB.
apply: whilewB => -[[n' m] l].
rewrite /collatzs1_body /collatzs2_body.
have [Hl|?] := eqVneq (l %% 4) 1 => /=.
  have [?|] := eqVneq n' 1 => /=.
    rewrite Hl fmapE bindA.
    by under eq_bind do rewrite bindA bindretf.
  have [|] := eqVneq (n' %% 2) 0 => /=;
  rewrite fmapE/= bindA bindfwB//= => a;
  by rewrite bindA bindretf.
have [Hn'|_] := eqVneq n' 1 => /=.
  rewrite Hn' ifN //= fmapE bindA.
  by under eq_bind do rewrite bindA bindA bindretf.
have [|] := eqVneq (n' %% 2) 0 => /=;
  rewrite fmapE/= bindA;
  by under eq_bind do rewrite bindA bindretf.
Qed.

End collatz.
