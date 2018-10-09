(*
  Concrete examples of programs and their small-step and denotational semantics.
*)

Require Import ZArith List.
Import ListNotations.
Require Import monad state_monad trace_monad.
Require Import smallstep smallstep_monad trace_model.

Notation "'eT' x y" := (@existT _ _ x y) (at level 200).
Notation "'e' x" := (@exist _ _ x _) (at level 200).

Definition p_nonce : program nat :=
  p_do n <- p_get;
  p_do _ <- p_put (S n);
  p_do _ <- p_mark n;
  p_ret n.

Let M := @ModelStateTraceRunMonad.mk.

Eval unfold denotation, p_nonce in denotation (M nat nat) nat p_nonce.

Definition nonce : M nat nat nat :=
  do n : nat <- stGet;
  do _ : unit <- stPut (S n);
  do _ : unit <- stMark n;
  Ret n.

Compute nonce (0, []).
Compute (denotation (M nat nat) nat p_nonce) (0, []).
Compute run_ss p_nonce 0.

Remark denotation_nonce : denotation (M nat nat) nat p_nonce = nonce.
Proof.
reflexivity.
Qed.

Program Example p_nonce_twice : program bool :=
  p_do nonce <- p_ret (
    p_do n : nat <- p_get;
    p_do _ : unit <- p_put (S n);
    p_do _ : unit <- p_mark n;
    p_ret n ) ;
  p_do x <- nonce ;
  p_do y <- nonce ;
  p_ret (x =? y).

Example nonce_twice : M _ _ _ :=
  do nonce <- Ret (
    do n : nat <- stGet;
    do _ : unit <- stPut (S n);
    do _ : unit <- stMark n;
    Ret n ) ;
  do x <- nonce ;
  do y <- nonce ;
  Ret (Nat.eqb x y).

Compute nonce_twice (0, []).
Compute (denotation (M nat nat) bool p_nonce_twice) (0, []).
Compute run_ss p_nonce_twice 0.

Remark denotation_nonce_twice :
  denotation (M nat nat) bool p_nonce_twice = nonce_twice.
Proof.
reflexivity.
Qed.

Fixpoint countdown (fuel : nat) : M nat bool unit :=
  match fuel with
  | O => Ret tt
  | S fuel' =>
    do n <- stGet ;
    if (n =? 0) then
      stMark true
    else
      do _ <- stMark false ; do _ <- stPut (n-1) ; countdown fuel'
  end.

Fixpoint p_countdown (fuel : nat) : program unit :=
  match fuel with
  | O => p_ret tt
  | S fuel' =>
    p_do n <- p_get ;
    p_cond (n =? 0) (
      p_mark true
    ) (
      p_do _ <- p_mark false ; p_do _ <- p_put (n-1) ; p_countdown fuel'
    )
  end.

Compute (countdown 100) (5, []).
Compute (denotation (M nat bool) unit (p_countdown 100)) (5, []).
Compute run_ss (p_countdown 100) 5.

Remark denotation_countdown fuel :
  denotation (M nat bool) unit (p_countdown fuel) = countdown fuel.
Proof.
induction fuel as [ | fuel' IH ].
- reflexivity.
- cbn.
  rewrite IH.
  reflexivity.
Qed.
