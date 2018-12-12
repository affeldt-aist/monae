(*
  Concrete examples of programs and their small-step and denotational semantics.
*)

Require Import ZArith List ssreflect.
Import ListNotations.
Require Import monad state_monad trace_monad.
Require Import smallstep smallstep_monad monad_model.

Notation "'eT' x y" := (@existT _ _ x y) (at level 200).
Notation "'e' x" := (@exist _ _ x _) (at level 200).

Definition p_nonce : program nat :=
  p_do n <- p_get;
  p_do _ <- p_put (S n);
  p_do _ <- p_mark n;
  p_ret n.

Let M := @ModelStateTraceRun.mk.

Eval unfold denote, p_nonce in denote (M nat nat) nat p_nonce.

Definition nonce : M nat nat nat :=
  do n : nat <- stGet;
  do _ : unit <- stPut (S n);
  do _ : unit <- stMark n;
  Ret n.

Compute nonce (0, []).
Compute (denote (M nat nat) nat p_nonce) (0, []).
Compute run_ss p_nonce 0.

Remark denote_p_nonce : denote (M nat nat) nat p_nonce = nonce.
Proof. by []. Qed.

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
Compute (denote (M nat nat) bool p_nonce_twice) (0, []).
Compute run_ss p_nonce_twice 0.

Remark denote_p_nonce_twice :
  denote (M nat nat) bool p_nonce_twice = nonce_twice.
Proof. by []. Qed.

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
Compute (denote (M nat bool) unit (p_countdown 100)) (5, []).
Compute run_ss (p_countdown 100) 5.

Remark denote_countdown fuel :
  denote (M nat bool) unit (p_countdown fuel) = countdown fuel.
Proof. by elim: fuel => //= n ->. Qed.

Example p_multiply (a b : nat) : program (T := unit) unit :=
  p_do _ <- p_put 0 ;
  p_repeat b (
    p_do x <- p_get ;
    p_put (a + x)
  ).

Compute run_ss (p_multiply 3 7) 0.

Example p_division (a b : nat) : program (T := unit) unit :=
  p_do _ <- p_put (a, 0);
  p_while a (fun s => b <=? fst s) (
    p_do s <- p_get ;
    p_put (fst s - b, S (snd s))
  ).

Compute run_ss (p_division 22 7) (0, 0).

Compute run_s_n 15 (p_division 22 7) (stop unit) (0, 0).
