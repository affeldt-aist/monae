From mathcomp Require Import all_ssreflect zify lra.
From monae Require Import preamble hierarchy monad_lib monad_model.

Set Implicit Arguments.

Local Open Scope do_notation.
Local Open Scope monae_scope.

Section with_cache.
Variable res : eqType.
Definition cache := nat -> option res.
Variable M : stateRunMonad cache idfun.
Variable f : nat -> res.

Definition update n v : M unit :=
  do c <- get; let c' x := if x == n then Some v else c x in put c'.

Definition lookup_or_compute n (m : M res) :=
  do c <- get;
  if c n is Some x then Ret x else
  do x <- m; do _ <- update n x; Ret x.

Definition f_trunc k n := if n < k then Some (f n) else None.

Definition goodcache k c := c = f_trunc k.

Definition R {X} k1 k2 (s : M X) (n : (idfun : monad) X) : Type :=
  forall c, goodcache k1 c ->
            (runStateT s c).1 = n /\ goodcache k2 (runStateT s c).2.

Lemma Rget k : R k k get (f_trunc k).
Proof.
move=> c Hc.
by rewrite runStateTget.
Qed.

Lemma Rret k A (a : A) : R k k (Ret a) a.
Proof.
move=> c Hc.
by rewrite runStateTret.
Qed.

Lemma Rupdate k : R k k.+1 (update k (f k)) tt.
Proof.
move=> c Hc.
rewrite /update runStateTbind runStateTget bindretf runStateTput /=.
split => //.
apply: boolp.funext => x.
rewrite Hc /f_trunc ltnS.
by case: ltngtP => // ->.
Qed.

Lemma Rbind k1 k2 k3 A B (m : M A) m' :
  R k1 k2 m m' -> forall (g : A -> M B) g',
      (R k2 k3 (g m') (g' m')) ->
      R k1 k3 (m >>= g) (m' >>= g').
Proof.
move=> Rmm' g g' Rgg' c Hc.
rewrite runStateTbind.
case: (Rmm' _ Hc).
case: (runStateT m c) => n2 c2 /= -> /[dup] Hc2 ->.
rewrite bindretf /=.
case: (Rgg' _ Hc2).
rewrite Hc2.
by move ->.
Qed.

Lemma Rlookup_or_compute k n (m : M res) :
  (k <= n -> R k n m (f n)) ->
  R k (maxn k n.+1) (lookup_or_compute n m) (f n).
Proof.
rewrite /lookup_or_compute => Rmm' /=.
have -> : f n = Ret (f_trunc k) >> Ret (f n) :> (idfun : monad) _ by [].
apply: Rbind; first exact: Rget.
rewrite /f_trunc /= /NId /=.
case: (ltnP k n.+1) => nk; last exact: Rret.
have -> : f n = Ret (f n) >>= fun x => Ret tt >> Ret x
        :> (idfun : monad) _ by [].
exact/(Rbind (Rmm' nk))/Rbind/Rret/Rupdate.
Qed.
End with_cache.

Section fibo_with_cache.
Variable M : stateRunMonad (cache nat) idfun.

Fixpoint fibo n :=
  match n with
  | 0 => 0
  | 0.+1 => 0.+1
  | (m.+1 as n).+1 => fibo m + fibo n
  end.

Fixpoint fibo_memo n : M nat :=
  lookup_or_compute M n
    match n with
    | 0 => Ret 0
    | (0 as n).+1 =>
        (* need a recursive call to ensure fibo 0 is in the cache for fibo 1 *)
        do _ <- fibo_memo n;
        Ret 0.+1
    | (m.+1 as n).+1 =>
        do x <- fibo_memo m;
        do y <- fibo_memo n;
        Ret (x+y)
    end.

Lemma fibo_memo_ok : forall n k,
    R M fibo k (maxn k n.+1) (fibo_memo n) (fibo n).
Proof.
elim/ltn_ind => -[|n] IH k;
rewrite [fibo_memo _]/=;
apply: Rlookup_or_compute.
  rewrite leqn0 => /eqP ->.
  exact: Rret.
case: n IH => [|n] IH Hk.
  have -> : fibo 1 = Ret 0 >> Ret (fibo 1) :> (idfun : monad) nat by [].
  apply: Rbind; first exact: IH.
  have -> : maxn k 1 = 1 by lia.
  exact: Rret.
have -> : fibo n.+2 = Ret (fibo n) >> (Ret (fibo n.+1) >> Ret (fibo n.+2))
        :> (idfun : monad) nat by [].
apply: Rbind; first exact: IH.
apply: Rbind; first exact: IH.
rewrite (_ : maxn _ _ = n.+2); last by lia.
exact: Rret.
Qed.

Fixpoint fibo' n :=
  match n with
  | 0 => (0, 0.+1)
  | m.+1 => let (a,b) := fibo' m in (b, a+b)
  end.
End fibo_with_cache.

Section Fixn.
Variable T : Type.
Variable F : forall n, (forall k, k < n -> T) -> T. 
Definition Fixn := 
  Fix Wf_nat.lt_wf (fun=> T)
    (fun x f => F x (fun y (yx : y < x) => f y (ltP yx))).
Lemma Fixn_eq :
  (forall x (f g : forall y, y < x -> T),
      (forall y (p : y < x), f y p = g y p) -> F x f = F x g) ->
  forall x, Fixn x = F x (fun y _ => Fixn y).
Proof.
move=> IH.
apply: Fix_eq => x f g H.
congr F.
apply: boolp.functional_extensionality_dep => y.
apply: boolp.functional_extensionality_dep => yx.
exact: H.
Qed.
End Fixn.

Section fix_with_cache.
Variable res : eqType.
Variable M : stateRunMonad (cache res) idfun.

Variable F : forall N : monad, forall n, (forall k, k < n -> N res) -> N res. 
Let fixF := Fixn (F idfun).
Let Fmemo := fun n f => lookup_or_compute M n (F M n f).
Let fixFmemo := Fixn Fmemo.

Hypothesis Funif :
  forall (N : monad) (x : nat) (f g : forall y : nat, y < x -> N res),
    (forall (y : nat) (p : y < x), f y p = g y p) -> F N x f = F N x g.

Hypothesis Fpure :
  forall n c, runStateT (Fixn (F M) n) c = (Fixn (F idfun) n, c).

Lemma fixFmemo_ok : forall n k,
    R M fixF k (maxn k n.+1) (fixFmemo n) (fixF n).
Proof.
rewrite /fixFmemo /Fmemo /fixF /=.
elim/ltn_ind => -[|n] IH k.
  rewrite Fixn_eq; last first.
    move=> x f g H.
    congr lookup_or_compute.
    exact: Funif.
  apply: Rlookup_or_compute.
  rewrite leqn0 => /eqP ->.
  rewrite (_ : F M 0 _ = F M 0 (fun y _ => Fixn (F M) y)); last exact: Funif.
  rewrite -Fixn_eq; last exact: Funif.
  move=> c Hc. by rewrite Fpure.
rewrite Fixn_eq; last first.
  move=> x f g H.
  by rewrite (Funif _ _ _ g).
apply: Rlookup_or_compute => kn1.
Abort.

End fix_with_cache.
