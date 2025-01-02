From mathcomp Require Import all_ssreflect.
From mathcomp Require Import boolp.
Require Import preamble hierarchy monad_lib fail_lib state_lib.

Local Open Scope monae_scope.
Notation "a '≈' b" := (wBisim a b).

Local Open Scope do_notation.

Section delaystatenat_example.
Variable M : delayStateMonad nat.

Definition factds_body m : M (unit + nat)%type :=
  do s <- get;
  match m with
  |O => do _ <- put s; Ret (inl tt)
  |m'.+1 => do _<- put (m * s); Ret (inr m')
  end.

Definition factds := while factds_body.

Fixpoint fact n := match n with |O => 1 |m.+1 => n * fact m end.

Lemma factE n : factds n ≈ do s <- get; do _ <- put (fact n * s); Ret tt.
Proof.
rewrite/factds/factds_body.
elim: n => /= [|n' IH].
rewrite fixpointE/= !bindA.
apply: bindfwB => a.
by rewrite bindA bindretf /= mulSn mul0n addn0.
rewrite/factds/factds_body fixpointE/= bindA.
apply: bindfwB => a.
rewrite bindA bindretf/=.
move: IH.
set h:= while _ _.
move => IH.
apply: wBisim_trans.
apply: bindfwB => a'.
apply IH.
rewrite -!bindA putget !bindA bindretf.
by rewrite -bindA putput mulnA (mulnC (fact n') _).
Qed.
End delaystatenat_example.

Section delaystateseq_example.
Variable M : delayStateMonad (seq nat).

Definition collatzs1_body nml : M ((nat * nat + nat * nat * nat) + nat * nat * nat)%type :=
  match nml with (n, m, l) =>
    do s' <- get;
    do _ <- put (n :: s');
    if n==1 then if (l %% 4 == 1)
            then Ret (inl (inl (m,l)))
                 else do _ <- put [::]; Ret (inl (inr (m+1, m+1, 0)))
    else if (n %% 2 == 0) then Ret (inr (n./2,m,l+1))
         else Ret (inr (3*n + 1, m, l+1))
  end.

Definition collatzs1 n := while (while collatzs1_body) (n,n,0).

Definition collatzs2_body nml : M ((nat * nat + nat * nat * nat))%type :=
  match nml with (n,m,l) =>
    do s' <- get;
    do _ <- put (n :: s');
    if (l %% 4 == 1) && (n == 1) then Ret (inl (m,l))
    else if (n == 1) then do _ <- put [::]; Ret (inr (m+1,m+1,0))
         else if (n %% 2) == 0 then Ret (inr (n./2,m,l+1))
              else Ret (inr (3*n + 1, m, l+1))
  end.

Definition collatzs2 n := while collatzs2_body (n,n,0).

Lemma collatzstepE n : collatzs1 n ≈ collatzs2 n.
Proof.
rewrite/collatzs1/collatzs2 -codiagonalE.
apply whilewB.
move => [[n' m] l].
rewrite/collatzs1_body/collatzs2_body.
case/boolP: (l %% 4 == 1) => Hl/=.
- case/boolP: (n' == 1) => Hn'/=.
  + rewrite Hl fmapE bindA.
    rewrite bindfwB//= => a.
    by rewrite bindA bindretf/=.
  + case/boolP: (n' %% 2 == 0) => He/=;
    rewrite fmapE/= bindA bindfwB//= => a;
    by rewrite bindA bindretf.
- case/boolP: (n' == 1) => Hn' //=.
  + rewrite ifN //= fmapE bindA.
    rewrite bindfwB //= => a.
    by rewrite  bindA bindA bindretf.
   + case/boolP: (n' %% 2 == 0) => He/=;
    rewrite fmapE/= bindA bindfwB//= => a;
    by rewrite bindA bindretf.
Qed.
