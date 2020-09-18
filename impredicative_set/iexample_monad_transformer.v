From mathcomp Require Import all_ssreflect.
Require Import imonae_lib ihierarchy imonad_lib ifail_lib istate_lib imonad_transformer imonad_model.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.

Import Univ.

Section example_stateT.

Section failStateMonad.
Variables M : failStateMonad nat.
Let incr : M unit := Get >>= (Put \o succn).
Let prog (B : UU0) : M unit := incr >> @Fail M B >> incr.

Goal forall T, prog T = Fail.
Proof.
move=> T; rewrite /prog.
rewrite bindA.
rewrite bindfailf.
by rewrite bindmfail0.
Abort.

End failStateMonad.

Section stateTfailMonad.
Lemma bindLmfail (M := ModelMonad.option_monad) S T U (m : stateT S M U)
    (FAIL := @ExceptOps.throw unit T tt) :
  m >> Lift (stateT S) M T FAIL = Lift (stateT S) M T FAIL.
Proof.
rewrite -!liftSE /liftS boolp.funeqE => s.
rewrite /Bind /=.
rewrite /bindS /=.
rewrite /stateTmonad /=.
rewrite /Monad_of_ret_bind /=.
rewrite /Actm /=.
rewrite /Monad_of_ret_bind.Map /=.
rewrite /bindS /retS /=.
rewrite /Bind /=.
rewrite /ModelMonad.Except.bind /= /Actm /=.
rewrite /Monad_of_ret_bind.Map /=.
rewrite /ModelMonad.Except.bind /=.
case: (m s).
  by case.
by case => u s' /=.
Qed.

Section test.
Variable M : failMonad.
Let N : monad := stateT nat M.
Let incr : N unit := Get >>= (Put \o succn).
Let prog T : N unit := incr >> Lift (stateT nat) M T Fail >> incr.

Goal forall T, prog T = Lift (stateT nat) M unit Fail.
Proof.
move=> T; rewrite /prog.
rewrite bindA.
rewrite bindLfailf.
Abort.
End test.

Section test2.
Let M : failMonad := ModelFail.option.
Let N : monad := stateT nat M.
Let FAIL T := @ExceptOps.throw unit T tt.

Let incr : N unit := Get >>= (Put \o succn).
Let prog T : N unit := incr >> Lift (stateT nat) M T (@FAIL T) >> incr.

Goal forall T, prog T = Lift (stateT nat) M unit (@FAIL unit).
Proof.
move=> T; rewrite /prog.
rewrite bindLmfail.
by rewrite bindLfailf.
Abort.
End test2.

Section test3.
Definition failMonad_of_errorT_mixin (M : monad) :
  MonadFail.class_of (errorT unit M).
Proof.
refine (@MonadFail.Class _ _
  (@MonadFail.Mixin (errorT unit M)
                    (fun B => Ret (@inl _ B tt))
                    _ )).
move=> A B.
case: M => m [f [/= r j a b c]] g.
rewrite /Bind /= /bindX /= /errorTmonad /Monad_of_ret_bind /= /Actm /=.
by rewrite /Monad_of_ret_bind.Map /= /bindX /= !bindretf.
Qed.

Canonical failMonad_of_errorT M := MonadFail.Pack (failMonad_of_errorT_mixin M).

Definition LGet S (M : stateMonad S) := Lift (errorT unit) M S (@Get S M).
Definition LPut S (M : stateMonad S) := Lift (errorT unit) M unit \o (@Put S M).

Variable M : stateMonad nat.
Let N : monad := errorT unit M.
Let incr : N unit := LGet M >>= (LPut M \o succn).
Let prog T : N unit := incr >> (Fail : _ T) >> incr.
End test3.

End stateTfailMonad.

End example_stateT.
