(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2020 monae authors, license: LGPL-2.1-or-later               *)
From mathcomp Require Import all_ssreflect.
Require Import imonae_lib ihierarchy imonad_lib ifail_lib istate_lib.
Require Import imonad_transformer.

(******************************************************************************)
(*               Examples of programs using monad transformers                *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.

Import Univ.

(******************************************************************************)
(* reference:                                                                 *)
(* - R. Affeldt, D. Nowak, Extending Equational Monadic Reasoning with Monad  *)
(* Transformers, https://arxiv.org/abs/2011.03463                             *)
(******************************************************************************)
Definition evalStateT (N : monad) (S : UU0) (M : stateRunMonad S N)
    {A : UU0} (m : M A) (s : S) : N A :=
  RunStateT m s >>= fun x => Ret x.1.

Section FastProduct.
Variables (N : exceptMonad) (M : exceptStateRunMonad nat N).

Fixpoint fastProductRec l : M unit :=
  match l with
  | [::] => Ret tt
  | 0 :: _ => Fail
  | n.+1 :: l' => Get >>= fun m => Put (m * n.+1) >> fastProductRec l'
  end.

Definition fastProduct l : M _ :=
  Catch (Put 1 >> fastProductRec l >> Get) (Ret 0 : M _).

Lemma fastProductCorrect l n :
  evalStateT (fastProduct l) n = Ret (product l).
Proof.
rewrite /fastProduct -(mul1n (product _)); move: 1.
elim: l => [ | [ | x] l ih] m.
- rewrite muln1 bindA bindretf putget.
  rewrite /evalStateT RunStateTCatch RunStateTBind RunStateTPut bindretf.
  by rewrite RunStateTRet RunStateTRet catchret bindretf.
- rewrite muln0.
  rewrite /evalStateT RunStateTCatch RunStateTBind RunStateTBind RunStateTPut.
  by rewrite bindretf RunStateTFail bindfailf catchfailm RunStateTRet bindretf.
- rewrite [fastProductRec _]/=.
  by rewrite -bindA putget bindA bindA bindretf -bindA -bindA putput ih mulnA.
Qed.

End FastProduct.

(* The following fail-state monad is such that it does not backtrack the
   state. *)
Module PersistentState.
Section persistentstate.
Variable S : UU0.

Definition failPState (A : UU0) : UU0 :=
S -> option A * S.

Definition runFailPState {A : UU0} (m : failPState A) (s : S) : option A * S :=
m s.

Definition ret {A : UU0} (a : A) : failPState A :=
fun s => (Some a, s).

Definition bind {A B : UU0} (m : failPState A) (f : A -> failPState B) :
failPState B :=
fun s => match m s with
| (None, s') => (None, s')
| (Some a, s') => f a s'
end.

Lemma bindretf (A B : UU0) (a : A) (f : A -> failPState B) :
bind (ret a) f = f a.
Proof.
reflexivity.
Qed.

Lemma bindmret (A : UU0) (m : failPState A) :
bind m ret = m.
Proof.
apply fun_ext => s.
unfold bind.
destruct (m s) as [[|]]; reflexivity.
Qed.

Lemma bindA
  (A B C : UU0) (m : failPState A)
  (f : A -> failPState B) (g : B -> failPState C) :
bind (bind m f) g = bind m (fun x => bind (f x) g).
Proof.
apply fun_ext => s.
unfold bind.
destruct (m s) as [[|]]; reflexivity.
Qed.

Definition fail {A : UU0} : failPState A := fun s => (None, s).

Definition catch {A : UU0} (m1 m2 : failPState A) :=
fun s => match m1 s with
| (Some a, s') => (Some a, s')
| (None, s') => m2 s'
end.

Definition get : failPState S := fun s => (Some s, s).

Definition put (s : S) : failPState unit := fun _ => (Some tt, s).

End persistentstate.
Arguments runFailPState {_ _} _ _.
Arguments ret {_ _} _.
Arguments bind {_ _ _} _ _.
Arguments fail {_ _}.
Arguments get {_}.
Arguments put {_} _.

Local Notation "m >>> f" := (bind m (fun _ => f)) (at level 49).

(* The following example illustrates how the state is NOT backtracked when a
   failure is catched. *)
Goal
  runFailPState (put 1 >>> catch (put 2 >>> fail) get) 0 =
  (Some 2, 2).
Proof.
reflexivity.
Qed.
End PersistentState.

Section incr_fail_incr.

Section with_failStateReifyMonad.
Variables M : failStateReifyMonad nat.
Let incr : M unit := Get >>= (Put \o succn).
Let prog (B : UU0) : M unit := incr >> @Fail _ B >> incr.

Goal forall T, prog T = @Fail _ _.
Proof.
move=> T; rewrite /prog.
rewrite bindA.
rewrite bindfailf.
by rewrite bindmfail.
Abort.
End with_failStateReifyMonad.

Section with_stateT_of_failMonad.
Variable N : failMonad.
Let M : monad := stateT nat N.
Let incr : M unit := Get >>= (Put \o succn).
Let prog T : M unit := incr >> Lift (stateT nat) N T Fail >> incr.

Goal forall T, prog T = Lift (stateT nat) N unit Fail.
Proof.
move=> T; rewrite /prog.
rewrite bindA.
rewrite bindLfailf. (* fail laws are not sufficient *)
Abort.
End with_stateT_of_failMonad.

Section with_exceptT_of_stateMonad.
Definition LGet S (M : stateMonad S) := Lift (exceptT unit) M S (@Get S M).
Definition LPut S (M : stateMonad S) := Lift (exceptT unit) M unit \o (@Put S M).

Variable N : stateMonad nat.
Let M : monad := exceptT unit N.
Let incr : M unit := LGet N >>= (LPut N \o succn).
Let prog T : M unit := incr >> (Fail : _ T) >> incr.

Goal forall T, prog T = @Fail _ unit.
Proof.
move=> T; rewrite /prog.
Abort.
End with_exceptT_of_stateMonad.

End incr_fail_incr.

Require Import imonad_model.

Section incr_fail_incr_model.

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
by case: (m s); case.
Qed.

Section fail_model_sufficient.
Let N : failMonad := ModelFail.option.
Let M : monad := stateT nat N.
Let FAIL T := @ExceptOps.throw unit T tt.

Let incr : M unit := Get >>= (Put \o succn).
Let prog T : M unit := incr >> Lift (stateT nat) N T (@FAIL T) >> incr.

Goal forall T, prog T = Lift (stateT nat) N unit (@FAIL unit).
Proof.
move=> T; rewrite /prog.
rewrite bindLmfail.
by rewrite bindLfailf.
Abort.
End fail_model_sufficient.

End incr_fail_incr_model.
