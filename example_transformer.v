(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2020 monae authors, license: LGPL-2.1-or-later               *)
From mathcomp Require Import all_ssreflect.
Require Import monae_lib hierarchy monad_lib fail_lib state_lib.
Require Import monad_transformer.

(******************************************************************************)
(*               Examples of programs using monad transformers                *)
(*                                                                            *)
(* reference:                                                                 *)
(* - R. Affeldt, D. Nowak, Extending Equational Monadic Reasoning with Monad  *)
(*   Transformers, https://arxiv.org/abs/2011.03463                           *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.

Definition evalStateT (N : monad) (S : UU0) (M : stateRunMonad S N)
    {A : UU0} (m : M A) (s : S) : N A :=
  runStateT m s >>= fun x => Ret x.1.

Section FastProduct.
Variables (N : exceptMonad) (M : exceptStateRunMonad nat N).

Fixpoint fastProductRec l : M unit :=
  match l with
  | [::] => Ret tt
  | 0 :: _ => fail
  | n.+1 :: l' => get >>= fun m => put (m * n.+1) >> fastProductRec l'
  end.

Definition fastProduct l : M _ :=
  catch (put 1 >> fastProductRec l >> get) (Ret 0 : M _).

Lemma fastProductCorrect l n :
  evalStateT (fastProduct l) n = Ret (product l).
Proof.
rewrite /fastProduct -(mul1n (product _)); move: 1.
elim: l => [ | [ | x] l ih] m.
- rewrite muln1 bindA bindretf putget.
  rewrite /evalStateT runStateTcatch runStateTbind runStateTput bindretf.
  by rewrite runStateTret runStateTret catchret bindretf.
- rewrite muln0.
  rewrite /evalStateT runStateTcatch runStateTbind runStateTbind runStateTput.
  by rewrite bindretf runStateTfail bindfailf catchfailm runStateTret bindretf.
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
apply boolp.funext => s.
unfold bind.
destruct (m s) as [[|]]; reflexivity.
Qed.

Lemma bindA
  (A B C : UU0) (m : failPState A)
  (f : A -> failPState B) (g : B -> failPState C) :
bind (bind m f) g = bind m (fun x => bind (f x) g).
Proof.
apply boolp.funext => s.
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
Let incr : M unit := get >>= (put \o succn).
Let prog (B : UU0) : M unit := incr >> @fail _ B >> incr.

Goal forall T, prog T = @fail _ _.
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
Let incr : M unit := get >>= (put \o succn).
Let prog T : M unit := incr >> Lift [the monadT of stateT nat] N T fail >> incr.
Goal forall T, prog T = Lift [the monadT of stateT nat] N unit fail.
Proof.
move=> T; rewrite /prog.
rewrite bindA.
rewrite bindLfailf. (* fail laws are not sufficient *)
Abort.
End with_stateT_of_failMonad.

Section with_exceptT_of_stateMonad.
Definition LGet S (M : stateMonad S) :=
  Lift [the monadT of exceptT unit] M S (@get S M).
Definition LPut S (M : stateMonad S) :=
  Lift [the monadT of exceptT unit] M unit \o (@put S M).

Variable N : stateMonad nat.
Let M : monad := exceptT unit N.
Let incr : M unit := LGet N >>= (LPut N \o succn).
Let prog T : M unit := incr >> (fail : _ T) >> incr.

Goal forall T, prog T = @fail _ unit.
Proof.
move=> T; rewrite /prog.
Abort.
End with_exceptT_of_stateMonad.

End incr_fail_incr.

Require Import monad_model.

Section incr_fail_incr_model.

Lemma bindLmfail (M := [the monad of option_monad]) S T U (m : stateT S M U)
    (FAIL := @throw unit T tt) :
  m >> Lift [the monadT of stateT S] M T FAIL =
  Lift [the monadT of stateT S] M T FAIL.
Proof.
rewrite /= /liftS boolp.funeqE => s.
rewrite except_bindE.
rewrite {1}bindE /= {1}/join_of_bind /= {1}/bindS /=.
rewrite {1}bindE /= {1}/join_of_bind /=.
rewrite /actm /= /MS_map /= /actm /=.
by case (m s) => // -[].
Qed.

Section fail_model_sufficient.
Let N : failMonad := [the failMonad of option_monad].
Let M : monad := [the stateMonad nat of MS nat N].
Let FAIL T := @throw unit T tt.

Let incr : M unit := get >>= (put \o succn).
Let prog T : M unit :=
  incr >> Lift [the monadT of stateT nat] N T (@FAIL T) >> incr.
Goal forall T, prog T = Lift [the monadT of stateT nat] N unit (@FAIL unit).
Proof.
move=> T; rewrite /prog.
rewrite bindLmfail.
by rewrite bindLfailf.
Abort.
End fail_model_sufficient.

End incr_fail_incr_model.
