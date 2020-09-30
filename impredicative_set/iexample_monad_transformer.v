From mathcomp Require Import all_ssreflect.
Require Import imonae_lib ihierarchy imonad_lib ifail_lib istate_lib
 imonad_transformer imonad_model.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.

Import Univ.

Section example_stateT.

Section failStateMonad.
Variables M : failStateRunMonad nat.
Let incr : M unit := Get >>= (Put \o succn).
Let prog (B : UU0) : M unit := incr >> @Fail _ B >> incr.

Goal forall T, prog T = @Fail _ _.
Proof.
move=> T; rewrite /prog.
rewrite bindA.
rewrite bindfailf.
by rewrite bindmfail.
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

Variable M : failMonad. (* because of the run fail law *)

Variable S : UU0.

Variable N : exceptStateRunMonad S M.

(* Could replace M with three different monads *)
Definition mapStateT2
  {A : UU0}
  (f : M (A*S)%type -> M (A*S)%type -> M (A*S)%type) (m1 m2 : N A) : N A :=
Liftme (fun s => f (RunStateT m1 s) (RunStateT m2 s)).

Definition evalStateT {A : UU0} (m : N A) (s : S) : M A :=
RunStateT m s >>= fun a_s' => Ret (a_s'.1).

Lemma RunStateTBind
  (A B : UU0) (m : N A) (f : A -> N B) (s : S) :
RunStateT (m >>= f) s =
RunStateT m s >>= fun a_s' => RunStateT (f (fst a_s')) (snd a_s').
Proof.
(*rewrite /runStateT.
rewrite {1}/Bind /Actm /= /bindS /=.
rewrite /Monad_of_ret_bind.Map /=.
rewrite /retS.
rewrite bindA.
congr (_ >>= _).
apply fun_ext => -[a s'] /=.
by rewrite bindretf.
Qed.*) Admitted.

Lemma RunStateTLiftme (A : UU0) s (f : S -> M (A * S)%type) :
  @RunStateT _ _ N _ (Liftme f) s = f s :> M _.
Admitted.

Lemma RunStateTRet (A : UU0) (a : A) (s : S) :
@RunStateT _ _ _ _ (Ret a : N _) s = Ret (a, s) :> M _.
Admitted.

Lemma RunStateTGet (s : S) :
  @RunStateT _ _ N _ Get s = Ret (s, s).
Admitted.

Lemma RunStateTPut (s' s : S) :
@RunStateT _ _ N _ (Put s' : N _) s = Ret (tt, s').
Proof.
Admitted.

Lemma RunStateTfail (A : UU0) (s : S) :
  @RunStateT S M N A (Fail : N A) s = @Fail M _ :> M (A * S)%type.
Proof.
Admitted.

End example_stateT.

Section FastProduct.

Variable M : exceptMonad.

Variable N : exceptStateRunMonad nat M.

Program Fixpoint fastProductRec (xs : list nat) : N unit :=
match xs with
| nil => Ret tt
| cons 0 _ => Fail
| cons x.+1 xs' => Get >>= fun r => Put (r * x.+1) >> fastProductRec xs'
end.

Definition fastProduct (xs : list nat) : N nat :=
mapStateT2 Catch (Put 1 >> fastProductRec xs >> Get) (Ret 0).

Definition runE := (RunStateTLiftme, RunStateTBind, RunStateTRet, RunStateTPut,RunStateTGet).

Lemma fastProductCorrect (xs : list nat) (s : nat) :
  evalStateT (fastProduct xs) s = Ret (product xs).
Proof.
assert (Hgen : forall n,
  evalStateT (mapStateT2 Catch ((Put n >> fastProductRec xs) >> Get)
     (Ret 0)) s = Ret (n * product xs)).
{
  induction xs as [ | [ | x] xs IH]; intro n.
  - rewrite muln1 bindA bindretf putget.
    rewrite /evalStateT.
    rewrite /mapStateT2.
    rewrite !runE.
    rewrite bindretf.
    rewrite !runE.
    rewrite catchret.
    by rewrite bindretf.
  - rewrite muln0.
    rewrite /evalStateT.
    rewrite /mapStateT2.
    rewrite !runE.
    rewrite bindretf /=.
    rewrite RunStateTfail.
    rewrite bindfailf.
    rewrite catchfailm.
    by rewrite bindretf.
  - rewrite /evalStateT.
    rewrite /mapStateT2.
    rewrite runE.
    rewrite runE.
    rewrite runE.
    rewrite runE.
    rewrite runE.
    rewrite bindretf /=.
    rewrite runE.
    rewrite runE.
    rewrite bindretf /=.
    rewrite 2!runE bindretf /=.
    have {IH} := IH (n * x.+1).
    rewrite /evalStateT /mapStateT2.
    rewrite 4!runE.
    rewrite runE bindretf /= => IH.
    rewrite IH.
    rewrite mulnA.
(*    rewrite putget.
    rewrite 2!bindA.
    rewrite bindretf.
    rewrite -2!bindA.
    rewrite putput.
    by rewrite IH mulnA.*)
    done.
}
by rewrite Hgen mul1n.
Admitted.


End FastProduct.





Definition runMonad_of_stateT_mixin S (M : runMonad S) :
  @MonadRun.mixin_of S (stateT S M).
Admitted.

Canonical run_of_stateT S M :=
  MonadRun.Pack (MonadRun.Class (@runMonad_of_stateT_mixin S M)).

Definition failRunMonad_of_stateT_class S (M : failRunMonad S) :
  @MonadFailRun.class_of S (stateT S M).
Admitted.

Canonical failRun_of_stateT S M :=
  MonadFailRun.Pack (@failRunMonad_of_stateT_class S M).

Definition failStateRun_of_stateT_class S (M : failRunMonad S) :
  @MonadFailStateRun.class_of S (stateT S M).
Admitted.

Canonical failStateRun_of_stateT S M :=
  @MonadFailStateRun.Pack _ _ (@failStateRun_of_stateT_class S M).

(* TODO(rei):
shouldn't
stateMonad_of_stateT_mixin
use the models? *)

Section FastProduct.

Local Obligation Tactic := idtac.
(*Local Set Bullet Behavior "Strict Subproofs".*)

Variable M : (*exceptMonad*)failRunMonad nat.
Let N := failStateRun_of_stateT (*stateT nat*) M.

Fixpoint fastProductRec (xs : list nat) : N unit :=
match xs with
| nil => Ret tt
| cons 0 _ => Lift (stateT nat) M unit Fail
| cons (S x) xs' => Get >>= fun r => Put (r * S x) >> fastProductRec xs'
end.

Definition evalFastProduct (xs : list nat) : nat -> nat :=
  fun s => if Run (Put 1 >> fastProductRec xs >> Get) s is Some (x, _) then x else 0.
(*  mapStateT2 (*Catch*) (fun s1 s2 => if s1 is Some x then Some x else s2)
    (Put 1 >> fastProductRec xs >> Get) (Ret 0).*)

(*Require Import Arith.
Import Nat.*)

Lemma evalFastProductCorrect (xs : list nat) (s : nat) :
  evalFastProduct xs s = product xs.
Proof.
assert (Hgen : forall n,
  (if Run (Put n >> fastProductRec xs >> Get) s is Some (x, _) then x else 0)
  = n * product xs).
{
  induction xs as [ | [ | x] xs IH]; intro n.
  - rewrite muln1 bindA bindretf putget.
    by rewrite runbind runput runret.
  - rewrite muln0.
    rewrite 2!runbind.
    rewrite runput.
    simpl fastProductRec.
    set m := Lift _ _ _ _.
    rewrite (_ : m = (fun=> @Fail _ _)); last first.
    + rewrite {}/m.
      rewrite -liftSE.
      rewrite /liftS.
      rewrite boolp.funeqE => m.
      by rewrite bindfailf.
    + replace (@Run _ N _ (fun=> Fail) n)
       with (@Run _ N unit Fail n).
      * by rewrite runfail.
      * admit.
  - simpl fastProductRec.
    rewrite -bindA.
    rewrite putget.
    rewrite 2!bindA.
    rewrite bindretf.
    rewrite -2!bindA.
    rewrite putput.
    by rewrite IH mulnA.
}
rewrite /evalFastProduct.
by rewrite Hgen mul1n.
Admitted.

End FastProduct.

Module runStateT.

(* The [runStateT] primitive and its laws.
   To be moved with the definition of the state monad transformer. *)
Definition runStateT {S A : UU0} {M : monad} (m : stateT S M A) (s : S) :
M (A*S)%type :=
m s.

(*failStateRunMonad*)

Lemma runStateTFun {S A : UU0} {M : monad} (m : stateT S M A) (s : S) :
@runStateT _ _ M (fun s => m s) s = m s.
Proof.
reflexivity.
Qed.

Lemma runStateTRet (S A : UU0) (M : monad) (a : A) (s : S) :
@runStateT _ _ M (Ret a) s = Ret (a, s).
Proof.
reflexivity.
Qed.

Lemma runStateTBind
  (S A B : UU0) (M : monad) (m : stateT S M A) (f : A -> stateT S M B) (s : S) :
runStateT (m >>= f) s =
runStateT m s >>= fun a_s' => runStateT (f (fst a_s')) (snd a_s').
Proof.
rewrite /runStateT.
rewrite {1}/Bind /Actm /= /bindS /=.
rewrite /Monad_of_ret_bind.Map /=.
rewrite /retS.
rewrite bindA.
congr (_ >>= _).
apply fun_ext => -[a s'] /=.
by rewrite bindretf.
Qed.

Lemma runStateTGet (S : UU0) (M : monad) (s : S) :
@runStateT _ _ M Get s = Ret (s, s).
Proof.
Admitted.

Lemma runStateTPut (S : UU0) (M : monad) (s' s : S) :
@runStateT _ _ M (Put s') s = Ret (tt, s').
Proof.
Admitted.

Lemma runStateTLfail (S A : UU0) (M : failMonad) (s : S) :
runStateT (Lift (stateT S) M A Fail) s = Fail.
Proof.
Admitted.

(* No need to unfold [runStateT] later because its laws are sufficient to
   conclude proofs. *)
Opaque runStateT.

(* [evalStateT] and [mapStateT2] are not primitives but are defined
   with [runStateT]. They will be unfolded in proof scripts below in
   order to apply the laws of [runStateT]. *)
Definition evalStateT {S A : UU0} {M : monad} (m : stateT S M A) (s : S) :
M A :=
runStateT m s >>= fun a_s' => Ret (a_s'.1).

(* In case of failure, the state is backtracked. *)
Definition mapStateT2
  {S A : UU0} {M : monad}
  (f : M (A*S)%type -> M (A*S)%type -> M (A*S)%type) (m1 m2 : stateT S M A) :
stateT S M A :=
fun s => f (runStateT m1 s) (runStateT m2 s).

Section FastProduct.

Local Obligation Tactic := idtac.
Local Set Bullet Behavior "Strict Subproofs".

Variable M : exceptMonad.
Let N : monad := stateT nat M.

Fixpoint fastProductRec (xs : list nat) : N unit :=
match xs with
| nil => Ret tt
| cons 0 _ => Lift (stateT nat) M unit Fail
| cons (S x) xs' => Get >>= fun r => Put (r * S x) >> fastProductRec xs'
end.

Definition fastProduct (xs : list nat) : N nat :=
mapStateT2 Catch (Put 1 >> fastProductRec xs >> Get) (Ret 0).

Require Import Arith.
Import Nat.

Lemma fastProductCorrect (xs : list nat) (s : nat) :
evalStateT (fastProduct xs) s = Ret (product xs).
Proof.
assert (Hgen : forall n,
  evalStateT (mapStateT2 Catch ((Put n >> fastProductRec xs) >> Get)
     (Ret 0)) s = Ret (n * product xs)).
{
  induction xs as [ | [ | x] xs IH]; cbn; intro n.
  - rewrite mult_1_r bindA bindretf putget.
    unfold mapStateT2, evalStateT.
    rewrite runStateTFun runStateTBind runStateTPut bindretf runStateTRet
     catchret bindretf.
    reflexivity.
  - rewrite mult_0_r.
    unfold mapStateT2, evalStateT.
    rewrite runStateTFun runStateTBind runStateTBind runStateTPut bindretf
     runStateTLfail bindfailf catchfailm runStateTRet bindretf.
    reflexivity.
  - rewrite <- bindA.
    rewrite putget bindA bindA bindretf.
    rewrite <- bindA, <- bindA, putput, IH.
    rewrite <- mult_n_Sm, mult_comm, mul_add_distr_l, mul_add_distr_l,
     plus_comm, mult_comm, (mult_comm (product xs)), mult_assoc.
    reflexivity.
}
rewrite Hgen.
cbn.
by rewrite <- plus_n_O.
Qed.

End FastProduct.

(* The following example illustrates how the state is backtracked when a
   failure is catched. *)

Goal
runStateT (
  Put 1 >>
  mapStateT2 Catch (Put 2 >> Lift (stateT _) ModelExcept.t _ Fail) Get) 0 =
inr (1, 1).
Proof.
rewrite runStateTBind runStateTPut bindretf.
unfold mapStateT2.
rewrite runStateTFun runStateTBind runStateTPut bindretf runStateTLfail
 catchfailm runStateTGet.
reflexivity.
Qed.

(* The following fail-state monad is such that it does not backtrack the
   state. *)
Section PersistentState.

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

End PersistentState.

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

End runStateT.
