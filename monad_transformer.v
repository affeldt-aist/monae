(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2020 monae authors, license: LGPL-2.1-or-later               *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require boolp.
Require Import monae_lib.
From HB Require Import structures.
Require Import hierarchy monad_lib fail_lib state_lib.

(******************************************************************************)
(*                    Formalization of monad transformers                     *)
(*                                                                            *)
(* This file corresponds to the formalization of [Mauro Jaskelioff, Modular   *)
(* Monad Transformers, ESOP 2009] (roughly, up to Sect. 5, Example 22).       *)
(*                                                                            *)
(*  Module MonadMLaws == laws of monad morphisms                              *)
(*             monadM == type of monad morphisms                              *)
(*             monadT == type of monad transformers, i.e., functions t of     *)
(*                       type monad -> monad equipped with an operator Lift   *)
(*                       such that for any monad M Lift t M is a monad        *)
(*                       morphism from M to t M                               *)
(*                       instances:                                           *)
(*                       - stateT: the state monad transformer                *)
(*                       - exceptT: the exception monad transformer           *)
(*                       - envT: environment                                  *)
(*                       - outputT                                            *)
(*                       - contT: continuation                                *)
(*         mapStateT2 == standard utility function                            *)
(*            lifting == lifting of a sigma-operation along a monad morphism  *)
(*           alifting == algebraic operation defined using an algebraic       *)
(*                       operation op and a monad morphism e                  *)
(* uniform_algebraic_lifting == Theorem: alifting is a lifting                *)
(*                                                                            *)
(*         functorial == type of functors where the action on objects as type *)
(*                       monad -> monad                                       *)
(*                fmt == type of functorial monad transformers                *)
(*                       instances:                                           *)
(*                       - exceptFMT                                          *)
(*                       - stateFMT                                           *)
(*                       - envFMT                                             *)
(*                       - outputFMT                                          *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.

Module MonadMLaws.
Section monadmlaws.
Variables (M N : monad).
Definition ret (e : M ~~> N) := forall A : UU0, e A \o Ret = Ret.
Definition bind (e : M ~~> N) := forall (A B : UU0) (m : M A) (f : A -> M B),
  e B (m >>= f) = e A m >>= (e B \o f).
End monadmlaws.
End MonadMLaws.

HB.mixin Record isMonadM (M N : monad) (e : M ~~> N) := {
  monadMret : MonadMLaws.ret e ;
  monadMbind : MonadMLaws.bind e }.

#[short(type=monadM)]
HB.structure Definition MonadM (M N : monad) :=
  {e of isMonadM M N e & isNatural M N e}.

HB.factory Record isMonadM_ret_bind (M N : monad) (e : M ~~> N) := {
  monadMret : MonadMLaws.ret e ;
  monadMbind : MonadMLaws.bind e }.

HB.builders Context (M N : monad) (e : M ~~> N) of isMonadM_ret_bind M N e.

Lemma naturality_monadM : naturality M N e.
Proof.
move=> A B h; apply boolp.funext => m /=.
by rewrite !fmapE monadMbind (compA (e B)) monadMret.
Qed.

HB.instance Definition _ := isNatural.Build M N e naturality_monadM.
HB.instance Definition _ := isMonadM.Build M N e monadMret monadMbind.
HB.end.

HB.mixin Record isMonadT (T : monad -> monad) := {
  Lift : forall M, monadM M (T M) }.

#[short(type=monadT)]
HB.structure Definition MonadT := {T of isMonadT T}.
Arguments Lift : clear implicits.

Section state_monad_transformer.
Variables (S : UU0) (M : monad).

Definition MS := fun A : UU0 => S -> M (A * S)%type.

Definition retS : FId ~~> MS := fun (A : UU0) => curry Ret.

Definition bindS (A B : UU0) (m : MS A) f : MS B := fun s => m s >>= uncurry f.

Let bindSretf : BindLaws.left_neutral bindS retS.
Proof.
by move=> A B a f; rewrite /bindS; apply boolp.funext => s; rewrite bindretf.
Qed.

Let bindSmret : BindLaws.right_neutral bindS retS.
Proof.
move=> A m; rewrite /bindS; apply boolp.funext => s.
by rewrite -[in RHS](bindmret (m s)); bind_ext; case.
Qed.

Let bindSA : BindLaws.associative bindS.
Proof.
move=> A B C m f g; rewrite /bindS; apply boolp.funext => s.
by rewrite bindA; bind_ext; case.
Qed.

HB.instance Definition _ :=
  isMonad_ret_bind.Build MS bindSretf bindSmret bindSA.

Lemma MS_mapE (A B : UU0) (f : A -> B) (m : MS A) :
  (MS # f) m = (M # (fun x => (f x.1, x.2))) \o m.
Proof.
apply boolp.funext=> s.
rewrite {1}/actm /= /bindS /= fmapE.
congr bind.
by apply: boolp.funext; case.
Qed.

Definition liftS (A : UU0) (m : M A) : MS A :=
  fun s => m >>= (fun x => Ret (x, s)).

Let retliftS : MonadMLaws.ret liftS.
Proof.
move=> A; rewrite /liftS; apply boolp.funext => a /=; apply boolp.funext => s /=.
by rewrite bindretf.
Qed.

Let bindliftS : MonadMLaws.bind liftS.
Proof.
move=> A B m f; rewrite {1}/liftS; apply boolp.funext => s.
rewrite [in LHS]bindA.
transitivity ((liftS m s) >>= (uncurry (@liftS B \o f))) => //.
rewrite [in RHS]bindA.
bind_ext => a.
by rewrite [in RHS]bindretf.
Qed.

HB.instance Definition _ := isMonadM_ret_bind.Build
  M [the monad of MS] liftS retliftS bindliftS.

End state_monad_transformer.

Definition stateT (S : UU0) := fun M => [the monad of MS S M].

HB.instance Definition _ (S : UU0) := isMonadT.Build
  (stateT S) (fun M => [the monadM _ _ of @liftS S M]).

Definition mapStateT2 (A S : UU0) (N1 N2 N3 : monad)
    (f : N1 (A * S)%type -> N2 (A * S)%type -> N3 (A * S)%type)
    (m1 : stateT S N1 A) (m2 : stateT S N2 A) : stateT S N3 A :=
  fun s => f (m1 s) (m2 s).

Section stateMonad_of_stateT.
Variables (S : UU0) (M : monad).

Local Notation M' := (MS S M).
Let Put : S -> M' unit := fun s _ => Ret (tt, s).
Let Get : M' S := fun s => Ret (s, s).

Let bindputput (s s' : S) : Put s >> Put s' = Put s'.
Proof.
rewrite bindE /= /bindS.
apply boolp.funext => s0.
by rewrite MS_mapE bind_fmap bindretf.
Qed.

Let bindputget (s : S) : Put s >> Get = Put s >> Ret s.
Proof.
rewrite !bindE !MS_mapE /= /bindS.
apply boolp.funext => s'.
by rewrite !bind_fmap !bindretf.
Qed.

Let bindgetput : Get >>= Put = skip.
Proof.
rewrite bindE MS_mapE /= /bindS.
by apply boolp.funext => s; rewrite bind_fmap bindretf.
Qed.

Let bindgetget (A : UU0) (k : S -> S -> stateT S M A) :
  Get >>= (fun s => Get >>= k s) = Get >>= (fun s => k s s).
Proof.
apply boolp.funext => s.
rewrite /Get/=.
rewrite !bindE !MS_mapE /= /bindS /= /retS/=.
rewrite !bind_fmap !bindretf/=.
rewrite !bindE !MS_mapE /= /bindS /= /retS/=.
by rewrite bind_fmap bindretf.
Qed.

HB.instance Definition _ := @isMonadState.Build
  S (MS S M) Get Put bindputput bindputget bindgetput bindgetget.

End stateMonad_of_stateT.

Section exception_monad_transformer.
Local Obligation Tactic := idtac.
Variables (Z : UU0) (* the type of exceptions *) (M : monad).

(* action on objects of the transformed monad *)
Definition MX := fun X : UU0 => M (Z + X)%type.

(* unit and bind operator of the transformed monad *)
Definition retX : FId ~~> MX := fun X x => Ret (inr x).

Definition bindX X Y (t : MX X) (f : X -> MX Y) : MX Y :=
  t >>= fun c => match c with inl z => Ret (inl z) | inr x => f x end.

Let bindXretf : BindLaws.left_neutral bindX retX.
Proof. by move=> A B a f; rewrite /bindX bindretf. Qed.

Let bindXmret : BindLaws.right_neutral bindX retX.
Proof.
by move=> A m; rewrite /bindX -[in RHS](bindmret m); bind_ext; case.
Qed.

Let bindXA : BindLaws.associative bindX.
Proof.
move=> A B C m f g; rewrite /bindX bindA; bind_ext; case => //.
by move=> z; rewrite bindretf.
Qed.

HB.instance Definition _ :=
 isMonad_ret_bind.Build MX bindXretf bindXmret bindXA.

Lemma MX_mapE (A B : UU0) (f : A -> B) :
  MX # f = M # (fun x => match x with inl y => inl y | inr y => inr (f y) end).
Proof.
apply boolp.funext => m.
rewrite {1}/actm /= /bindX /= [in RHS]fmapE.
congr (_ _).
by apply: boolp.funext; case.
Qed.

Definition liftX X (m : M X) : MX X := m >>= (@ret [the monad of MX] _).

Let retliftX : MonadMLaws.ret liftX.
Proof.
by move=> A; apply boolp.funext => a; rewrite /liftX /= bindretf.
Qed.

Let bindliftX : MonadMLaws.bind liftX.
Proof.
move=> A B m f; rewrite {1}/liftX.
rewrite !bindE !fmapE.
rewrite /= /join_of_bind /bindX /= !bindA.
rewrite 2!joinE !bindA.
bind_ext => a.
rewrite 3!bindretf.
rewrite /liftX /=.
bind_ext => b.
by rewrite bindretf.
Qed.

HB.instance Definition _ := isMonadM_ret_bind.Build
  M [the monad of MX] liftX retliftX bindliftX.

End exception_monad_transformer.

Definition exceptT (Z : UU0) := fun M => [the monad of MX Z M].

HB.instance Definition _ (Z : UU0) := isMonadT.Build
  (exceptT Z) (fun M => [the monadM M [the monad of MX Z M] of @liftX Z M]).

Section failMonad_of_exceptT.
Variable M : monad.
Let N (B : UU0) := M (unit + B)%type.

Let Fail : forall B, N B := fun B => Ret (inl tt).

Let bindfail : BindLaws.left_zero (@bind (exceptT unit M)) Fail.
Proof.
move=> A B g; rewrite /Fail.
by rewrite bindE /= /join_of_bind /bindX /= fmapE /= bindA 2!bindretf.
Qed.

HB.instance Definition _ := @isMonadFail.Build (MX unit M) Fail bindfail.

End failMonad_of_exceptT.

Section exceptMonad_of_exceptT.
Variable (M : monad).
Let N (B : UU0) := M (unit + B)%type.

Let Catch (B : UU0) (x : N B) (y : N B) : N B :=
  x >>= (fun u => (fun k k' => match u with | inl a => k a | inr b => k' b end)
    (fun=> y) (fun b => Ret (inr b))).

Let Catchmfail (A : UU0) :
  right_id (@fail [the failMonad of MX unit M] A) (@Catch A).
Proof.
move=> x; rewrite /Catch /= /fail /= -[in RHS](bindmret x); bind_ext.
by case=> /= [[]|].
Qed.

Let Catchfailm (A : UU0) :
  left_id (@fail [the failMonad of MX unit M] A) (@Catch A).
Proof.
move=> x; rewrite /N in x *.
by rewrite /Catch /= /fail /= bindretf.
Qed.

Let CatchA (A : UU0) : associative (@Catch A).
Proof.
move=> x y z; rewrite /Catch bindA; bind_ext.
by case=> [[]//|b]; rewrite bindretf.
Qed.

Let Catchret (A : UU0) (ua : A%type) :
  @left_zero (N A) (N A) (Ret (inr ua)) (@Catch A).
Proof. by move=> n ; rewrite /Catch /= bindretf. Qed.

HB.instance Definition _ := @isMonadExcept.Build
  (MX unit M) Catch Catchmfail Catchfailm CatchA Catchret.

End exceptMonad_of_exceptT.

Section environment_monad_transformer.
Local Obligation Tactic := idtac.
Variables (R : UU0) (M : monad).

Definition MEnv := fun A : UU0 => R -> M A.

Definition retEnv : FId ~~> MEnv := fun (A : UU0) a r => Ret a.

Definition bindEnv A B (m : MEnv A) f : MEnv B :=
  fun r => m r >>= (fun a => f a r).

Let bindEnvretf : BindLaws.left_neutral bindEnv retEnv.
Proof.
by move=> A B a f; rewrite /bindEnv; apply boolp.funext => r; rewrite bindretf.
Qed.

Let bindEnvmret : BindLaws.right_neutral bindEnv retEnv.
Proof.
move=> A m; rewrite /bindEnv; apply boolp.funext => r.
rewrite -[in RHS](bindmret (m r)); by bind_ext; case.
Qed.

Let bindEnvA : BindLaws.associative bindEnv.
Proof.
move=> A B C m f g; rewrite /bindEnv; apply boolp.funext => r.
by rewrite bindA; bind_ext; case.
Qed.

HB.instance Definition _ :=
 isMonad_ret_bind.Build MEnv bindEnvretf bindEnvmret bindEnvA.

Lemma MEnv_mapE (A B : UU0) (f : A -> B) (m : MEnv A) :
  (MEnv # f) m = (M # f) \o m.
Proof. by apply boolp.funext=> r; rewrite /= fmapE. Qed.

Definition liftEnv A (m : M A) : MEnv A := fun r => m.

Let retliftEnv : MonadMLaws.ret liftEnv. Proof. by []. Qed.

Let bindliftEnv : MonadMLaws.bind liftEnv. Proof. by []. Qed.

HB.instance Definition envTmonadM := isMonadM_ret_bind.Build
  M [the monad of MEnv] liftEnv retliftEnv bindliftEnv.

End environment_monad_transformer.

Definition envT (E : UU0) := fun M => [the monad of MEnv E M].

HB.instance Definition _ (E : UU0) := isMonadT.Build (envT E)
  (fun M => [the monadM M [the monad of MEnv E M] of @liftEnv E M]).

(* traces monad transformer? *)
Section output_monad_transformer.
Local Obligation Tactic := idtac.
Variables (R : UU0) (M : monad).

Definition MO (X : UU0) := M (X * seq R)%type.

Definition retO : FId ~~> MO := fun (A : UU0) a => Ret (a, [::]).

Definition bindO A B (m : MO A) (f : A -> MO B) : MO B :=
  m >>= (fun o => let: (x, w) := o in f x >>=
  (fun o' => let (x', w') := o' in Ret (x', w ++ w'))).

Let bindOretf : BindLaws.left_neutral bindO retO.
Proof.
move=> A B a f; rewrite /bindO /= bindretf /=.
rewrite (_ : (fun o' : B * seq R => _) = (fun o => Ret o)) ?bindmret //.
by apply boolp.funext => -[].
Qed.

Let bindOmret : BindLaws.right_neutral bindO retO.
Proof.
move=> A m; rewrite /bindO /= /retO /= -[RHS]bindmret.
by bind_ext => -[a w]; rewrite bindretf cats0.
Qed.

Let bindOA : BindLaws.associative bindO.
Proof.
move=> A B C m f g; rewrite /bindO /=.
rewrite bindA; bind_ext; case=> x w.
rewrite !bindA; bind_ext; case=> x' w'.
rewrite !bindA bindretf; bind_ext; case=> x'' w''.
by rewrite bindretf catA.
Qed.

HB.instance Definition _ :=
 isMonad_ret_bind.Build MO bindOretf bindOmret bindOA.

Lemma MO_mapE (A B : UU0) (f : A -> B) (m : MO A) :
  (MO # f) m = (M # (fun x => (f x.1, x.2))) m.
Proof.
rewrite [in LHS]/actm /= /bindO /= [in RHS]fmapE.
congr (_ _).
apply boolp.funext => -[] ? ?.
by  rewrite bindretf cats0.
Qed.

Definition liftO A (m : M A) : MO A := m >>= (fun x => Ret (x, [::])).

Let retliftO : MonadMLaws.ret liftO.
Proof.
move=> a; rewrite /liftO /= /retO; apply boolp.funext => o /=.
by rewrite bindretf.
Qed.

Let bindliftO : MonadMLaws.bind liftO.
Proof.
move=> A B m f; rewrite {1}/liftO.
rewrite !bindE !fmapE /= /join_of_bind /bindO /= 2!joinE !bindA.
bind_ext => a.
rewrite /= !bindretf /liftO bindA.
bind_ext => b.
by rewrite bindretf /= bindretf.
Qed.

HB.instance Definition outputTmonadM := isMonadM_ret_bind.Build
  M [the monad of MO] liftO retliftO bindliftO.

End output_monad_transformer.

Definition outputT (R : UU0) := fun M => [the monad of MO R M].

HB.instance Definition _ (R : UU0) := isMonadT.Build (outputT R)
  (fun M => [the monadM M [the monad of MO R M] of @liftO R M]).

Section continuation_monad_tranformer.
Local Obligation Tactic := idtac.
Variables (r : UU0) (M : monad).

Definition MC : UU0 -> UU0 := fun A => (A -> M r) -> M r %type.

Definition retC : FId ~~> MC := fun (A : UU0) (a : A) k => k a.

Definition bindC A B (m : MC A) f : MC B := fun k => m (f^~ k).

Let bindCretf : BindLaws.left_neutral bindC retC.
Proof. by []. Qed.

Let bindCmret : BindLaws.right_neutral bindC retC.
Proof. by []. Qed.

Let bindCA : BindLaws.associative bindC.
Proof. by []. Qed.

HB.instance Definition _ :=
  isMonad_ret_bind.Build MC bindCretf bindCmret bindCA.

Lemma MC_mapE (A B : UU0) (f : A -> B) (m : MC A) :
  (MC # f) m = fun k : B -> M r => m (k \o f).
Proof. by []. Qed.

Definition liftC A (x : M A) : MC A := fun k => x >>= k.

Let retliftC : MonadMLaws.ret liftC.
Proof.
move => A; rewrite /liftC; apply boolp.funext => a /=.
by apply boolp.funext => s; rewrite bindretf.
Qed.

Let bindliftC : MonadMLaws.bind liftC.
Proof.
move => A B m f; rewrite /liftC; apply boolp.funext => cont.
by rewrite 3!bindA.
Qed.

HB.instance Definition contTmonadM := isMonadM_ret_bind.Build
  M [the monad of MC] liftC retliftC bindliftC.

End continuation_monad_tranformer.

Definition contT (r : UU0) := fun M => [the monad of MC r M].

HB.instance Definition _ (r : UU0) := isMonadT.Build (contT r)
  (fun M => [the monadM M [the monad of MC r M] of @liftC r M]).

Definition abortT r X (M : monad) A : contT r M A := fun _ : A -> M r => Ret X.
Arguments abortT {r} _ {M} {A}.

Section contMonad_of_contT.
Variables (r : UU0) (M : monad).
Let N := MC r M.

Let Callcc (A B : UU0) : ((A -> N B) -> N A) -> N A :=
  fun k f => k (fun a => fun=> f a) f.

Let Callcc0 (A B : UU0) (g : (A -> N B) -> N A) (k : B -> N B) :
  @Callcc _ _ (fun f => g (fun x => f x >>= k)) = @Callcc _ _ g.
Proof. by []. Qed.

Let Callcc1 (A B : UU0) (m : N B) : @Callcc _ _ (fun _ : B -> N A => m) = m.
Proof. by []. Qed.

Let Callcc2 (A B C : UU0) (m : N A) x (k : A -> B -> N C) :
  @Callcc _ _ (fun f : _ -> N _ => m >>= (fun a => f x >>= (fun b => k a b))) =
  @Callcc _ _ (fun f : _ -> N _ => m >> f x).
Proof. by []. Qed.

Let Callcc3 (A B : UU0) (m : N A) b :
  @Callcc _ _ (fun f : B -> N B => m >> f b) = @Callcc _ _ (fun _ : B -> N B => m >> Ret b).
Proof. by []. Qed.

HB.instance Definition _ := @isMonadContinuation.Build
  (MC r M) Callcc Callcc0 Callcc1 Callcc2 Callcc3.

End contMonad_of_contT.

Section continuation_monad_transformer_examples.

Fixpoint for_loop (M : monad) (it min : nat) (body : nat -> contT unit M unit) : M unit :=
  if it <= min then Ret tt
  else if it is it'.+1 then
      (body it') (fun _ => for_loop it' min body)
      else Ret tt.

Section for_loop_lemmas.
Variable M : monad.
Implicit Types body : nat  -> contT unit M unit.

Lemma loop0 i body : for_loop i i body = Ret tt.
Proof.
by case i => //= n; rewrite ltnS leqnn.
Qed.

Lemma loop1 i j body : for_loop (i.+1 + j) i body =
  (body (i + j)) (fun _ => for_loop (i + j) i body).
Proof.
rewrite /=.
by case : ifPn ; rewrite ltnNge leq_addr.
Qed.

Lemma loop2 i j body :
  body (i + j) = abortT tt -> for_loop (i + j).+1 i body = Ret tt.
Proof.
move=> Hbody /=.
case : ifPn => Hcond.
- reflexivity.
- by rewrite Hbody /= /abortT.
Qed.

End for_loop_lemmas.
(* TODO : instantiate with RunStateMonad *)

Definition foreach (M : monad) (items : list nat) (body : nat -> contT unit M unit) : M unit :=
  foldr
    (fun x next => (body x) (fun _ => next))
    (Ret tt)
    items.

(* Lemma loop3 : forall i j body, *)
(*      foreach (i + j).+1 i body = Ret tt -> body (i + j) = @abort_tt m unit. *)
(* Proof. *)
(* move => i j body /=. *)
(* case : ifPn => //; rewrite ltnNge; rewrite leq_addr. *)
(* by []. *)
(* move => _ /= Hfor. *)
(* have Hcont2 : forall cont, body (i + j) = @abort_tt m unit -> body (i + j) cont = Ret tt. *)
(*   (* split. *) *)
(*   rewrite /= /abort_tt /abort. *)
(*   by rewrite funeqE. *)
(* have Hcont1 : (forall cont, body (i + j) cont = Ret tt) -> body (i + j) = @abort_tt m unit.   *)
(*   move => Hcont. *)
(*   rewrite /= /abort_tt /abort. *)
(*   rewrite funeqE => k. *)
(*   exact: Hcont. *)
(* apply Hcont1. *)
(* move => cont. *)
(* rewrite Hcont2 //. *)

(* set bl := (fun _ : unit => foreach (i + j) i body). *)
(* (* Check (fun _ : unit => foreach (i + j) i body). *) *)
(* generalize (Hcont1 bl). *)

(* move => bl. *)
(* Qed *)

Section sum.
Variables M : stateMonad nat.

Let sum n : M unit := for_loop n O
  (fun i : nat => liftC (get >>= (fun z => put (z + i)))).

Lemma sum_test n :
  sum n = get >>= (fun m => put (m + sumn (iota 0 n))).
Proof.
elim: n => [|n ih].
  rewrite /sum.
  rewrite loop0.
  rewrite (_ : sumn (iota 0 0) = 0) //.
  rewrite -[LHS]bindskipf.
  rewrite -getputskip.
  rewrite bindA.
  bind_ext => a.
  rewrite addn0.
  rewrite -[RHS]bindmret.
  bind_ext.
  by case.
rewrite /sum -add1n loop1 /liftC bindA; bind_ext => m.
rewrite -/(sum n) {}ih -bindA.
rewrite putget bindA bindretf putput.
congr put.
by rewrite add0n (addnC 1) iotaD /= sumn_cat /= add0n addn0 /= addnAC addnA.
Qed.

Example sum_from_0_to_10 : M unit :=
  foreach (iota 100 0) (fun i => if i > 90 then
                            abortT tt
                          else
                            liftC (get >>= (fun z => put (z + i)))).

End sum.

End continuation_monad_transformer_examples.

(* laws about lifted fail *)

Lemma bindLfailf (M : failMonad) S :
  BindLaws.left_zero (@bind (stateT S M)) (Lift _ _ ^~ fail).
Proof.
move=> A B g /=; rewrite /liftS; apply boolp.funext => s; rewrite bindfailf.
set x := (X in X >>= _ = _).
by rewrite (_ : x = fail) ?bindfailf// /x bindfailf.
Qed.

Lemma bindmLfail (M : failR0Monad) S :
  BindLaws.right_zero (@bind (stateT S M)) (Lift _ _ ^~ fail).
Proof.
move=> A B m /=; rewrite /liftS/=; apply/boolp.funext => s; rewrite bindfailf.
set x := (X in _ >>= X = _).
rewrite (_ : x = fun=> fail) ?bindmfail//.
by apply/boolp.funext=> -[b s']; rewrite /x/= bindfailf.
Qed.

Section lifting.
Variables (E : functor) (M : monad) (op : E.-operation M)
          (N : monad) (e : monadM M N).
Definition lifting (f : E \o N ~~> N) :=
  forall X : UU0, e X \o op X = f X \o (E # e X).
End lifting.

Section liftingt.
Variables (E : functor) (M : monad) (op : E.-operation M)
          (t : monadT).
Definition lifting_monadT := lifting op (Lift t M).
End liftingt.

Section proposition17.

Section psi.
Variables (E : functor) (M : monad).

Definition psi' (n : E ~~> M) : E \o M ~~> M := fun X => Join \o n (M X).

Lemma natural_psi' (n : E ~> M) : naturality [the functor of E \o M] M (psi' n).
Proof.
move=> A B h; rewrite /psi'.
rewrite -/(Join \o n (M A)) [LHS]compA natural.
by rewrite -compA (natural n).
Qed.

HB.instance Definition _ (n : E ~> M) := isNatural.Build
  [the functor of E \o M] M (psi' n) (natural_psi' n).

Lemma algebraic_psi' (n : E ~> M) : algebraicity (psi' n).
Proof.
move=> A B g t.
rewrite bindE.
rewrite -(compE (M # g)).
rewrite {1}/psi'.
rewrite [in LHS](compA (M # g) Join).
rewrite /=.
rewrite -[in X in _ = Join X]compE.
rewrite -[in RHS](natural n).
transitivity (Join ((M # (Join \o (M # g))) (n (M A) t))); last first.
  rewrite -(compE _ (n (M A)) t).
  congr (Join ((M # _ \o _ ) t)).
  apply boolp.funext => ma.
  by rewrite bindE.
rewrite -[in X in Join X = _]compE.
rewrite (natural join).
rewrite functor_o.
rewrite -[in RHS]FCompE.
rewrite -[RHS]compE.
rewrite [in RHS]compA.
by rewrite joinA.
Qed.

HB.instance Definition _ (n : E ~> M) := isAOperation.Build
  E M (psi' n) (algebraic_psi' n).
Definition psi (n : E ~> M) := [the E.-aoperation M of psi' n].

Lemma psiE (n : E ~> M) A : psi n A = Join \o n (M A).
Proof. by []. Qed.

End psi.

Section phi.
Variables (E : functor) (M : monad).

Definition phi' (op : E.-operation M) : E ~~> M := fun X => op X \o (E # Ret).

Lemma natural_phi' (op : E.-operation M) : naturality E M (phi' op).
Proof.
move=> A B h; rewrite /phi'.
rewrite compA.
rewrite (natural op).
rewrite -compA.
rewrite -[in RHS]compA.
congr (_ \o _).
rewrite /=.
rewrite -2!(@functor_o E).
by rewrite (natural ret) FIdE.
Qed.

HB.instance Definition _ (op : E.-operation M) := isNatural.Build
  E M (phi' op) (natural_phi' op).

Definition phi (op : E.-operation M) := [the _ ~> _ of phi' op].

Lemma phiE (op : E.-operation M) (X : UU0) : phi op X = op X \o (E # Ret).
Proof. by []. Qed.

End phi.

Section bijection.
Variables (E : functor) (M : monad).

Lemma psiK (op : E ~> M) : phi (psi op) = op.
Proof.
apply/nattrans_ext => A.
rewrite phiE /= psiE; apply boolp.funext => m /=.
rewrite -(compE (op _)) -(natural op) -(compE Join).
by rewrite compA joinMret.
Qed.

Lemma phiK (op : E.-aoperation M) : psi (phi op) = op.
Proof.
apply/aoperation_ext => A.
rewrite /=.
rewrite psiE phiE; apply boolp.funext => m /=.
rewrite -(compE (op _)) joinE.
rewrite (algebraic op).
rewrite -(compE (E # _)) -functor_o.
rewrite -(compE (op _)).
set x := _^~ id.
rewrite (_ : x = Join); last first.
  apply boolp.funext => mma.
  by rewrite /x bindE functor_id (*TODO: lemma*).
by rewrite joinretM functor_id compfid.
Qed.

End bijection.
End proposition17.

Section uniform_algebraic_lifting.
Variables (E : functor) (M : monad) (op : E.-aoperation M).
Variables (N : monad) (e : monadM M N).

Definition alifting := psi (e \v phi op).

Lemma aliftingE : alifting =
  (fun X => Join \o e (N X) \o phi op (N X)) :> (_ ~~> _).
Proof. by rewrite /alifting/= /vcomp; unlock. Qed.

Theorem uniform_algebraic_lifting : lifting op e alifting.
Proof.
move=> X.
apply boolp.funext => Y.
rewrite /alifting.
rewrite [in RHS]/=.
rewrite psiE.
rewrite vcompE.
rewrite phiE.
rewrite !compE.
rewrite (_ : (E # Ret) ((E # e X) Y) =
             (E # (M # e X)) ((E # Ret) Y)); last first.
  rewrite -[in LHS]compE -functor_o.
  rewrite -[in RHS]compE -functor_o.
  by rewrite (natural ret) FIdE.
set x := (Z in Join (e (N X) Z)).
rewrite (_ : x =
             (M # e X) (op (M X) ((E # Ret) Y))); last first.
  rewrite -(compE (M # e X)).
  by rewrite (natural op).
transitivity (e X (Join (op (M X) ((E # Ret) Y)))); last first.
  rewrite joinE.
  rewrite monadMbind.
  rewrite bindE -(compE _ (M # e X)).
  by rewrite -natural.
by rewrite -[in LHS](phiK op).
Qed.
End uniform_algebraic_lifting.

HB.mixin Record isFunctorial (t : monad -> monad) := {
  hmap : forall {M N : monad}, (M ~> N) -> t M ~> t N ;
  functorial_id : forall M : monad,
    hmap [the _ ~> _ of NId M] = [the _ ~> _ of NId (t M)] ;
  functorial_o : forall (M N P : monad) (t : M ~> N) (s : N ~> P),
    hmap (s \v t) = hmap s \v hmap t }.

#[short(type=functorial)]
HB.structure Definition Functorial := {t of isFunctorial t}.
Arguments hmap _ {M N} _.

HB.mixin Record isFMT (t : monad -> monad) of MonadT t & Functorial t := {
  fmt_ret : forall M N (e : monadM M N),
    MonadMLaws.ret (hmap [the functorial of t] e) ;
  fmt_bind : forall M N (e : monadM M N),
    MonadMLaws.bind (hmap [the functorial of t] e) ;
  natural_hmap : forall (M N : monad) (n : M ~> N),
    hmap [the functorial of t] n \v Lift [the monadT of t] M =
    Lift [the monadT of t] N \v n }.

#[short(type=fmt)]
HB.structure Definition FMT := {t of isFMT t & isFunctorial t & isMonadT t}.

Section fmt_lemmas.

Lemma natural_hmapE (t : fmt) (M N : monad) (n : M ~> N) (X : UU0) :
  hmap t n X \o Lift t M X = Lift t N X \o n X.
Proof.
have /nattrans_ext/(_ X)/= := @natural_hmap t M N n.
by rewrite !vcompE.
Qed.

End fmt_lemmas.

Section exceptFMT.
Variable X : UU0.
Let T := [the monadT of exceptT X].
Definition hmapX' (F G : monad) (tau : F ~> G) : T F ~~> T G :=
  fun (A : UU0) t => tau _ t.

Let naturality_hmapX' (F G : monad) (tau : F ~> G) :
  naturality (T F) (T G) (hmapX' tau).
Proof.
move=> A B h.
by rewrite /hmapX' 2!MX_mapE (natural tau).
Qed.

HB.instance Definition hmapX (F G : monad) (tau : F ~> G) :=
  isNatural.Build (T F) (T G) (hmapX' tau) (naturality_hmapX' tau).

Let hmapX_NId (M : monad) :
  [the _ ~> _ of hmapX' [the _ ~> _ of NId M]] = [the _ ~> _ of NId (T M)].
Proof. by apply/nattrans_ext => A. Qed.

Let hmapX_v (M N P : monad) (t : M ~> N) (s : N ~> P) :
  [the _ ~> _ of hmapX' (s \v t)] =
  [the _ ~> _ of hmapX' s] \v [the _ ~> _ of hmapX' t].
Proof.
by apply/nattrans_ext => /= A; rewrite vcompE /= /hmapX'/= vcompE.
Qed.

HB.instance Definition _ := isFunctorial.Build (exceptT X) hmapX_NId hmapX_v.

Let monadMret_hmapX (F G : monad) (e : monadM F G) :
  MonadMLaws.ret (hmapX' e).
Proof.
move=> A; apply boolp.funext => /= a.
by rewrite /hmapX' /retX /= -(compE (e _)) monadMret.
Qed.

Let monadMbind_hmapX (F G : monad) (e : monadM F G) :
  MonadMLaws.bind (hmapX' e).
Proof.
move=> A B m f; rewrite /hmapX' /=.
rewrite !bindE /= !MX_mapE /bindX /= !bind_fmap.
rewrite !monadMbind /=.
congr (bind (e (X + A)%type m) _).
apply boolp.funext => -[x/=|//].
by rewrite -(compE (e _)) monadMret.
Qed.

Let hmapX_lift :
  let h := fun F G FG => [the _ ~> _ of hmapX' FG] in
  forall (M N : monad) (n : M ~> N),
  h M N n \v Lift T M = Lift T N \v n.
Proof.
move=> h M N t; apply/nattrans_ext => A/=; rewrite !vcompE/=.
rewrite /hmapX' /=.
rewrite /liftX /=.
rewrite /retX /=.
apply boolp.funext => ma /=.
rewrite (_ : (fun x : A => Ret (inr x)) = Ret \o inr) //.
rewrite -bind_fmap.
rewrite bindmret.
rewrite (_ : (fun x : A => Ret (inr x)) = Ret \o inr) //.
rewrite -bind_fmap.
rewrite bindmret.
rewrite -(compE (N # inr)).
by rewrite (natural t).
Qed.

HB.instance Definition _ := isFMT.Build (exceptT X)
  monadMret_hmapX monadMbind_hmapX  hmapX_lift.

End exceptFMT.

Section Fmt_stateT.
Variable S : UU0.
Let T := [the monadT of stateT S].
Definition hmapS (F G : monad) (tau : F ~> G) : T F ~~> T G :=
  fun (A : UU0) t s => tau _ (t s).

Let naturality_hmapS (F G : monad) (tau : F ~> G) :
  naturality (T F) (T G) (hmapS tau).
Proof.
move=> A B h.
rewrite /hmapS /=.
have H : forall G, [the monad of stateT S G] # h = [the functor of MS S G] # h by [].
rewrite !H {H}.

apply boolp.funext => m /=.
rewrite !MS_mapE.
apply boolp.funext => s /=.
rewrite -(compE  _ (tau (A * S)%type)).
by rewrite natural.
Qed.

HB.instance Definition _ (F G : monad) (tau : F ~> G) := isNatural.Build
  (T F) (T G) (hmapS tau) (naturality_hmapS tau).

Let hmapS_NId (M : monad) :
  [the _ ~> _ of hmapS [the _ ~> _ of NId M]] = [the _ ~> _ of NId (T M)].
Proof. by apply/nattrans_ext. Qed.

Let hmapS_v (M N P : monad) (t : M ~> N) (s : N ~> P) :
  [the _ ~> _ of hmapS (s \v t)] =
  [the _ ~> _ of hmapS s] \v [the _ ~> _ of hmapS t].
Proof.
by apply/nattrans_ext => A /=; rewrite vcompE/= /hmapS/= vcompE.
Qed.

HB.instance Definition _ := isFunctorial.Build (stateT S) hmapS_NId hmapS_v.

Let monadMret_hmapS (F G : monad) (e : monadM F G) :
  MonadMLaws.ret (hmapS e).
Proof.
move=> A; apply boolp.funext => /= a.
rewrite /hmapS /= /retS /=; apply boolp.funext => s.
by rewrite [in LHS]curryE monadMret.
Qed.

Let monadMbind_hmapS (F G : monad) (e : monadM F G) :
  MonadMLaws.bind (hmapS e).
Proof.
move=> A B m f.
rewrite /hmapS /=; apply boolp.funext => s.
rewrite /= 2!bindE /= !MS_mapE /bindS /= 2!bind_fmap.
by rewrite monadMbind.
Qed.

Let hmapS_lift :
  let h := fun F G FG => [the _ ~> _ of hmapS FG] in
  forall (M N : monad) (n : M ~> N),
  h M N n \v Lift T M = Lift T N \v n.
Proof.
move=> h M N t; apply/nattrans_ext => A /=; rewrite !vcompE/=.
rewrite /hmapS /=.
rewrite /liftS /=.
apply boolp.funext => ma /=.
apply boolp.funext => s /=.
rewrite ![in LHS]bindE ![in LHS]fmapE ![in LHS]bindE.
rewrite 2!(_ : (fun x : A => Ret (x, s)) = Ret \o (fun x => (x, s))) //.
rewrite functor_o.
rewrite -(compE Join (_ \o _)).
rewrite (compA Join (M # _)).
rewrite joinMret.
rewrite compidf.
rewrite functor_o.
rewrite compA.
rewrite joinMret.
rewrite compidf.
rewrite -(compE _ (t A)).
rewrite -(compE (t _)).
rewrite -natural.
rewrite /=.
rewrite ![in RHS]bindE ![in RHS]fmapE ![in RHS]bindE.
rewrite functor_o.
rewrite -(compE Join (_ \o _)).
rewrite (compA Join (N # _)).
rewrite joinMret.
rewrite compidf.
rewrite functor_o.
rewrite compA.
rewrite joinMret.
rewrite compidf.
by rewrite -(compE _ (t A)).
Qed.

HB.instance Definition _ := isFMT.Build (stateT S)
  monadMret_hmapS monadMbind_hmapS hmapS_lift.

End Fmt_stateT.

Section Fmt_envT.
Variable E : UU0.
Let T := [the monadT of envT E].
Definition hmapEnv (F G : monad) (tau : F ~> G) : T F ~~> T G :=
  fun (A : UU0) t s => tau _ (t s).

Let naturality_hmapEnv (F G : monad) (tau : F ~> G) :
  naturality (T F) (T G) (hmapEnv tau).
Proof.
move=> A B h.
rewrite /hmapEnv.
rewrite /=.
have H : forall G, [the monad of envT E G] # h = [the functor of MEnv E G] # h by [].
rewrite !H {H}.
apply boolp.funext => m /=.
rewrite !MEnv_mapE.
apply boolp.funext => s /=.
rewrite -(compE  _ (tau A)).
by rewrite natural.
Qed.

HB.instance Definition _ (F G : monad) (tau : F ~> G) :=
  isNatural.Build (T F) (T G) (hmapEnv tau) (naturality_hmapEnv tau).

Let hmapEnv_NId (M : monad) :
  [the _ ~> _ of hmapEnv [the _ ~> _ of NId M]] = [the _ ~> _ of NId (T M)].
Proof. by apply nattrans_ext. Qed.

Let hmapEnv_v (M N P : monad) (t : M ~> N) (s : N ~> P) :
  [the _ ~> _ of hmapEnv (s \v t)] =
  [the _ ~> _ of hmapEnv s] \v [the _ ~> _ of hmapEnv t].
Proof. by apply/nattrans_ext => A /=; rewrite vcompE/= /hmapEnv vcompE. Qed.

HB.instance Definition _ := isFunctorial.Build (envT E) hmapEnv_NId hmapEnv_v.

Let monadMret_hmapEnv (F G : monad) (e : monadM F G) :
  MonadMLaws.ret (hmapEnv e).
Proof.
move=> A; apply boolp.funext => /= a.
rewrite /hmapEnv /= /retEnv /=; apply boolp.funext => s.
by rewrite -[LHS](compE _ Ret) monadMret.
Qed.

Let monadMbind_hmapEnv (F G : monad) (e : monadM F G) :
  MonadMLaws.bind (hmapEnv e).
Proof.
move=> A B m f.
rewrite /hmapEnv /=; apply boolp.funext => s.
rewrite /= 2!bindE /= !MEnv_mapE /bindEnv /= 2!bind_fmap.
by rewrite monadMbind.
Qed.

Let hmapEnv_lift :
  let h := fun F G FG => [the _ ~> _ of hmapEnv FG] in
  forall (M N : monad) (n : M ~> N),
  h M N n \v Lift T M = Lift T N \v n.
Proof.
move=> h M N t; apply/nattrans_ext => A /=; rewrite !vcompE/=.
by rewrite /hmapEnv/= /liftEnv/=; exact: boolp.funext.
Qed.

HB.instance Definition _ := isFMT.Build (envT E)
  monadMret_hmapEnv monadMbind_hmapEnv hmapEnv_lift.

End Fmt_envT.

Section Fmt_outputT.
Variable R : UU0.
Let T := [the monadT of outputT R].
Definition hmapO (F G : monad) (tau : F ~> G) : T F ~~> T G :=
  fun (A : UU0) => tau _.

Let naturality_hmapO (F G : monad) (tau : F ~> G) :
  naturality (T F) (T G) (hmapO tau).
Proof.
move=> A B h.
rewrite /hmapO.
rewrite /=.
have H : forall G, [the monad of outputT R G] # h = [the functor of MO R G] # h by [].
rewrite !H {H}.
apply boolp.funext => m /=; rewrite !MO_mapE.
rewrite -[in LHS](compE  _ (tau _)).
by rewrite natural.
Qed.

HB.instance Definition _ (F G : monad) (tau : F ~> G) :=
  isNatural.Build (T F) (T G) (hmapO tau) (naturality_hmapO tau).

Let hmapO_NId (M : monad) :
  [the _ ~> _ of hmapO [the _ ~> _ of NId M]] = [the _ ~> _ of NId (T M)].
Proof. by apply nattrans_ext. Qed.

Let hmapO_v (M N P : monad) (t : M ~> N) (s : N ~> P) :
  [the _ ~> _ of hmapO (s \v t)] =
  [the _ ~> _ of hmapO s] \v [the _ ~> _ of hmapO t].
Proof. by apply/nattrans_ext => A /=; rewrite vcompE/= /hmapO/= vcompE. Qed.

HB.instance Definition _ := isFunctorial.Build (outputT R) hmapO_NId hmapO_v.

Let monadMret_hmapO (F G : monad) (e : monadM F G) :
  MonadMLaws.ret (hmapO e).
Proof.
move=> A; apply boolp.funext => /= a; rewrite /hmapO /= /retO /=.
by rewrite -[LHS](compE _ Ret) monadMret.
Qed.

Let monadMbind_hmapO (F G : monad) (e : monadM F G) :
  MonadMLaws.bind (hmapO e).
Proof.
move=> A B m f.
rewrite /hmapO /=.
rewrite 2!bindE /= !MO_mapE /bindO /= 2!bind_fmap.
rewrite !monadMbind.
bind_ext => -[x w].
rewrite /retO /=.
rewrite monadMbind.
bind_ext => /= -[h t] /=.
rewrite -[LHS](compE _ Ret (h, _)).
by rewrite monadMret.
Qed.

Let hmapO_lift :
  let h := fun F G FG => [the _ ~> _ of hmapO FG] in
  forall (M N : monad) (n : M ~> N),
  h M N n \v Lift T M = Lift T N \v n.
Proof.
move=> h M N t; apply/nattrans_ext => A /=; rewrite !vcompE/=.
rewrite /hmapO /= /liftO /=.
apply boolp.funext => ma /=.
rewrite -!fmapE.
rewrite -(compE _ (t A)).
by rewrite natural.
Qed.

HB.instance Definition _ := isFMT.Build (outputT R)
  monadMret_hmapO monadMbind_hmapO hmapO_lift.

End Fmt_outputT.
