(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2020 monae authors, license: LGPL-2.1-or-later               *)
From mathcomp Require Import all_ssreflect.
Require Import imonae_lib.
From HB Require Import structures.
Require Import ihierarchy imonad_lib ifail_lib istate_lib.

(******************************************************************************)
(*                    Formalization of monad transformers                     *)
(*                                                                            *)
(* This file corresponds to the formalization of [Mauro Jaskelioff, Modular   *)
(* Monad Transformers, ESOP 2009] (roughly, up to Sect. 5, Example 22).       *)
(*                                                                            *)
(* Module MonadMLaws  == laws of monad morphisms                              *)
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
(*                FMT == functorial monad transformer                         *)
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

Module monadM.
Section monadm.
Variables (M N : monad).
Record mixin_of (e : M ~~> N) := Mixin
  {_ : MonadMLaws.ret e ; _ : MonadMLaws.bind e }.
Structure t := Pack { e : M ~~> N ; class : mixin_of e }.
End monadm.
Module Exports.
Notation monadM := t.
Coercion e : monadM >-> Funclass.
End Exports.
End monadM.
Export monadM.Exports.

Section monadM_interface.
Variables (M N : monad) (f : monadM M N).
Lemma monadMret A : f A \o Ret = Ret.
Proof. by case: f => ? []. Qed.
Lemma monadMbind A B (m : M A) (h : A -> M B) :
  f _ (m >>= h) = f _ m >>= (f _ \o h).
Proof. by case: f => ? []. Qed.
End monadM_interface.

Section monadM_lemmas.
Variables (M N : monad) (e : monadM M N).
Lemma natural_monadM : naturality M N e.
Proof.
move=> A B h; apply fun_ext => m /=.
by rewrite !fmapE monadMbind (compA (e B)) monadMret.
Qed.
End monadM_lemmas.

Canonical monadM_nt (M N : monad) (e : monadM M N) : M ~> N :=
  Natural.Pack (Natural.Mixin (natural_monadM e)).

HB.mixin Record isMonadT (T : monad -> monad) := {
  liftT : forall M : monad, monadM M (T M)
}.
HB.structure Definition MonadT := {T of isMonadT T}.
Notation monadT := MonadT.type.
Definition Lift (s : monadT) (M : monad) := @liftT s M.

(*Module MonadT.
Record mixin_of (T : monad -> monad) := Mixin {
  liftT : forall M : monad, monadM M (T M) }.
Record t := Pack {m : monad -> monad ; class : mixin_of m}.
Module Exports.
Notation monadT := t.
Coercion m : monadT >-> Funclass.
Definition Lift (T : t) : forall M : monad, monadM M (m T M) :=
  let: Pack _ (Mixin f) := T return forall M : monad, monadM M (m T M) in f.
Arguments Lift _ _ : simpl never.
End Exports.
End MonadT.
Export MonadT.Exports.*)

Section state_monad_transformer.
Variables (S : UU0) (M : monad).

Definition MS := fun A : UU0 => S -> M (A * S)%type.

Definition retS (A : UU0) : A -> MS A := curry Ret.

Definition bindS A B (m : MS A) f : MS B := fun s => m s >>= uncurry f.

Definition MS_map (A B : UU0) (f : A -> B) (m : MS A) : MS B :=
  (M # (fun x => (f x.1, x.2))) \o m.

Local Lemma MS_map_i : FunctorLaws.id MS_map.
Proof.
move=> A; apply fun_ext => m.
rewrite /MS_map; apply fun_ext => s.
rewrite (_ : (fun x : A * S => _) = id) ?functor_id //.
by apply fun_ext; case.
Qed.

Local Lemma MS_map_o : FunctorLaws.comp MS_map.
Proof.
move=> A B C g h; rewrite /MS_map; apply fun_ext => m.
by apply fun_ext => s /=; rewrite -[RHS]compE -functor_o.
Qed.

HB.instance Definition _ := isFunctor.Build MS MS_map_i MS_map_o.

Local Lemma naturality_retS : naturality FId [the functor of MS] retS.
Proof.
move=> A B h; rewrite /actm /=; apply fun_ext => a /=.
rewrite /MS_map /=; apply fun_ext => s /=.
by rewrite /retS [in LHS]curryE (natural ret).
Qed.

Canonical retS_natural : FId ~> MS :=
  Natural.Pack (Natural.Mixin naturality_retS).

Local Lemma bindSretf : BindLaws.left_neutral bindS retS_natural.
Proof.
by move=> A B a f; rewrite /bindS; apply fun_ext => s; rewrite bindretf.
Qed.

Local Lemma bindSmret : BindLaws.right_neutral bindS retS_natural.
Proof.
move=> A m; rewrite /bindS; apply fun_ext => s.
by rewrite -[in RHS](bindmret (m s)); bind_ext; case.
Qed.

Local Lemma bindSA : BindLaws.associative bindS.
Proof.
move=> A B C m f g; rewrite /bindS; apply fun_ext => s.
by rewrite bindA; bind_ext; case.
Qed.

Local Lemma MS_mapE (A B : UU0) (f : A -> B) (m : MS A) :
  ([the functor of MS] # f) m = bindS m (@retS_natural _ \o f).
Proof.
rewrite /bindS; apply fun_ext => s.
rewrite (_ : _ # f = MS_map f) // /MS_map [LHS]/= fmapE; congr bind.
by apply fun_ext => -[].
Qed.

HB.instance Definition _ :=
  Monad_of_ret_bind.Build MS MS_mapE bindSretf bindSmret bindSA.

(*Definition stateTmonad : monad := Monad.Pack stateTmonad_mixin.*)

Definition liftS A (m : M A) : MS A := fun s => m >>= (fun x => Ret (x, s)).

Local Lemma retliftS : MonadMLaws.ret liftS.
Proof.
move=> A; rewrite /liftS; apply fun_ext => a /=; apply fun_ext => s /=.
by rewrite bindretf.
Qed.

Local Lemma bindliftS : MonadMLaws.bind liftS.
Proof.
move=> A B m f; rewrite {1}/liftS; apply fun_ext => s.
rewrite [in LHS]bindA.
transitivity (bind (liftS m s) (uncurry (liftS (A:=B) \o f))) => //.
rewrite [in RHS]bindA.
bind_ext => a.
by rewrite [in RHS]bindretf.
Qed.

Definition stateTmonadM : monadM M [the monad of MS] :=
  monadM.Pack (@monadM.Mixin _ _ liftS retliftS bindliftS).

End state_monad_transformer.

Definition stateT S : monadT := MonadT.Pack (MonadT.Class (isMonadT.Build _ (stateTmonadM S))).

Definition mapStateT2 (A S : UU0) (N1 N2 N3 : monad)
    (f : N1 (A * S)%type -> N2 (A * S)%type -> N3 (A * S)%type)
    (m1 : stateT S N1 A) (m2 : stateT S N2 A) : stateT S N3 A :=
  fun s => f (m1 s) (m2 s).

Lemma liftSE S (M : monad) U (m : M U) : liftS m = Lift (stateT S) M U m.
Proof. by []. Qed.

Section stateMonad_of_stateT.
Variables (S : UU0) (M : monad).

Let Put : S -> MS S M unit := fun s _ : S => @ret M (unit * S)%type (tt, s).
Let Get : MS S M S := fun s : S => @ret M (S * S)%type (s, s).

Local Lemma bindputput (s s' : S) : @bind (stateT S M) _ _ (Put s) (fun=> Put s') = Put s'.
Proof.
rewrite bindE /= /join_of_bind /= /bindS /=; apply fun_ext => s0 /=.
by rewrite bind_fmap {1}/Put bindretf.
Qed.

Local Lemma bindputget (s : S) : @bind (stateT S M) _ _ (Put s) (fun=> Get) =
                 @bind (stateT S M) _ _ (Put s) (fun=> ret S s).
Proof.
apply fun_ext => s0.
by rewrite !bindE /= /join_of_bind /= /bindS /= !bind_fmap /= 2!bindretf.
Qed.

Local Lemma bindgetput : @bind (stateT S M) _ _ Get Put = skip.
Proof.
apply fun_ext => s.
rewrite !bindE /= /join_of_bind /= /bindS /=.
by rewrite bind_fmap bindretf.
Qed.

Local Lemma bindgetget (A : UU0) (k : S -> S -> stateT S M A) :
  @bind (stateT S M) _ _ Get (fun s => @bind (stateT S M) _ _ Get (k s)) =
  @bind (stateT S M) _ _ Get (fun s => k s s).
Proof.
apply fun_ext => s.
rewrite !bindE !MS_mapE /bindS /= /join_of_bind /= /bindS /= !bindretf /=.
by rewrite bindE /= /join_of_bind /= /bindS bind_fmap bindretf.
Qed.

HB.instance Definition _ := @isMonadState.Build S (MS S M) Get Put
  bindputput bindputget bindgetput bindgetget.

End stateMonad_of_stateT.

(*Definition stateMonad_of_stateT_mixin S (M : monad) :
  isMonadState S (stateT S M).
Proof.
xxxx

Canonical stateMonad_of_stateT S M :=
  MonadState.Pack (MonadState.Class (stateMonad_of_stateT_mixin S M)).*)

Section exception_monad_transformer.

Local Obligation Tactic := idtac.

Variables (Z : UU0) (* the type of exceptions *) (M : monad).

(* action on objects of the transformed monad *)
Definition MX := fun X : UU0 => M (Z + X)%type.

(* unit and bind operator of the transformed monad *)
Definition retX X x : MX X := Ret (inr x).

Definition bindX X Y (t : MX X) (f : X -> MX Y) : MX Y :=
  t >>= fun c => match c with inl z => Ret (inl z) | inr x => f x end.

Local Open Scope mprog.
Definition MX_map (A B : UU0) (f : A -> B) : MX A -> MX B :=
  M # (fun x => match x with inl y => inl y | inr y => inr (f y) end).
Local Close Scope mprog.

Local Lemma MX_map_i : FunctorLaws.id MX_map.
Proof.
move=> A; apply fun_ext => x.
rewrite /MX in x *.
by rewrite /MX_map (_ : (fun _ => _) = id) ?functor_id //; apply fun_ext; case.
Qed.

Local Lemma MX_map_o : FunctorLaws.comp MX_map.
Proof.
rewrite /MX_map => A B C g h /=.
apply fun_ext => x /=.
rewrite -[RHS]compE -functor_o /=; congr (_ # _).
by apply fun_ext; case.
Qed.

HB.instance Definition _ := isFunctor.Build MX MX_map_i MX_map_o.

Local Lemma naturality_retX : naturality FId [the functor of MX] retX.
Proof.
move=> A B h; rewrite /retX; apply fun_ext => /= a.
by rewrite /actm /= /MX_map -[LHS]compE (natural ret).
Qed.

Definition retX_natural : FId ~> MX :=
  Natural.Pack (Natural.Mixin naturality_retX).

Local Lemma bindXretf : BindLaws.left_neutral bindX retX_natural.
Proof. by move=> A B a f; rewrite /bindX bindretf. Qed.

Local Lemma bindXmret : BindLaws.right_neutral bindX retX_natural.
Proof.
by move=> A m; rewrite /bindX -[in RHS](bindmret m); bind_ext; case.
Qed.

Local Lemma bindXA : BindLaws.associative bindX.
Proof.
move=> A B C m f g; rewrite /bindX bindA; bind_ext; case => //.
by move=> z; rewrite bindretf.
Qed.

Local Lemma MX_mapE (A B : UU0) (f : A -> B) (m : MX A) :
  ([the functor of MX] # f) m = bindX m (@retX_natural _ \o f).
Proof.
rewrite /bindX (_ : _ # f = MX_map f) // /MX_map fmapE; congr bind => /=.
by apply fun_ext => -[|].
Qed.

HB.instance Definition _ :=
  Monad_of_ret_bind.Build MX MX_mapE bindXretf bindXmret bindXA.

Definition liftX X (m : M X) : MX X :=
  m >>= (@ret [the monad of MX] _).

Local Lemma retliftX : MonadMLaws.ret liftX.
Proof.
by move=> A; apply fun_ext => a; rewrite /liftX /= bindretf.
Qed.

Local Lemma bindliftX : MonadMLaws.bind liftX.
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

Definition exceptTmonadM : monadM M [the monad of MX] :=
  monadM.Pack (@monadM.Mixin _ _ liftX retliftX bindliftX).

End exception_monad_transformer.

Definition exceptT Z := MonadT.Pack (MonadT.Class (isMonadT.Build _ (exceptTmonadM Z))).

Lemma liftXE Z (M : monad) U (m : M U) : liftX _ m = Lift (exceptT Z) M U m.
Proof. by []. Qed.

Section failMonad_of_exceptT.
Variable M : monad.
Let N (B : UU0) := M (unit + B)%type.

Let Fail : forall B, N B := fun B => Ret (@inl _ B tt).

Local Lemma bindfail : BindLaws.left_zero (@bind (exceptT unit M)) Fail.
Proof.
move=> A B g.
rewrite /Fail.
by rewrite bindE /= /join_of_bind /bindX /= fmapE /= bindA 2!bindretf.
Qed.

HB.instance Definition _ := @isMonadFail.Build (MX unit M) Fail bindfail.
(*Canonical failMonad_of_exceptT M := MonadFail.Pack (MonadFail.Class (failMonad_of_exceptT_mixin M)).*)

End failMonad_of_exceptT.

Section exceptMonad_of_exceptT.
Variables (M : monad).
Let N (B : UU0) := M (unit + B)%type.

Let Catch (B : UU0) (x : N B) (y : N B) : N B.
apply: (@bind M (unit + B)).
exact: x.
case.
  case.
  exact: y.
move=> b.
apply: ret.
apply: inr.
exact: b.
Defined.

Let Catchmfail : forall A, right_id (@fail [the failMonad of MX unit M] A) (@Catch A).
Proof.
move=> A x.
rewrite /Catch /=.
rewrite /fail /=.
rewrite -[in RHS](bindmret x).
bind_ext.
case=> /=.
  by case => //.
by move=> b.
Qed.

Let Catchfailm : forall A, left_id (@fail [the failMonad of MX unit M] A) (@Catch A).
Proof.
move=> A x; rewrite /N in x *.
by rewrite /Catch /= /fail /= bindretf.
Qed.

Let CatchA : forall A, associative (@Catch A).
Proof.
move=> A x y z; rewrite /Catch bindA.
bind_ext.
case.
  by case.
move=> b.
by rewrite bindretf.
Qed.

Let Catchret : forall (A : UU0) (x : A%type), @left_zero (N A) (N A) (Ret (inr x)) (@Catch A).
Proof.
move=> A /= ua n.
by rewrite /Catch /= bindretf.
Qed.

HB.instance Definition _ :=
  @isMonadExcept.Build (MX unit M) Catch Catchmfail Catchfailm CatchA Catchret.

End exceptMonad_of_exceptT.

Section environment_monad_transformer.

Local Obligation Tactic := idtac.

Variables (R : UU0) (M : monad).

Definition MEnv := fun A : UU0 => R -> M A.

Definition retEnv (A : UU0) : A -> MEnv A := fun a r => Ret a.

Definition bindEnv A B (m : MEnv A) f : MEnv B := fun r => m r >>= (fun a => f a r).

Definition MEnv_map (A B : UU0) (f : A -> B) (m : MEnv A) : MEnv B :=
  (M # f) \o m.

Lemma MEnv_map_i : FunctorLaws.id MEnv_map.
Proof.
move=> A; apply fun_ext => m.
by rewrite /MEnv_map functor_id compidf.
Qed.

Lemma MEnv_map_o : FunctorLaws.comp MEnv_map.
Proof.
move=> A B C g h; rewrite /MEnv_map; apply fun_ext => m /=.
by rewrite [in RHS]compA -functor_o.
Qed.

HB.instance Definition MEnv_functor := isFunctor.Build MEnv MEnv_map_i MEnv_map_o.

Lemma naturality_retEnv : naturality FId [the functor of MEnv] retEnv.
Proof.
move=> A B h; rewrite /actm /=; apply fun_ext => a /=.
rewrite /MEnv_map /retEnv; apply fun_ext => r /=.
by rewrite -[LHS](compE _ Ret) natural FIdf.
Qed.

Definition retEnv_natural : FId ~> MEnv :=
  Natural.Pack (Natural.Mixin naturality_retEnv).

Local Lemma bindEnvretf : BindLaws.left_neutral bindEnv retEnv_natural.
Proof.
by move=> A B a f; rewrite /bindEnv; apply fun_ext => r; rewrite bindretf.
Qed.

Local Lemma bindEnvmret : BindLaws.right_neutral bindEnv retEnv_natural.
Proof.
move=> A m; rewrite /bindEnv; apply fun_ext => r.
rewrite -[in RHS](bindmret (m r)); by bind_ext; case.
Qed.

Local Lemma bindEnvA : BindLaws.associative bindEnv.
Proof.
move=> A B C m f g; rewrite /bindEnv; apply fun_ext => r.
by rewrite bindA; bind_ext; case.
Qed.

Local Lemma MEnv_mapE (A B : UU0) (f : A -> B) (m : MEnv A) :
  ([the functor of MEnv] # f) m = bindEnv m (@retEnv_natural _ \o f).
Proof.
rewrite /bindEnv; apply fun_ext => s.
by rewrite (_ : _ # f = MEnv_map f) // /MEnv_map [LHS]/= fmapE.
Qed.

HB.instance Definition _ :=
  Monad_of_ret_bind.Build MEnv MEnv_mapE bindEnvretf bindEnvmret bindEnvA.

Definition liftEnv A (m : M A) : MEnv A :=
  fun r => m.

Local Lemma retliftEnv : MonadMLaws.ret liftEnv.
Proof. by []. Qed.

Local Lemma bindliftEnv : MonadMLaws.bind liftEnv.
Proof. by []. Qed.

Definition envTmonadM : monadM M [the monad of MEnv] :=
  monadM.Pack (@monadM.Mixin _ _ liftEnv retliftEnv bindliftEnv).

End environment_monad_transformer.

Definition envT E : monadT := MonadT.Pack (MonadT.Class (isMonadT.Build _ (envTmonadM E))).

Lemma liftEnvE E (M : monad) U : @liftEnv _ _ _ = Lift (envT E) M U.
Proof.
case: M => [M [[f fi fo] [r j a b c]]].
by rewrite /= /Lift /= /envTmonadM; unlock.
Qed.

(* traces monad transformer? *)
Section output_monad_transformer.

Local Obligation Tactic := idtac.

Variables (R : UU0) (M : monad).

Definition MO (X : UU0) := M (X * seq R)%type.

Definition retO (A : UU0) : A -> MO A := fun a => Ret (a, [::]).

Definition bindO A B (m : MO A) (f : A -> MO B) : MO B :=
  m >>= (fun o => let: (x, w) := o in f x >>=
  (fun o' => let (x', w') := o' in Ret (x', w ++ w'))).

Definition MO_map (A B : UU0) (f : A -> B) (m : MO A) : MO B :=
  (M # (fun x => (f x.1, x.2))) m.

Lemma MO_map_i : FunctorLaws.id MO_map.
Proof.
move=> A; apply fun_ext => m.
rewrite /MO_map (_ : (fun _ => _) = id) ?functor_id//.
by apply fun_ext; case.
Qed.

Lemma MO_map_o : FunctorLaws.comp MO_map.
Proof.
move=> A B C g h; rewrite /MO_map; apply fun_ext => m /=.
by rewrite -[in RHS](compE _ (M # _)) -functor_o.
Qed.

HB.instance Definition MO_functor := isFunctor.Build MO MO_map_i MO_map_o.

Lemma naturality_retO : naturality FId [the functor of MO] retO.
Proof.
move=> A B h; rewrite /actm /=; apply fun_ext => a /=.
by rewrite /MO_map /retO -[LHS](compE _ Ret) natural FIdf.
Qed.

Definition retO_natural : FId ~> MO :=
  Natural.Pack (Natural.Mixin naturality_retO).

Local Lemma bindOretf : BindLaws.left_neutral bindO retO_natural.
Proof.
move=> A B a f; rewrite /bindO /= bindretf /=.
rewrite (_ : (fun o' : B * seq R => _) = (fun o => Ret o)) ?bindmret //.
by apply fun_ext; case.
Qed.

Local Lemma bindOmret : BindLaws.right_neutral bindO retO_natural.
Proof.
move=> A m; rewrite /bindO /= /retO /= -[RHS]bindmret.
by bind_ext => -[a w]; rewrite bindretf cats0.
Qed.

Local Lemma bindOA : BindLaws.associative bindO.
Proof.
move=> A B C m f g; rewrite /bindO /=.
rewrite bindA; bind_ext; case=> x w.
rewrite !bindA; bind_ext; case=> x' w'.
rewrite !bindA bindretf; bind_ext; case=> x'' w''.
by rewrite bindretf catA.
Qed.

Local Lemma MO_mapE (A B : UU0) (f : A -> B) (m : MO A) :
  ([the functor of MO] # f) m = bindO m (@retO_natural _ \o f).
Proof.
rewrite (_ : _ # f = MO_map f) // /MO_map [LHS]/= fmapE /=; congr bind.
apply fun_ext => -[] /= h t.
by rewrite bindretf /= cats0.
Qed.

HB.instance Definition _ :=
  Monad_of_ret_bind.Build MO MO_mapE bindOretf bindOmret bindOA.

Definition liftO A (m : M A) : MO A :=
  m >>= (fun x => Ret (x, [::])).

Local Lemma retliftO : MonadMLaws.ret liftO.
Proof.
move=> a; rewrite /liftO /= /retO; apply fun_ext => o /=.
by rewrite bindretf.
Qed.

Local Lemma bindliftO : MonadMLaws.bind liftO.
Proof.
move=> A B m f; rewrite {1}/liftO.
rewrite !bindE !fmapE /= /join_of_bind /bindO /=.
rewrite 2!joinE !bindA.
bind_ext => a.
rewrite /=.
rewrite !bindretf /liftO.
rewrite bindA.
bind_ext => b.
rewrite bindretf /=.
by rewrite bindretf.
Qed.

Definition outputTmonadM : monadM M [the monad of MO] :=
  monadM.Pack (@monadM.Mixin _ _ liftO retliftO bindliftO).

End output_monad_transformer.

Definition outputT R : monadT := MonadT.Pack (MonadT.Class (isMonadT.Build _ (outputTmonadM R))).

Lemma liftOE R (M : monad) U : @liftO _ _ _ = Lift (outputT R) M U.
Proof.
case: M => [M [[f fi fo] [r j a b c]]].
by rewrite /= /Lift /= /outputTmonadM; unlock.
Qed.

Section continuation_monad_tranformer.

Local Obligation Tactic := idtac.

Variables (r : UU0) (M : monad).

Definition MC : UU0 -> UU0 := fun A => (A -> M r) -> M r %type.

Definition retC (A : UU0) (a : A) : MC A := fun k => k a.

Definition bindC A B (m : MC A) f : MC B := fun k => m (f^~ k).

Definition MC_map (A B : UU0) (f : A -> B) (m : MC A) : MC B.
move=> Br; apply m => a.
apply Br; exact: (f a).
Defined.

Lemma MC_map_i : FunctorLaws.id MC_map. Proof. by []. Qed.

Lemma MC_map_o : FunctorLaws.comp MC_map. Proof. by []. Qed.

HB.instance Definition _ := isFunctor.Build MC MC_map_i MC_map_o.

Lemma naturality_retC : naturality FId [the functor of MC] retC.
Proof. by []. Qed.

Definition retC_natural : FId ~> MC :=
  Natural.Pack (Natural.Mixin naturality_retC).

Local Lemma bindCretf : BindLaws.left_neutral bindC retC_natural.
Proof. by []. Qed.

Local Lemma bindCmret : BindLaws.right_neutral bindC retC_natural.
Proof. by []. Qed.

Local Lemma bindCA : BindLaws.associative bindC.
Proof. by []. Qed.

Local Lemma MC_mapE (A B : UU0) (f : A -> B) (m : MC A) :
  ([the functor of MC] # f) m = bindC m (@retC_natural _ \o f).
Proof. by []. Qed.

HB.instance Definition _ :=
  Monad_of_ret_bind.Build MC MC_mapE bindCretf bindCmret bindCA.

Definition liftC A (x : M A) : MC A := fun k => x >>= k.

Local Lemma retliftC : MonadMLaws.ret liftC.
Proof.
move => A.
rewrite /liftC; apply fun_ext => a /=.
apply fun_ext => s.
by rewrite bindretf.
Qed.

Local Lemma bindliftC : MonadMLaws.bind liftC.
Proof.
move => A B m f.
rewrite /liftC; apply fun_ext => cont.
by rewrite 3!bindA /=.
Qed.

Definition contTmonadM : monadM M [the monad of MC] :=
  monadM.Pack (@monadM.Mixin _ _ liftC  retliftC bindliftC).

End continuation_monad_tranformer.

Definition contT r : monadT := MonadT.Pack (MonadT.Class (isMonadT.Build _ (contTmonadM r))).

Definition abortT r X (M : monad) A : contT r M A := fun _ : A -> M r => Ret X.
Arguments abortT {r} _ {M} {A}.

Section contMonad_of_contT.
Variables (r : UU0) (M : monad).
Let N := MC r M.

Let Callcc (A B : UU0) : ((A -> N B) -> N A) -> N A :=
  fun k f => k (fun a => fun=> f a) f.

Local Lemma Callcc0 (A B : UU0) (g : (A -> N B) -> N A) (k : B -> N B) :
  @Callcc _ _ (fun f => g (fun x => f x >>= k)) = @Callcc _ _ g.
Proof. by []. Qed.

Local Lemma Callcc1 (A B : UU0) (m : N B) : @Callcc _ _ (fun _ : B -> N A => m) = m.
Proof. by []. Qed.

Local Lemma Callcc2 (A B C : UU0) (m : N A) x (k : A -> B -> N C) :
  @Callcc _ _ (fun f : _ -> N _ => m >>= (fun a => f x >>= (fun b => k a b))) =
  @Callcc _ _ (fun f : _ -> N _ => m >> f x).
Proof. by []. Qed.

Local Lemma Callcc3 (A B : UU0) (m : N A) b :
  @Callcc _ _ (fun f : B -> N B => m >> f b) = @Callcc _ _ (fun _ : B -> N B => m >> Ret b).
Proof. by []. Qed.

HB.instance Definition _ := @isMonadContinuation.Build (MC r M) Callcc
  Callcc0 Callcc1 Callcc2 Callcc3.

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
  (fun i : nat => liftC (get >>= (fun z => put (z + i)) ) ).
(*
Let sum n : stateMonad_of_stateT nat(*TODO: <- was inserted explicitly before*) M unit := for_loop n O
  (fun i : nat => liftC (get >>= (fun z => put (z + i)) ) ).*)

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
rewrite add0n (addnC 1).
rewrite iota_add /= sumn_cat /=.
by rewrite add0n addn0 /= addnAC addnA.
Qed.

Example sum_from_0_to_10 : M unit :=
  foreach (iota 100 0) (fun i => if i > 90 then
                            abortT tt
                          else
                            liftC (get >>= (fun z => put (z + i)))).

End sum.

End continuation_monad_transformer_examples.

(*******************)
(* TODO: lift laws *)
(*******************)

Lemma bindLfailf (M : failMonad) S T U (m : stateT S M U) :
  Lift (stateT S) M T fail >> m = Lift (stateT S) M U fail.
Proof.
rewrite -!liftSE /liftS; apply fun_ext => s.
rewrite bindfailf.
set x := (X in bind X _ = _).
rewrite (_ : x = fail); last first.
  by rewrite /x bindfailf.
by rewrite bindfailf.
Qed.

Section lifting.
Variables (E : functor) (M : monad) (op : E.-operation M)
          (N : monad) (e : monadM M N).
Definition lifting (f : E \O N ~~> N) :=
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

Definition psi' (n : E ~~> M) : E \O M ~~> M :=
  fun X => Join \o n (M X).

Lemma natural_psi' (n : E ~> M) : naturality (E \O M) M (psi' n).
Proof.
move=> A B h; rewrite /psi'.
rewrite -/(Join \o n (M A)) compA natural.
by rewrite -compA (natural n).
Qed.

Definition psi0 (n : E ~> M) : E.-operation M := Natural.Pack (Natural.Mixin (natural_psi' n)).

Lemma algebraic_psi0 (n : E ~> M) : algebraicity (psi0 n).
Proof.
move=> A B g t.
rewrite bindE.
rewrite -(compE (M # g)).
rewrite compA.
rewrite /=.
rewrite -[in X in _ = Join X]compE.
rewrite -[in RHS](natural n).
transitivity (Join ((M # (Join \o (M # g))) (n (M A) t))); last first.
  rewrite -(compE _ (n (M A)) t).
  congr (Join ((M # _ \o _ ) t)).
  apply fun_ext => ma.
  by rewrite bindE.
rewrite -[in X in Join X = _]compE.
rewrite (natural join).
rewrite functor_o.
rewrite -[in RHS]FCompE.
rewrite -[RHS]compE.
rewrite [in RHS]compA.
by rewrite joinA.
Qed.

Definition psi (n : E ~> M) : E.-aoperation M :=
  AOperation.Pack (AOperation.Class (AOperation.Mixin (algebraic_psi0 n))).

Lemma psiE (n : E ~> M) A : (psi n) A = Join \o n (M A).
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
rewrite (natural ret).
by rewrite FIdf.
Qed.

Definition phi (op : E.-operation M) : E ~> M :=
  Natural.Pack (Natural.Mixin (natural_phi' op)).

Lemma phiE (op : E.-operation M) X : phi op X = op X \o (E # Ret).
Proof. by []. Qed.

End phi.

Section bijection.
Variables (E : functor) (M : monad).

Lemma psiK (op : E ~> M) : phi (psi op) = op.
Proof.
apply/nattrans_ext => A.
rewrite phiE psiE; apply fun_ext => m /=.
rewrite -(compE (op _)) -(natural op) -(compE Join).
by rewrite compA joinMret.
Qed.

Lemma phiK (op : E.-aoperation M) : psi (phi op) = op.
Proof.
apply/aoperation_ext => A.
rewrite psiE phiE; apply fun_ext => m /=.
rewrite -(compE (op _)) joinE (algebraic op).
rewrite -(compE (E # _)) -functor_o.
rewrite -(compE (op _)).
set x := _^~ id.
rewrite (_ : x = Join); last first.
  apply fun_ext => mma.
  by rewrite /x bindE functor_id (*TODO: lemma*).
by rewrite joinretM functor_id compfid.
Qed.

End bijection.
End proposition17.

Section uniform_algebraic_lifting.
Variables (E : functor) (M : monad) (op : E.-aoperation M).
Variables (N : monad) (e : monadM M N).

Definition alifting : E.-aoperation N := psi (monadM_nt e \v phi op).

Lemma aliftingE :
  alifting = (fun X => Join \o e (N X) \o phi op (N X)) :> (_ ~~> _).
Proof. by []. Qed.

Theorem uniform_algebraic_lifting : lifting op e alifting.
Proof.
move=> X.
apply fun_ext => Y.
rewrite /alifting !compE psiE vcompE phiE !compE.
rewrite (_ : (E # Ret) ((E # e X) Y) =
             (E # (M # e X)) ((E # Ret) Y)); last first.
  rewrite -[in LHS]compE -functor_o.
  rewrite -[in RHS]compE -functor_o.
  rewrite (natural ret).
  by rewrite FIdf.
rewrite (_ : op (N X) ((E # (M # e X)) ((E # Ret) Y)) =
             (M # e X) (op (M X) ((E # Ret) Y))); last first.
  rewrite -(compE (M # e X)).
  by rewrite (natural op).
transitivity (e X (Join (op (M X) ((E # Ret) Y)))); last first.
  rewrite joinE monadMbind.
  rewrite bindE -(compE _ (M # e X)).
  by rewrite -natural.
by rewrite -[in LHS](phiK op).
Qed.
End uniform_algebraic_lifting.

Definition natural_hmap_lift (t : monadT)
    (h : forall (M N : monad), (M ~> N) -> (t M ~> t N)) :=
  forall (M N : monad) (n : M ~> N) X,
    h M N n X \o Lift t M X = Lift t N X \o n X.

Module Fmt.
Section functorial_monad_transformer.
Record mixin_of (t : monadT) := Class {
  hmap : forall (M N : monad), (M ~> N) -> (t M ~> t N) ;
  _ : forall M N (e : monadM M N), MonadMLaws.ret (hmap (monadM_nt e)) ;
  _ : forall M N (e : monadM M N), MonadMLaws.bind (hmap (monadM_nt e)) ;
  _ : forall (M : monad), hmap (NId M) = NId (t M) ;
  _ : forall (M N P : monad) (t : M ~> N) (s : N ~> P), hmap s \v hmap t = hmap (s \v t) ;
  _ : natural_hmap_lift hmap }.
Structure t := Pack { m : monadT ; class : mixin_of m }.
End functorial_monad_transformer.
Module Exports.
Notation FMT := t.
Definition Hmap (T : t) : forall (M N : monad), (M ~> N) -> (m T M ~> m T N) :=
  let: Pack _ (Class f _ _ _ _ _) := T return forall (M N : monad), (M ~> N) -> (m T M ~> m T N) in f.
Arguments Hmap _ _ : simpl never.
Coercion m : FMT >-> monadT.
End Exports.
End Fmt.
Export Fmt.Exports.

Section fmt_lemmas.
Lemma fmt_ret (t : FMT) M N (e : monadM M N) :
  MonadMLaws.ret (Hmap t (monadM_nt e)).
Proof. by case: t M N e => m []. Qed.
Lemma fmt_bind (t : FMT) M N (e : monadM M N) :
  MonadMLaws.bind (Hmap t (monadM_nt e)).
Proof. by case: t M N e => m []. Qed.
Lemma fmt_NId (t : FMT) (M : monad) : Hmap t (NId M) = NId (t M).
Proof. by case: t M => m []. Qed.
Lemma fmt_vcomp (t : FMT) (M N P : monad) (n : M ~> N) (s : N ~> P) :
  Hmap t s \v Hmap t n = Hmap t (s \v n).
Proof. by case: t M N P n s => m []. Qed.
Lemma natural_hmap (T : FMT) : natural_hmap_lift (Hmap T).
Proof. by case: T => [? []]. Qed.
End fmt_lemmas.

Section exceptFMT.
Variable X : UU0.
Let T : monadT := exceptT X.
Let hmapX' (F G : monad) (tau : F ~> G) (A : UU0) (t : T F A) : T G A :=
  tau _ t.

Lemma natural_hmapX' (F G : monad) (tau : F ~> G) :
  naturality (T F) (T G) (hmapX' tau).
Proof.
move=> A B h.
rewrite /hmapX'.
have eXh : forall G, exceptT X G # h = MX_map h by [].
by rewrite 2!eXh /MX_map /= (natural tau).
Qed.

Definition hmapX (F G : monad) (tau : F ~> G) : T F ~> T G :=
  Natural.Pack (Natural.Mixin (natural_hmapX' tau)).

Let monadMret_hmapX (F G : monad) (e : monadM F G) :
  MonadMLaws.ret (hmapX (monadM_nt e)).
Proof.
move=> A; apply fun_ext => /= a.
by rewrite /hmapX' /retX /= -(compE (e _)) monadMret.
Qed.

Let monadMbind_hmapX (F G : monad) (e : monadM F G) :
  MonadMLaws.bind (hmapX (monadM_nt e)).
Proof.
move=> A B m f; rewrite /hmapX /= /hmapX' /=.
rewrite !bindE /= /join_of_bind /bindX /= !bind_fmap.
rewrite !monadMbind /=.
congr (bind (e (X + A)%type m) _).
apply fun_ext.
case.
  move=> x /=.
(*  rewrite bindretf.*)
  by rewrite -(compE (e _)) monadMret.
by move=> a /=.
(*rewrite /retX bindretf /=.
rewrite -(compE (e _)) monadMret.
by rewrite bindretf.*)
Qed.

Let hmapX_NId (M : monad) : hmapX (NId M) = NId (T M).
Proof. by apply nattrans_ext. Qed.

Let hmapX_v (M N P : monad) (t : M ~> N) (s : N ~> P) :
  hmapX s \v hmapX t = hmapX (s \v t).
Proof. exact/nattrans_ext. Qed.

Let hmapX_lift : natural_hmap_lift hmapX.
Proof.
move=> M N t A.
rewrite /hmapX /= /hmapX' /=.
rewrite /liftX /=.
rewrite /retX /=.
apply fun_ext => ma /=.
rewrite (_ : (fun x : A => Ret (inr x)) = Ret \o inr) //.
rewrite -bind_fmap.
rewrite bindmret.
rewrite (_ : (fun x : A => Ret (inr x)) = Ret \o inr) //.
rewrite -bind_fmap.
rewrite bindmret.
rewrite -(compE (N # inr)).
by rewrite (natural t).
Qed.

Program Definition exceptFMT : FMT := @Fmt.Pack (exceptT X)
  (@Fmt.Class _ (fun M N nt => hmapX nt) monadMret_hmapX
    monadMbind_hmapX _ hmapX_v hmapX_lift).

End exceptFMT.

Lemma liftFMTXE X (M : monad) U : @liftX _ _ _ = Lift (exceptFMT X) M U.
Proof. by []. Qed.

Section Fmt_stateT.
Variable S : UU0.
Let T : monadT := stateT S.
Definition hmapS' (F G : monad) (tau : F ~> G) (A : UU0) (t : T F A) : T G A :=
  fun s => tau _ (t s).

Lemma natural_hmapS' (F G : monad) (tau : F ~> G) :
  naturality (T F) (T G) (hmapS' tau).
Proof.
move=> A B h.
rewrite /hmapS'.
rewrite /=.
have H : forall G, [the monad of stateT S G] # h = [the functor of MS S G] # h.
  done.
(*  move=> H; apply fun_ext => m.
  rewrite /actm /=.
  rewrite /Monad_of_ret_bind.Map /=.
  rewrite /bindS /MS_map /retS /=.
  apply fun_ext => s.
  set j := uncurry _.
  have -> : j = Ret \o (fun x : A * S => (h x.1, x.2)).
    by apply fun_ext; case.
  by rewrite -fmapE. *)
rewrite !H {H}.
rewrite /= {1}/actm /=.
rewrite /MS_map; apply fun_ext => m; apply fun_ext => s /=.
rewrite -(compE  _ (tau (A * S)%type)).
by rewrite natural.
Qed.

Definition hmapS (F G : monad) (tau : F ~> G) : T F ~> T G :=
  Natural.Pack (Natural.Mixin (natural_hmapS' tau)).

Let monadMret_hmapS (F G : monad) (e : monadM F G) :
  MonadMLaws.ret (hmapS (monadM_nt e)).
Proof.
move=> A; apply fun_ext => /= a.
rewrite /hmapS' /= /retS /=; apply fun_ext => s.
by rewrite [in LHS]curryE monadMret.
Qed.

Let monadMbind_hmapS (F G : monad) (e : monadM F G) :
  MonadMLaws.bind (hmapS (monadM_nt e)).
Proof.
move=> A B m f.
rewrite /hmapS /=; apply fun_ext => s.
rewrite /hmapS' /= 2!bindE /= /join_of_bind /bindS /= 2!bind_fmap.
by rewrite monadMbind.
Qed.

Let hmapS_NId (M : monad) : hmapS (NId M) = NId (T M).
Proof. by apply nattrans_ext. Qed.

Let hmapS_v (M N P : monad) (t : M ~> N) (s : N ~> P) :
  hmapS s \v hmapS t = hmapS (s \v t).
Proof. exact/nattrans_ext. Qed.

Let hmapS_lift : natural_hmap_lift hmapS.
Proof.
move=> M N t A.
rewrite /hmapS /= /hmapS'.
rewrite /Lift /=.
rewrite /stateTmonadM /=.
unlock.
rewrite /=.
rewrite /liftS /=.
apply fun_ext => ma /=.
apply fun_ext => s /=.
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

Program Definition stateFMT : FMT := @Fmt.Pack T
  (@Fmt.Class _ (fun M N nt => hmapS nt) monadMret_hmapS
    monadMbind_hmapS _ hmapS_v hmapS_lift).

End Fmt_stateT.

Section Fmt_envT.
Variable E : UU0.
Let T : monadT := envT E.
Definition hmapEnv' (F G : monad) (tau : F ~> G) (A : UU0) (t : T F A) : T G A :=
  fun s => tau _ (t s).

Lemma natural_hmapEnv' (F G : monad) (tau : F ~> G) :
  naturality (T F) (T G) (hmapEnv' tau).
Proof.
move=> A B h.
rewrite /hmapEnv'.
rewrite /=.
have H : forall G, [the monad of envT E G] # h = [the functor of MEnv E G] # h.
  done.
(*  move=> H; apply fun_ext => m.
  rewrite /actm /=.
  rewrite /Monad_of_ret_bind.Map /=.
  rewrite /bindEnv /MEnv_map /retEnv /=; apply fun_ext => s.
  by rewrite (_ : (fun a : A => _) = Ret \o h) // -fmapE.*)
rewrite !H {H}.
rewrite {1}/actm /=.
rewrite /MEnv_map; apply fun_ext => m; apply fun_ext => s /=.
rewrite -(compE  _ (tau A)).
by rewrite natural.
Qed.

Definition hmapEnv (F G : monad) (tau : F ~> G) : T F ~> T G :=
  Natural.Pack (Natural.Mixin (natural_hmapEnv' tau)).

Let monadMret_hmapEnv (F G : monad) (e : monadM F G) :
  MonadMLaws.ret (hmapEnv (monadM_nt e)).
Proof.
move=> A; apply fun_ext => /= a.
rewrite /hmapEnv' /= /retEnv /=; apply fun_ext => s.
by rewrite -[LHS](compE _ Ret) monadMret.
Qed.

Let monadMbind_hmapEnv (F G : monad) (e : monadM F G) :
  MonadMLaws.bind (hmapEnv (monadM_nt e)).
Proof.
move=> A B m f.
rewrite /hmapEnv /=; apply fun_ext => s.
rewrite /hmapEnv' /= 2!bindE /= /join_of_bind /bindEnv /= 2!bind_fmap.
by rewrite monadMbind.
Qed.

Let hmapEnv_NId (M : monad) : hmapEnv (NId M) = NId (T M).
Proof. by apply nattrans_ext. Qed.

Let hmapEnv_v (M N P : monad) (t : M ~> N) (s : N ~> P) :
  hmapEnv s \v hmapEnv t = hmapEnv (s \v t).
Proof. exact/nattrans_ext. Qed.

Let hmapEnv_lift : natural_hmap_lift hmapEnv.
Proof.
move=> M N t A.
rewrite /hmapEnv /= /hmapEnv'.
rewrite /Lift /=.
rewrite /envTmonadM /=.
unlock.
rewrite /=.
rewrite /liftEnv /=.
by apply fun_ext.
Qed.

Program Definition envFMT : FMT := @Fmt.Pack T
  (@Fmt.Class _ (fun M N nt => hmapEnv nt) monadMret_hmapEnv
    monadMbind_hmapEnv _ hmapEnv_v hmapEnv_lift).

End Fmt_envT.

Section Fmt_outputT.
Variable R : UU0.
Let T : monadT := outputT R.
Definition hmapO' (F G : monad) (tau : F ~> G) (A : UU0) (t : T F A) : T G A := tau _ t.

Lemma natural_hmapO' (F G : monad) (tau : F ~> G) :
  naturality (T F) (T G) (hmapO' tau).
Proof.
move=> A B h.
rewrite /hmapO'.
rewrite /=.
have H : forall G, [the monad of outputT R G] # h = [the functor of MO R G] # h.
  done.
(*  move=> H; apply fun_ext => m.
  rewrite /actm /=.
  rewrite /Monad_of_ret_bind.Map /=.
  rewrite /MO_map.
  rewrite /bindO /retO /=.
  rewrite fmapE.
  congr (_ >>= _).
  apply fun_ext => -[x w].
  by rewrite bindretf cats0.*)
rewrite !H {H}.
rewrite {1}/actm /=.
rewrite /MO_map; apply fun_ext => m /=.
rewrite -[in LHS](compE  _ (tau _)).
by rewrite natural.
Qed.

Definition hmapO (F G : monad) (tau : F ~> G) : T F ~> T G :=
  Natural.Pack (Natural.Mixin (natural_hmapO' tau)).

Let monadMret_hmapO (F G : monad) (e : monadM F G) :
  MonadMLaws.ret (hmapO (monadM_nt e)).
Proof.
move=> A; apply fun_ext => /= a.
rewrite /hmapO' /= /retO /=.
by rewrite -[LHS](compE _ Ret) monadMret.
Qed.

Let monadMbind_hmapO (F G : monad) (e : monadM F G) :
  MonadMLaws.bind (hmapO (monadM_nt e)).
Proof.
move=> A B m f.
rewrite /hmapO /=.
rewrite /hmapO' /=.
rewrite 2!bindE /= /join_of_bind /bindO /= 2!bind_fmap.
rewrite !monadMbind.
bind_ext => -[x w].
rewrite /retO /=.
rewrite monadMbind.
bind_ext => /= -[h t] /=.
rewrite -[LHS](compE _ Ret (h, _)).
by rewrite monadMret.
Qed.

Let hmapO_NId (M : monad) : hmapO (NId M) = NId (T M).
Proof. by apply nattrans_ext. Qed.

Let hmapO_v (M N P : monad) (t : M ~> N) (s : N ~> P) :
  hmapO s \v hmapO t = hmapO (s \v t).
Proof. exact/nattrans_ext. Qed.

Let hmapO_lift : natural_hmap_lift hmapO.
Proof.
move=> M N t A.
rewrite /hmapO /= /hmapO'.
rewrite /Lift /=.
rewrite /outputTmonadM /=.
unlock.
rewrite /=.
rewrite /liftO /=.
apply fun_ext => ma /=.
rewrite -!fmapE.
rewrite -(compE _ (t A)).
by rewrite natural.
Qed.

Program Definition outputFMT : FMT := @Fmt.Pack T
  (@Fmt.Class _ (fun M N nt => hmapO nt) monadMret_hmapO
    monadMbind_hmapO _ hmapO_v hmapO_lift).

End Fmt_outputT.
