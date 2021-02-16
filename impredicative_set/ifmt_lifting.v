(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2020 monae authors, license: LGPL-2.1-or-later               *)
From mathcomp Require Import all_ssreflect.
Require Import imonae_lib ihierarchy imonad_lib imonad_transformer.

(******************************************************************************)
(*   Uniform Lifting of Sigma-operations Along Functorial Monad Transformers  *)
(*                                                                            *)
(* This file corresponds to the formalization of [Mauro Jaskelioff,           *)
(* Modular Monad Transformers, ESOP 2009] (from Sect. 5, definition 23).      *)
(*                                                                            *)
(*            codensityT == codensity monad transformer                       *)
(*              slifting == definition of a sigma-operation using a           *)
(*                          sigma-operation and a functorial monad            *)
(*                          transformer                                       *)
(* uniform_sigma_lifting == Theorem: given a functiorial monad transformer t, *)
(*                          slifting is a lifting along Lift t                *)
(*       slifting_stateT == lifting of a sigma-operation along stateT         *)
(*      slifting_exceptT == lifting of a sigma-operation along exceptT        *)
(*         slifting_envT == lifting of a sigma-operation along envT           *)
(*      slifting_outputT == lifting of a sigma-operation along outputT        *)
(*   slifting_alifting_* == Lemmas: slifting and alifting of algebraic        *)
(*                          operations coincide                               *)
(*              local_*E == Lemmas: liftings of local                         *)
(*             handle_*E == Lemmas: liftings of handle                        *)
(*              flush_*E == Lemmas: liftings of flush                         *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.

Import Univ.

Definition MK (m : UU0 -> UU0) (A : UU0) :=
  forall (B : UU0), (A -> m B) -> m B.

Section codensity.
Variable (M : monad).

Definition retK (A : UU0) (a : A) : MK M A :=
  fun (B : UU0) (k : A -> M B) => k a.

Definition bindK (A B : UU0) (m : MK M A) f : MK M B :=
  fun (C : UU0) (k : B -> M C) => m C (fun a : A => (f a) C k).

Definition MK_map (A B : UU0) (f : A -> B) (m : MK M A) : MK M B :=
  fun (C : UU0) (k : B -> M C) => m C (fun a : A => k (f a)).

Lemma MK_map_i : FunctorLaws.id MK_map.
Proof.
move=> A; rewrite /MK_map; apply fun_ext => m /=.
apply fun_ext_dep => B.
by apply fun_ext => k.
Qed.

Lemma MK_map_o : FunctorLaws.comp MK_map.
Proof. by []. Qed.

Definition MK_functor := Functor.Pack (Functor.Mixin MK_map_i MK_map_o).

Lemma naturality_retK : naturality FId MK_functor retK.
Proof.
move=> A B h.
rewrite /MK_functor /Actm /= /MK_map /retK /=.
by apply fun_ext => a /=; exact: fun_ext_dep.
Qed.

Definition retK_natural : FId ~> MK_functor :=
  Natural.Pack (Natural.Mixin naturality_retK).

Program Definition codensityTmonad : monad :=
  @Monad_of_ret_bind MK_functor retK_natural bindK _ _ _.
Next Obligation.
move=> A B a f; rewrite /bindK /=.
by apply fun_ext_dep => C; apply fun_ext.
Qed.
Next Obligation.
move=> A m; rewrite /bindK /retK.
by apply fun_ext_dep => C; apply fun_ext.
Qed.
Next Obligation. by move=> A B C m f g; rewrite /bindK; exact: fun_ext_dep. Qed.

Definition liftK (A : UU0) (m : M A) : codensityTmonad A :=
  fun (B : UU0) (k : A -> M B) => m >>= k.

Program Definition codensityTmonadM : monadM M codensityTmonad :=
  locked (monadM.Pack (@monadM.Mixin _ _ liftK _ _)).
Next Obligation.
move=> A; rewrite /liftK /= /retK /=.
apply fun_ext => a; apply fun_ext_dep => B /=.
by apply fun_ext => b; rewrite bindretf.
Qed.
Next Obligation.
move=> A B m f; rewrite /liftK.
apply fun_ext_dep => C /=; apply fun_ext => g.
by rewrite bindA.
Qed.

End codensity.

Definition codensityT : monadT :=
  MonadT.Pack (@MonadT.Mixin codensityTmonad codensityTmonadM).

Section kappa.
Variables (M : monad) (E : functor) (op : E.-operation M).

Definition kappa' : E ~~> codensityT M :=
  fun (A : UU0) (s : E A) (B : UU0) (k : A -> M B) =>
    op B ((E # k) s).

Lemma natural_kappa' : naturality _ _ kappa'.
Proof.
move=> A B h; rewrite /kappa'; apply fun_ext => ea; rewrite [in RHS]/=.
transitivity (fun B0 (k : B -> M B0) => op B0 ((E # (k \o h)) ea)) => //.
by apply fun_ext_dep => C; apply fun_ext => D; rewrite functor_o.
Qed.

Definition kappa := Natural.Pack (Natural.Mixin natural_kappa').

Lemma kappaE X : kappa X = (fun (s : E X) (B : UU0) (k : X -> M B) => op B ((E # k) s)).
Proof. by []. Qed.

End kappa.

Definition naturality_MK (M : functor) (A : UU0) (m : MK M A) :=
  naturality (exponential_F A \O M) M m.

Section from.
Variables (M : monad).

Definition from_component : codensityT M ~~> M :=
  fun (A : UU0) (c : codensityT M A) => c A Ret.

Hypothesis naturality_MK : forall (A : UU0) (m : MK M A),
  naturality_MK m.

Lemma natural_from_component : naturality (codensityT M) M from_component.
Proof.
move=> A B h; apply fun_ext => m /=.
transitivity (m B (Ret \o h)) => //. (* by definition of from *)
rewrite -(natural RET).
transitivity ((M # h \o m A) Ret) => //. (* by definition of from *)
by rewrite naturality_MK.
Qed.

Definition from := Natural.Pack (Natural.Mixin natural_from_component).

Lemma from_component_liftK A : @from_component A \o Lift codensityT M A = id.
Proof.
apply fun_ext => m /=.
rewrite /from_component /= /Lift /=.
rewrite /codensityTmonadM /=.
(* TODO *) unlock => /=.
rewrite /liftK /=.
by rewrite bindmret.
Qed.

End from.

Section psi_kappa.
Variables (E : functor) (M : monad) (op : E.-operation M).

Definition psik : E.-aoperation (codensityT M) := psi (kappa op).

Lemma psikE (A : UU0) : op A =
  (@from_component M A) \o (@psik A) \o ((E ## (monadM_nt (Lift codensityT M))) A).
Proof.
apply fun_ext => m /=.
rewrite /from_component /psik /= /psi' /kappa' /fun_app_nt /=.
rewrite /bindK /=.
rewrite -[in RHS]compE.
rewrite -[in RHS]compE.
rewrite -compA.
rewrite -functor_o.
rewrite from_component_liftK.
rewrite functor_id.
by rewrite compfid.
Qed.

End psi_kappa.

Section uniform_sigma_lifting.
Variables (E : functor) (M : monad) (op : E.-operation M) (t : FMT).
Hypothesis naturality_MK : forall (A : UU0) (m : MK M A),
  naturality_MK m.

Let op1 : t (codensityT M) ~> t M := Hmap t (from naturality_MK).
Let op2 := alifting (psik op) (Lift t _).
Let op3 : E \O t M ~> E \O t (codensityT M) :=
  E ## Hmap t (monadM_nt (Lift codensityT M)).

Definition slifting : E.-operation (t M) := op1 \v op2 \v op3.

Theorem uniform_sigma_lifting : lifting_monadT op slifting.
Proof.
rewrite /lifting_monadT /slifting => X.
apply/esym.
transitivity ((op1 \v op2) X \o op3 X \o E # Lift t M X).
  by rewrite (vassoc op1).
rewrite -compA.
transitivity ((op1 \v op2) X \o
  ((E # Lift t (codensityT M) X) \o (E # Lift codensityT M X))).
  congr (_ \o _); rewrite /op3.
  by rewrite -functor_o -natural_hmap functor_o functor_app_naturalE.
transitivity (op1 X \o
  (op2 X \o E # Lift t (codensityT M) X) \o E # Lift codensityT M X).
  by rewrite vcompE -compA.
rewrite -uniform_algebraic_lifting.
transitivity (Lift t M X \o from naturality_MK X \o (psik op) X \o
  E # Lift codensityT M X).
  congr (_ \o _).
  by rewrite compA natural_hmap.
rewrite -2!compA.
congr (_ \o _).
by rewrite compA -psikE.
Qed.
End uniform_sigma_lifting.

(* example 29 *)
Section slifting_instances.

Variables (E : functor) (M : monad) (op : E.-operation M).
Hypothesis naturality_MK : forall (A : UU0) (m : MK M A),
  naturality_MK m.

Section slifting_stateT.
Variable S : UU0.

Let tau (X : UU0) s (f : S -> M (X * S)%type) := f s.

Let op' X : (E \O stateFMT S M) X -> stateFMT S M X :=
  fun t s => op (X * S)%type ((E # tau s) t).

Lemma slifting_stateT (X : UU0) :
  (slifting op (stateFMT S) naturality_MK) X = @op' _.
Proof.
apply fun_ext => emx.
rewrite /op'.
apply fun_ext => s.
rewrite /slifting.
rewrite 2!vcompE.
set h := Hmap _.
rewrite (psikE op).
rewrite 2!functor_app_naturalE.
rewrite /=.
congr (from_component _).
apply fun_ext_dep => A; apply fun_ext => f.
rewrite {1}/psi' /=.
rewrite /bindS /=.
rewrite -liftSE /liftS /=.
rewrite -(compE _ _ emx) -functor_o.
rewrite -[in RHS](compE _ _ emx) -functor_o.
rewrite bindA.
set ret_id := (X in _ >>= X).
have -> : ret_id = fun (x : MS S (codensityT M) X) (C : UU0) => (fun t => x s C t).
  exact: fun_ext.
rewrite {1}/Bind /= /bindK /= {1}/Actm /=.
rewrite /Monad_of_ret_bind.Map /= /bindK /=.
rewrite /psi' /= /bindK /kappa' /=.
rewrite /retK /= /MK /=.
rewrite -(compE _ _ emx).
rewrite -functor_o.
rewrite -[in RHS](compE _ _ emx).
by rewrite -functor_o.
Qed.

End slifting_stateT.

Section slifting_exceptT.
Variable Z : UU0.

Let op' Y : (E \O exceptFMT Z M) Y -> exceptFMT Z M Y := @op _.

Lemma slifting_exceptT (X : UU0) :
  (slifting op (exceptFMT Z) naturality_MK) X = @op' X.
Proof.
apply fun_ext => emx.
rewrite /op'.
rewrite (psikE op (Z + X)%type).
rewrite /slifting.
rewrite 2!vcompE.
set h := Hmap _.
rewrite /=.
congr (from_component (psi' _ _)).
apply fun_ext_dep => A; apply fun_ext => B; apply fun_ext_dep => C.
rewrite /=.
rewrite /psi'.
rewrite /retK /= /bindK /=.
apply fun_ext => D.
rewrite /kappa'.
congr (op C _).
rewrite -(compE (E # _)).
by rewrite -functor_o.
Qed.

End slifting_exceptT.

Section slifting_envT.
Variable Env : UU0.

Let tau (X : UU0) e (f : Env -> M X) := f e.

Let op' X : (E \O envFMT Env M) X -> envFMT Env M X :=
  fun t => fun e => op X ((E # tau e) t).

Lemma slifting_envT (X : UU0) :
  (slifting op (envFMT Env) naturality_MK) X = @op' _.
Proof.
apply fun_ext => emx.
rewrite /op'.
apply fun_ext => s.
rewrite /slifting.
rewrite 2!vcompE.
set h := Hmap _.
rewrite (psikE op).
rewrite 2!functor_app_naturalE.
rewrite /=.
congr (from_component _).
apply fun_ext_dep => A; apply fun_ext => f.
rewrite {1}/psi' /=.
rewrite /bindEnv /=.
rewrite -liftEnvE /liftEnv /=.
rewrite -(compE _ _ emx) -functor_o.
rewrite -[in RHS](compE _ _ emx) -functor_o.
rewrite /Bind /Join /= /bindK /=.
rewrite {1}/Actm /= /Monad_of_ret_bind.Map /=.
rewrite /bindK.
rewrite /psi' /= /bindK /= /kappa' /=.
congr (op A).
rewrite -(compE _ _ emx) -[in RHS](compE _ _ emx).
by rewrite -2!functor_o.
Qed.

End slifting_envT.

Section slifting_outputT.
Variable R : UU0.

Let op' X : (E \O outputFMT R M) X -> outputFMT R M X :=
  @op (X * seq R)%type.

Lemma slifting_outputT (X : UU0) :
  (slifting op (outputFMT R) naturality_MK) X = @op' _.
Proof.
apply fun_ext => emx.
rewrite /op'.
rewrite /slifting.
rewrite 2!vcompE.
set h := Hmap _.
rewrite (psikE op).
rewrite 2!functor_app_naturalE.
rewrite /=.
congr (from_component _).
apply fun_ext_dep => A; apply fun_ext => f.
rewrite {1}/psi' /=.
rewrite /bindO /=.
rewrite -liftOE /liftO /=.
rewrite -(compE _ _ emx) -functor_o.
rewrite /Bind /Join /= /bindK /=.
rewrite {1}/Actm /= /Monad_of_ret_bind.Map /=.
rewrite /bindK.
rewrite /psi' /= /bindK /= /kappa' /=.
congr (op A).
rewrite -(compE _ _ emx) -[in RHS](compE _ _ emx).
rewrite -2!functor_o.
congr ((E # _) _).
apply fun_ext => rmx /=.
rewrite /retK /= /Actm /= /Monad_of_ret_bind.Map /bindK.
congr (Lift codensityT M _ _ _ _).
by apply fun_ext; case.
Qed.

End slifting_outputT.

End slifting_instances.

(* proposition 28 *)
Section slifting_alifting_coincide.

Variables (E : functor) (M : monad) (aop : E.-aoperation M).
Hypothesis naturality_MK : forall (A : UU0) (m : MK M A),
  naturality_MK m.

Lemma slifting_alifting_stateFMT (S : UU0) (t := stateFMT S) :
  slifting aop t naturality_MK = alifting aop (Lift t M).
Proof.
apply nattrans_ext => X.
rewrite (slifting_stateT aop naturality_MK S).
apply fun_ext => m.
apply fun_ext => s.
rewrite /alifting.
rewrite psiE /= /bindS -liftSE /liftS /=.
rewrite 2!algebraic.
congr (aop _ _).
rewrite -[RHS](compE _ (E # _)).
rewrite -functor_o.
rewrite -[RHS](compE _ (E # _)).
rewrite -functor_o.
congr ((E # _) m).
apply fun_ext => x.
by rewrite /= 2!bindretf.
Qed.

Lemma slifting_alifting_exceptFMT (Z : UU0) (t := exceptFMT Z) :
  slifting aop t naturality_MK = alifting aop (Lift t M).
Proof.
apply nattrans_ext => X.
rewrite (slifting_exceptT aop naturality_MK Z).
apply fun_ext => m.
rewrite /alifting.
rewrite psiE /= /bindX /liftX.
rewrite 2!algebraic.
congr (aop _ _).
rewrite -[RHS](compE _ (E # _)).
rewrite -functor_o.
rewrite -[RHS](compE _ (E # _)).
rewrite -functor_o.
rewrite (_ : _ \o _ = id) ?functor_id //.
apply fun_ext => n /=.
by rewrite 2!bindretf.
Qed.

Lemma slifting_alifting_envFMT (Env : UU0) (t := envFMT Env) :
  slifting aop t naturality_MK = alifting aop (Lift t M).
Proof.
apply nattrans_ext => X.
rewrite (slifting_envT aop naturality_MK Env).
apply fun_ext => m.
apply fun_ext => e.
rewrite /alifting.
rewrite psiE /= /bindEnv -liftEnvE /liftEnv.
rewrite algebraic.
congr (aop _ _).
rewrite -[RHS](compE _ (E # _)).
rewrite -functor_o.
congr ((E # _) m).
apply fun_ext => x.
by rewrite /= bindretf.
Qed.

Lemma slifting_alifting_outputFMT (R : UU0) (t := outputFMT R) :
  slifting aop t naturality_MK = alifting aop (Lift t M).
Proof.
apply nattrans_ext => X.
rewrite (slifting_outputT aop naturality_MK R).
apply fun_ext => m.
rewrite /alifting.
rewrite psiE /= /bindO -liftOE /liftO.
rewrite 2!algebraic.
congr (aop _ _).
rewrite -[RHS](compE _ (E # _)).
rewrite -functor_o.
rewrite -[RHS](compE _ (E # _)).
rewrite -functor_o.
rewrite (_ : _ \o _ = id) ?functor_id //.
apply fun_ext => n /=.
rewrite 2!bindretf.
Open (X in _ >>= X).
 by case : x => ? ?; rewrite cat0s.
by rewrite bindmret.
Qed.

End slifting_alifting_coincide.

Require Import imonad_model.

(* example 30 *)
Section slifting_local.
Variable Env : UU0.
Let E := imonad_model.EnvironmentOps.Local.func Env.
Let M := imonad_model.ModelMonad.Environment.t Env.
Let local : E.-operation M := imonad_model.EnvironmentOps.local_op Env.
Hypothesis naturality_MK : forall (A : UU0) (m : MK M A),
  naturality_MK m.

Section slifting_local_FMT.
Variable T : FMT.

Definition localKT (X : UU0) (f : Env -> Env) (t : T (codensityT M) X)
    : T (codensityT M) X :=
  Join (Lift T (codensityT M) (T (codensityT M) X) (fun Y k => local Y (f, k t))).

Definition localT (X : UU0) (f : Env -> Env) (t : T M X) : T M X :=
  let t' := Hmap T (monadM_nt (Lift codensityT M)) X t in
  Hmap T (from naturality_MK) X (localKT f t').

End slifting_local_FMT.

Section slifting_local_stateT.
Variable S : UU0.

Definition local_stateT (X : UU0) (f : Env -> Env) (t : stateFMT S M X)
    : stateFMT S M X
  := fun s e => t s (f e).

Let local_stateT' (X : UU0) : (E \O stateFMT S M) X -> (stateFMT S M) X :=
  uncurry (@local_stateT X).

Lemma local_stateTE (X : UU0) :
  (slifting local (stateFMT S) naturality_MK) X = @local_stateT' X.
Proof.
rewrite slifting_stateT.
by apply fun_ext => -[].
Qed.
End slifting_local_stateT.

Section slifting_local_exceptT.
Variable Z : UU0.
Definition local_exceptT (X : UU0) (f : Env -> Env) (t : exceptFMT Z M X)
    : exceptFMT Z M X
  := fun e => t (f e).

Let local_exceptT' (X : UU0) : (E \O exceptFMT Z M) X -> (exceptFMT Z M) X :=
  uncurry (@local_exceptT X).

Lemma local_exceptTE (X : UU0) :
  (slifting local (exceptFMT Z) naturality_MK) X = @local_exceptT' X.
Proof.
rewrite slifting_exceptT.
by apply fun_ext => -[].
Qed.

End slifting_local_exceptT.

Section slifting_local_envT.
Variable Z : UU0.
Definition local_envT (X : UU0) (f : Env -> Env) (t : envFMT Z M X)
    : envFMT Z M X :=
  fun e e' => t e (f e').

Let local_envT' (X : UU0) : (E \O envFMT Z M) X -> (envFMT Z M) X :=
  uncurry (@local_envT X).

Lemma local_envTE (X : UU0) :
  (slifting local (envFMT Z) naturality_MK) X = @local_envT' X.
Proof.
rewrite slifting_envT.
by apply fun_ext => -[].
Qed.
End slifting_local_envT.

Section slifting_local_outputT.
Variable R : UU0.
Definition local_outputT (X : UU0) (f : Env -> Env) (t : outputFMT R M X)
    : outputFMT R M X :=
  fun e => t (f e).

Let local_outputT' (X : UU0) : (E \O outputFMT R M) X -> (outputFMT R M) X :=
  uncurry (@local_outputT X).

Lemma local_outputTE (X : UU0) :
  (slifting local (outputFMT R) naturality_MK) X = @local_outputT' X.
Proof.
rewrite slifting_outputT.
by apply fun_ext; case.
Qed.
End slifting_local_outputT.

End slifting_local.

(* example 31 *)
Section slifting_handle. (* except monad with Z = unit *)
Let E := imonad_model.ExceptOps.Handle.func unit.
Let M := imonad_model.ModelExcept.t.
Let handle : E.-operation M := @imonad_model.ExceptOps.handle_op unit.
Hypothesis naturality_MK : forall (A : UU0) (m : MK M A),
  naturality_MK m.

Section slifting_handle_stateT.
Variable S : UU0.
Definition handle_stateT (X : UU0) (t : stateFMT S M X) (h : unit -> stateFMT S M X)
  : stateFMT S M X := fun s => match t s with
    | inl z(*unit*) => h z s
    | inr x => inr x
    end.

Let handle_stateT' (X : UU0) : (E \O stateFMT S M) X -> (stateFMT S M) X :=
  uncurry (@handle_stateT X).

Lemma handle_stateTE (X : UU0) :
  (slifting handle (stateFMT S) naturality_MK) X = @handle_stateT' X.
Proof.
rewrite slifting_stateT.
apply fun_ext => -[m f].
by apply fun_ext.
Qed.
End slifting_handle_stateT.

Section slifting_handle_exceptT.
Variable Z : UU0.
Definition handle_exceptT (X : UU0) (t : exceptFMT Z M X) (h : unit -> exceptFMT Z M X)
  : exceptFMT Z M X := match t with
    | inl z(*unit*) => h z
    | inr x => inr x
    end.

Let handle_exceptT' (X : UU0) : (E \O exceptFMT Z M) X -> (exceptFMT Z M) X :=
  uncurry (@handle_exceptT X).

Lemma handle_exceptTE (X : UU0) :
  (slifting handle (exceptFMT Z) naturality_MK) X = @handle_exceptT' X.
Proof.
rewrite slifting_exceptT.
by apply fun_ext.
Qed.
End slifting_handle_exceptT.

Section slifting_handle_envT.
Variable Z : UU0.
Definition handle_envT (X : UU0) (t : envFMT Z M X) (h : unit -> envFMT Z M X)
  : envFMT Z M X := fun e => match t e with
    | inl z(*unit*) => h z e
    | inr x => inr x
    end.

Let handle_envT' (X : UU0) : (E \O envFMT Z M) X -> (envFMT Z M) X :=
  uncurry (@handle_envT X).

Lemma handle_envTE (X : UU0) :
  (slifting handle (envFMT Z) naturality_MK) X = @handle_envT' X.
Proof.
rewrite slifting_envT.
apply fun_ext => -[m f].
by apply fun_ext.
Qed.
End slifting_handle_envT.

Section slifting_handle_outputT.
Variable R : UU0.
Definition handle_outputT (X : UU0) (t : outputFMT R M X) (h : unit -> outputFMT R M X)
  : outputFMT R M X := match t with
    | inl z(*unit*) => h z
    | inr x => inr x
    end.

Let handle_outputT' (X : UU0) : (E \O outputFMT R M) X -> (outputFMT R M) X :=
  uncurry (@handle_outputT X).

Lemma handle_outputTE (X : UU0) :
  (slifting handle (outputFMT R) naturality_MK) X = @handle_outputT' X.
Proof.
rewrite slifting_outputT.
by apply fun_ext; case.
Qed.
End slifting_handle_outputT.

End slifting_handle.

(* example 32 *)
Section slifting_flush.
Variable R : UU0.
Let E := imonad_model.OutputOps.Flush.func.
Let M := imonad_model.ModelMonad.Output.t R.
Let flush : E.-operation M := @imonad_model.OutputOps.flush_op R.
Hypothesis naturality_MK : forall (A : UU0) (m : MK M A),
  naturality_MK m.

Section slifting_flush_stateT.
Variable S : UU0.
Definition flush_stateT (X : UU0) (t : stateFMT S M X) : stateFMT S M X :=
  fun s => let: (x, _) := t s in (x, [::]).

Lemma flush_stateTE (X : UU0) :
  (slifting flush (stateFMT S) naturality_MK) X = @flush_stateT X.
Proof. by rewrite slifting_stateT. Qed.
End slifting_flush_stateT.

Section slifting_flush_exceptT.
Variable Z : UU0.
Definition flush_exceptT (X : UU0) (t : exceptFMT Z M X) (h : Z -> exceptFMT Z M X)
    : exceptFMT Z M X :=
  let: (c, _) := t in (c, [::]).

Let flush_exceptT' (X : UU0) : (E \O exceptFMT Z M) X -> (exceptFMT Z M) X :=
  fun c => let : (x, _) := c in (x, [::]).

Lemma flush_exceptTE (X : UU0) :
  (slifting flush (exceptFMT Z) naturality_MK) X = @flush_exceptT' X.
Proof. by rewrite slifting_exceptT. Qed.
End slifting_flush_exceptT.

Section slifting_flush_envT.
Variable Z : UU0.
Definition flush_envT (X : UU0) (t : envFMT Z M X) : envFMT Z M X :=
  fun e => let: (x, _) := t e in (x, [::]).

Lemma flush_envTE (X : UU0) :
  (slifting flush (envFMT Z) naturality_MK) X = @flush_envT X.
Proof. by rewrite slifting_envT. Qed.
End slifting_flush_envT.

Section slifting_flush_outputT.
Variable Z : UU0.
Definition flush_outputT (X : UU0) (t : outputFMT R M X) (h : Z -> outputFMT R M X)
  : outputFMT R M X := let: (p, w) := t in (p, [::]).

Let flush_outputT' (X : UU0) : (E \O outputFMT R M) X -> (outputFMT R M) X :=
  fun e => let: (pw, w') := e in (pw, [::]).

Lemma flush_outputTE (X : UU0) :
  (slifting flush (outputFMT R) naturality_MK) X = @flush_outputT' X.
Proof.
rewrite slifting_outputT.
by apply fun_ext; case.
Qed.
End slifting_flush_outputT.

End slifting_flush.
