(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2020 monae authors, license: LGPL-2.1-or-later               *)
From mathcomp Require Import all_ssreflect.
From HB Require Import structures.
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
(* uniform_sigma_lifting == Theorem: given a functorial monad transformer t,  *)
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
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.

Definition MK (m : UU0 -> UU0) (A : UU0) := forall (B : UU0), (A -> m B) -> m B.

Section codensity.
Variable (M : monad).

Definition retK : FId ~~> MK M :=
  fun (A : UU0) (a : A) (B : UU0) (k : A -> M B) => k a.

Definition bindK (A B : UU0) (m : MK M A) f : MK M B :=
  fun (C : UU0) (k : B -> M C) => m C (fun a : A => (f a) C k).

Definition MK_map (A B : UU0) (f : A -> B) (m : MK M A) : MK M B :=
  fun (C : UU0) (k : B -> M C) => m C (fun a : A => k (f a)).

Let MK_map_i : FunctorLaws.id MK_map.
Proof.
move=> A; rewrite /MK_map; apply funext => m /=.
by apply funext_dep => B; exact: funext.
Qed.

Let MK_map_o : FunctorLaws.comp MK_map. Proof. by []. Qed.

HB.instance Definition _ := isFunctor.Build (MK M) MK_map_i MK_map_o.

Let naturality_retK : naturality FId [the functor of MK M] retK.
Proof.
move=> A B h; rewrite /actm /= /MK_map /retK /=.
by apply funext => a /=; exact: funext_dep.
Qed.

HB.instance Definition _ := isNatural.Build
  _ [the functor of MK M] retK naturality_retK.

Let left_neutral : BindLaws.left_neutral bindK retK.
Proof.
by move=> A B a f; rewrite /bindK /=; apply funext_dep => C; exact: funext.
Qed.

Let right_neutral : BindLaws.right_neutral bindK retK.
Proof.
by move=> A m; rewrite /bindK /retK; apply funext_dep => C; exact: funext.
Qed.

Lemma associative : BindLaws.associative bindK.
Proof. by move=> A B C m f g; rewrite /bindK; exact: funext_dep. Qed.

Lemma fmapE (A B : UU0) (f : A -> B) (m : MK M A) :
  ([the functor of MK M] # f) m = bindK m (@retK _ \o f).
Proof. by []. Qed.

HB.instance Definition _ := @Monad_of_ret_bind.Build
  (MK M) [the _ ~> _ of retK] bindK fmapE left_neutral right_neutral associative.

Definition liftK : M ~~> MK M :=
  fun (A : UU0) (m : M A) (B : UU0) (k : A -> M B) => m >>= k.

Let retliftK : MonadMLaws.ret liftK.
Proof.
move=> A; rewrite /liftK/= /retK/=; apply funext => a.
by apply funext_dep => B /=; apply: funext => b; rewrite bindretf.
Qed.

Let bindliftK : MonadMLaws.bind liftK.
Proof.
move=> A B m f; rewrite /liftK; apply funext_dep => C /=.
by apply funext => g; rewrite bindA.
Qed.

HB.instance Definition _ := isMonadM_of_ret_bind.Build
  M [the monad of MK M] liftK retliftK bindliftK.

End codensity.

Definition codensityT := fun M : monad => [the monad of MK M].

HB.instance Definition _ :=
  isMonadT.Build codensityT (fun M => [the monadM _ _ of @liftK M]).

Section kappa.
Variables (M : monad) (E : functor) (op : E.-operation M).

Definition kappa' : E ~~> codensityT M :=
  fun (A : UU0) (s : E A) (B : UU0) (k : A -> M B) =>
    op B ((E # k) s).

Lemma naturality_kappa' : naturality _ _ kappa'.
Proof.
move=> A B h; rewrite /kappa'; apply funext => ea; rewrite [in RHS]/=.
transitivity (fun B0 (k : B -> M B0) => op B0 ((E # (k \o h)) ea)) => //.
by apply funext_dep => C; apply funext => D; rewrite functor_o.
Qed.

HB.instance Definition _ := isNatural.Build
  _ (codensityT M) kappa' naturality_kappa'.

Definition kappa := [the _ ~> _ of kappa'].

Lemma kappaE X : kappa X =
  fun (s : E X) (B : UU0) (k : X -> M B) => op B ((E # k) s).
Proof. by []. Qed.

End kappa.

Definition naturality_MK (M : functor) (A : UU0) (m : MK M A) :=
  naturality [the functor of exponential_F A \o M] M m.

Section from.
Variables (M : monad).

Definition from_component : codensityT M ~~> M :=
  fun (A : UU0) (c : codensityT M A) => c A Ret.

Hypothesis naturality_MK : forall (A : UU0) (m : MK M A),
  naturality_MK m.

Lemma natural_from_component : naturality (codensityT M) M from_component.
Proof.
move=> A B h; apply funext => m /=.
rewrite [RHS](_ : _ = m B (Ret \o h)) //. (* by definition of from *)
rewrite -natural.
rewrite [LHS](_ : _ = (M # h \o m A) Ret) //. (* by definition of from *)
by rewrite naturality_MK.
Qed.

HB.instance Definition _ :=
  isNatural.Build _ M from_component natural_from_component.

Definition from := [the _ ~> _ of from_component].

Lemma from_component_liftK A :
  @from_component A \o Lift [the monadT of codensityT] M A = id.
Proof.
by apply funext => m /=; rewrite /from_component/= /liftK /= bindmret.
Qed.

End from.

Section psi_kappa.
Variables (E : functor) (M : monad) (op : E.-operation M).

Definition psik : E.-aoperation (codensityT M) := psi (kappa op).

Lemma psikE (A : UU0) : op A = (@from_component M A) \o (@psik A) \o
  ((E ## Lift [the monadT of codensityT] M) A).
Proof.
apply funext => m /=.
rewrite /from_component /psik /= /psi' /kappa' /fun_app_nt /=.
rewrite /bindK /=.
rewrite /join_of_bind.
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
Variables (E : functor) (M : monad) (op : E.-operation M) (t : fmt).
Hypothesis naturality_MK : forall (A : UU0) (m : MK M A), naturality_MK m.

Let op1 : t (codensityT M) ~> t M := hmap t (from naturality_MK).
Let op2 := alifting (psik op) (Lift t _).
Let op3 : [the functor of E \o t M] ~> [the functor of E \o t (codensityT M)] :=
  E ## hmap t (Lift [the monadT of codensityT] M).

Definition slifting : E.-operation (t M) := op1 \v op2 \v op3.

Theorem uniform_sigma_lifting : lifting_monadT op slifting.
Proof.
rewrite /lifting_monadT /slifting => X.
apply/esym.
transitivity ((op1 \v op2) X \o op3 X \o E # Lift t M X).
  by rewrite (vassoc op1) vcompE/= !vcompE.
rewrite -compA.
transitivity ((op1 \v op2) X \o
    ((E # Lift t (codensityT M) X) \o
    (E # Lift [the monadT of codensityT] M X))).
  congr (_ \o _); rewrite /op3.
  by rewrite -functor_o -natural_hmapE functor_app_naturalE -(@functor_o E).
transitivity (op1 X \o
  (op2 X \o E # Lift t (codensityT M) X) \o E # Lift [the monadT of codensityT] M X).
  by rewrite vcompE -compA.
rewrite -uniform_algebraic_lifting.
transitivity (Lift t M X \o from naturality_MK X \o (psik op) X \o
  E # Lift [the monadT of codensityT] M X).
  congr (_ \o _).
  by rewrite compA natural_hmapE.
rewrite -2!compA.
congr (_ \o _).
by rewrite compA -psikE.
Qed.
End uniform_sigma_lifting.

(* example 29 *)
Section slifting_instances.

Variables (E : functor) (M : monad) (op : E.-operation M).
Hypothesis naturality_MK : forall (A : UU0) (m : MK M A), naturality_MK m.

Section slifting_stateT.
Variable S : UU0.

Let tau (X : UU0) s (f : S -> M (X * S)%type) := f s.

Let op' : E \o stateT S M ~~> stateT S M :=
  fun (X : UU0) t s => op (X * S)%type ((E # tau s) t).

Lemma slifting_stateT (X : UU0) :
  (slifting op [the fmt of stateT S] naturality_MK) X = @op' _.
Proof.
apply funext => emx.
rewrite /op'.
apply funext => s.
rewrite /slifting.
rewrite 2!vcompE.
set h := hmap _.
rewrite [in RHS](psikE op).
rewrite 2!functor_app_naturalE.
rewrite /=.
congr (from_component _).
apply funext_dep => A; apply funext => f.
rewrite {1}/psi' /=.
rewrite /bindS /=.
rewrite /join_of_bind.
rewrite vcompE/=.
rewrite /liftS /=.
rewrite -(compE _ _ emx) -functor_o.
rewrite -[in RHS](compE _ _ emx) -functor_o.
rewrite bindA.
set ret_id := (X in _ >>= X).
have -> : ret_id = fun (x : MS S (codensityT M) X) (C : UU0) => (fun t => x s C t).
  by apply funext.
rewrite {1}bindE /= /join_of_bind /=.
rewrite fmapE.
rewrite /bindK /=.
rewrite /psi' /= /bindK /kappa' /=.
rewrite /join_of_bind /=.
rewrite /retK /= /MK /=.
rewrite -(compE _ _ emx).
rewrite -functor_o.
rewrite -[in RHS](compE _ _ emx).
by rewrite -functor_o.
Qed.

End slifting_stateT.

Section slifting_exceptT.
Variable Z : UU0.

Let op' : E \o exceptT Z M ~~> exceptT Z M := fun (Y : UU0) => @op _.

Lemma slifting_exceptT (X : UU0) :
  (slifting op [the fmt of exceptT Z] naturality_MK) X = @op' X.
Proof.
apply funext => emx.
rewrite /op'.
rewrite (psikE op (Z + X)%type).
rewrite /slifting.
rewrite 2!vcompE.
set h := hmap _.
rewrite /=.
f_equal.
rewrite /psi' /= /join_of_bind.
rewrite /bindX /= bindE /= {1}/join_of_bind /=.
rewrite fmapE.
rewrite /bindK /=.
apply funext_dep => A; apply funext => k.
rewrite vcompE/=.
rewrite /liftX /= bindE /= /join_of_bind /= /bindK /= fmapE /= /bindK /=.
rewrite /psi' /= /join_of_bind /= /bindK /= /kappa'.
congr (op _ _).
rewrite -(compE (E # _)).
by rewrite -functor_o.
Qed.

End slifting_exceptT.

Section slifting_envT.
Variable Env : UU0.

Let tau (X : UU0) e (f : Env -> M X) := f e.

Let op' : E \o envT Env M ~~> envT Env M :=
  fun (X : UU0) t => fun e => op X ((E # tau e) t).

Lemma slifting_envT (X : UU0) :
  (slifting op [the fmt of envT Env] naturality_MK) X = @op' _.
Proof.
apply funext => emx.
rewrite /op'.
apply funext => s.
rewrite /slifting.
rewrite 2!vcompE.
set h := hmap _.
rewrite (psikE op).
rewrite 2!functor_app_naturalE.
rewrite /=.
congr (from_component _).
apply funext_dep => A; apply funext => f.
rewrite {1}/psi' /= /join_of_bind /=.
rewrite /bindEnv /=.
rewrite vcompE/=.
rewrite bindE /= /join_of_bind /= /bindK.
rewrite fmapE /bindK.
rewrite /liftEnv /=.
rewrite -(compE _ _ emx) -functor_o.
rewrite -[in RHS](compE _ _ emx) -functor_o.
rewrite /psi' /= /bindK /= /kappa' /=.
congr (op A).
rewrite -(compE _ _ emx) -[in RHS](compE _ _ emx).
by rewrite -2!functor_o.
Qed.

End slifting_envT.

Section slifting_outputT.
Variable R : UU0.

Let op' : E \o outputT R M ~~> outputT R M :=
  fun (X : UU0) => @op (X * seq R)%type.

Lemma slifting_outputT (X : UU0) :
  (slifting op [the fmt of outputT R] naturality_MK) X = @op' _.
Proof.
apply funext => emx.
rewrite /op'.
rewrite /slifting.
rewrite 2!vcompE.
set h := hmap _.
rewrite (psikE op).
rewrite 2!functor_app_naturalE.
rewrite /=.
f_equal.
rewrite /psi' /= /join_of_bind /= /bindK /bindO /= bindE /= /join_of_bind /bindK /=.
apply funext_dep => A; apply funext => f.
rewrite fmapE /bindK.
rewrite vcompE/=.
rewrite /liftO /=.
rewrite -(compE _ _ emx) -functor_o.
rewrite bindE /= /join_of_bind /= /bindK /=.
rewrite fmapE.
rewrite /bindK.
rewrite /psi' /= /bindK /= /kappa' /=.
congr (op A).
rewrite -(compE _ _ emx) -[in RHS](compE _ _ emx).
rewrite -2!functor_o.
congr ((E # _) _).
apply funext => rmx /=.
rewrite /retK /= bindE fmapE /= /join_of_bind /= /bindK.
congr (Lift [the monadT of codensityT] M _ _ _ _).
by apply funext => -[].
Qed.

End slifting_outputT.

End slifting_instances.

(* proposition 28 *)
Section slifting_alifting_coincide.

Variables (E : functor) (M : monad) (aop : E.-aoperation M).
Hypothesis naturality_MK : forall (A : UU0) (m : MK M A),
  naturality_MK m.

Lemma slifting_alifting_stateFMT (S : UU0) (t := [the fmt of stateT S]) :
  slifting aop t naturality_MK = alifting aop (Lift t M).
Proof.
apply nattrans_ext => X.
rewrite (slifting_stateT aop naturality_MK S).
apply funext => m; apply funext => s.
rewrite /alifting.
rewrite /=.
rewrite psiE /=.
rewrite /join_of_bind /= /bindS.
rewrite vcompE/=.
rewrite /liftS/=.
rewrite 2!algebraic.
congr (aop _ _).
rewrite -[RHS](compE _ (E # _)).
rewrite -functor_o.
rewrite -[RHS](compE _ (E # _)).
rewrite -functor_o.
congr ((E # _) m).
apply funext => x /=.
by rewrite 2!bindretf.
Qed.

Lemma slifting_alifting_exceptFMT (Z : UU0) (t := [the fmt of exceptT Z]) :
  slifting aop t naturality_MK = alifting aop (Lift t M).
Proof.
apply nattrans_ext => X.
rewrite (slifting_exceptT aop naturality_MK Z).
apply funext => m.
rewrite /alifting.
rewrite /=.
rewrite psiE /= /join_of_bind /bindX.
rewrite vcompE/=.
rewrite /liftX.
rewrite 2!algebraic.
congr (aop _ _).
rewrite -[RHS](compE _ (E # _)).
rewrite -functor_o.
rewrite -[RHS](compE _ (E # _)).
rewrite -functor_o.
rewrite (_ : _ \o Ret = id) ?functor_id //.
apply funext => n /=.
by rewrite 2!bindretf.
Qed.

Lemma slifting_alifting_envFMT (Env : UU0) (t := [the fmt of envT Env]) :
  slifting aop t naturality_MK = alifting aop (Lift t M).
Proof.
apply nattrans_ext => X.
rewrite (slifting_envT aop naturality_MK Env).
apply funext => m; apply funext => e.
rewrite /alifting.
rewrite /=.
rewrite psiE /= /join_of_bind /= /bindEnv.
rewrite vcompE/=.
rewrite /liftEnv.
rewrite algebraic.
congr (aop _ _).
rewrite -[RHS](compE _ (E # _)).
rewrite -functor_o.
congr ((E # _) m).
apply funext => x /=.
by rewrite bindretf.
Qed.

Lemma slifting_alifting_outputFMT (R : UU0) (t := [the fmt of outputT R]) :
  slifting aop t naturality_MK = alifting aop (Lift t M).
Proof.
apply nattrans_ext => X.
rewrite (slifting_outputT aop naturality_MK R).
apply funext => m.
rewrite /alifting.
rewrite /=.
rewrite psiE /= /join_of_bind /= /bindO.
rewrite vcompE/=.
rewrite /liftO.
rewrite 2!algebraic.
congr (aop _ _).
rewrite -[RHS](compE _ (E # _)).
rewrite -functor_o.
rewrite -[RHS](compE _ (E # _)).
rewrite -functor_o.
rewrite (_ : _ \o Ret = id) ?functor_id //.
apply funext => n /=.
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
Let E := [the functor of Local.acto Env].
Let M := [the monad of EnvironmentMonad.acto Env].
Let local : E.-operation M := local_op Env.
Hypothesis naturality_MK : forall (A : UU0) (m : MK M A), naturality_MK m.

Section slifting_local_FMT.
Variable T : fmt.

Definition localKT (f : Env -> Env) : T (codensityT M) ~~> T (codensityT M) :=
  fun (X : UU0) t => Join
    (Lift T (codensityT M) (T (codensityT M) X) (fun Y k => local Y (f, k t))).

Definition localT (f : Env -> Env) : T M ~~> T M :=
  fun X t => let t' := hmap T (Lift [the monadT of codensityT] M) X t in
  hmap T (from naturality_MK) X (localKT f t').

End slifting_local_FMT.

Section slifting_local_stateT.
Variable S : UU0.

Definition local_stateT (f : Env -> Env) : stateT S M ~~> stateT S M :=
  fun X t s e => t s (f e).

Let local_stateT' : (E \o stateT S M) ~~> (stateT S M) :=
  fun X => uncurry (@local_stateT ^~ X).

Lemma local_stateTE (X : UU0) :
  (slifting local [the fmt of stateT S] naturality_MK) X = @local_stateT' X.
Proof. by rewrite slifting_stateT; apply funext => -[]. Qed.
End slifting_local_stateT.

Section slifting_local_exceptT.
Variable Z : UU0.
Definition local_exceptT (f : Env -> Env) : exceptT Z M ~~> exceptT Z M :=
  fun X t e => t (f e).

Let local_exceptT' : (E \o exceptT Z M) ~~> (exceptT Z M) :=
  fun X => uncurry (@local_exceptT ^~ X).

Lemma local_exceptTE (X : UU0) :
  (slifting local [the fmt of exceptT Z] naturality_MK) X = @local_exceptT' X.
Proof. by rewrite slifting_exceptT; apply funext => -[]. Qed.

End slifting_local_exceptT.

Section slifting_local_envT.
Variable Z : UU0.
Definition local_envT (f : Env -> Env) : envT Z M ~~> envT Z M :=
  fun X t e e' => t e (f e').

Let local_envT' : E \o envT Z M ~~> envT Z M :=
  fun X => uncurry (@local_envT ^~ X).

Lemma local_envTE (X : UU0) :
  (slifting local [the fmt of envT Z] naturality_MK) X = @local_envT' X.
Proof.
rewrite slifting_envT.
by apply funext => -[].
Qed.
End slifting_local_envT.

Section slifting_local_outputT.
Variable R : UU0.
Definition local_outputT (f : Env -> Env) : outputT R M ~~> outputT R M :=
  fun (X : UU0) t e => t (f e).

Let local_outputT' : E \o outputT R M ~~> outputT R M :=
  fun (X : UU0) => uncurry (@local_outputT ^~ X).

Lemma local_outputTE (X : UU0) :
  (slifting local [the fmt of outputT R] naturality_MK) X = @local_outputT' X.
Proof. by rewrite slifting_outputT; apply funext => -[]. Qed.
End slifting_local_outputT.

End slifting_local.

(* example 31 *)
Section slifting_handle. (* except monad with Z = unit *)
Let E := [the functor of Handle.acto unit].
Let M := [the monad of ExceptMonad.acto unit].
Let handle : E.-operation M := @handle_op unit.
Hypothesis naturality_MK : forall (A : UU0) (m : MK M A),
  naturality_MK m.

Section slifting_handle_stateT.
Variable S : UU0.
Definition handle_stateT (X : UU0) (t : stateT S M X) (h : unit -> stateT S M X)
  : stateT S M X := fun s => match t s with
    | inl z(*unit*) => h z s
    | inr x => inr x
    end.

Let handle_stateT' : (E \o stateT S M) ~~> (stateT S M) :=
  fun (X : UU0) => uncurry (@handle_stateT X).

Lemma handle_stateTE (X : UU0) :
  (slifting handle [the fmt of stateT S] naturality_MK) X = @handle_stateT' X.
Proof. by rewrite slifting_stateT; apply funext => -[m f]. Qed.
End slifting_handle_stateT.

Section slifting_handle_exceptT.
Variable Z : UU0.
Definition handle_exceptT (X : UU0) (t : exceptT Z M X)
  (h : unit -> exceptT Z M X) : exceptT Z M X := match t with
    | inl z(*unit*) => h z
    | inr x => inr x
    end.

Let handle_exceptT' : E \o exceptT Z M ~~> exceptT Z M :=
  fun (X : UU0) => uncurry (@handle_exceptT X).

Lemma handle_exceptTE (X : UU0) :
  (slifting handle [the fmt of exceptT Z] naturality_MK) X = @handle_exceptT' X.
Proof. by rewrite slifting_exceptT; exact: funext. Qed.
End slifting_handle_exceptT.

Section slifting_handle_envT.
Variable Z : UU0.
Definition handle_envT (X : UU0) (t : envT Z M X) (h : unit -> envT Z M X)
  : envT Z M X := fun e => match t e with
    | inl z(*unit*) => h z e
    | inr x => inr x
    end.

Let handle_envT' : E \o envT Z M ~~> envT Z M :=
  fun (X : UU0) => uncurry (@handle_envT X).

Lemma handle_envTE (X : UU0) :
  (slifting handle [the fmt of envT Z] naturality_MK) X = @handle_envT' X.
Proof.
by rewrite slifting_envT; apply funext => -[m f]; exact: funext.
Qed.
End slifting_handle_envT.

Section slifting_handle_outputT.
Variable R : UU0.
Definition handle_outputT (X : UU0) (t : outputT R M X)
  (h : unit -> outputT R M X) : outputT R M X := match t with
    | inl z(*unit*) => h z
    | inr x => inr x
    end.

Let handle_outputT' : E \o outputT R M ~~> outputT R M :=
  fun (X : UU0) => uncurry (@handle_outputT X).

Lemma handle_outputTE (X : UU0) :
  (slifting handle [the fmt of outputT R] naturality_MK) X = @handle_outputT' X.
Proof. by rewrite slifting_outputT; apply funext => -[]. Qed.
End slifting_handle_outputT.

End slifting_handle.

(* example 32 *)
Section slifting_flush.
Variable R : UU0.
Let E := [the functor of Flush.acto].
Let M := [the monad of OutputMonad.acto R].
Let flush : E.-operation M := flush_op R.
Hypothesis naturality_MK : forall (A : UU0) (m : MK M A),
  naturality_MK m.

Section slifting_flush_stateT.
Variable S : UU0.
Definition flush_stateT : stateT S M ~~> stateT S M :=
  fun (X : UU0) t s => let: (x, _) := t s in (x, [::]).

Lemma flush_stateTE (X : UU0) :
  (slifting flush [the fmt of stateT S] naturality_MK) X = @flush_stateT X.
Proof. by rewrite slifting_stateT. Qed.
End slifting_flush_stateT.

Section slifting_flush_exceptT.
Variable Z : UU0.
Definition flush_exceptT (X : UU0) (t : exceptT Z M X) (h : Z -> exceptT Z M X)
    : exceptT Z M X :=
  let: (c, _) := t in (c, [::]).

Let flush_exceptT' : E \o exceptT Z M ~~> exceptT Z M :=
  fun (X : UU0) c => let : (x, _) := c in (x, [::]).

Lemma flush_exceptTE (X : UU0) :
  (slifting flush [the fmt of exceptT Z] naturality_MK) X = @flush_exceptT' X.
Proof. by rewrite slifting_exceptT. Qed.
End slifting_flush_exceptT.

Section slifting_flush_envT.
Variable Z : UU0.
Definition flush_envT : envT Z M ~~>  envT Z M :=
  fun (X : UU0) t e => let: (x, _) := t e in (x, [::]).

Lemma flush_envTE (X : UU0) :
  (slifting flush [the fmt of envT Z] naturality_MK) X = @flush_envT X.
Proof. by rewrite slifting_envT. Qed.
End slifting_flush_envT.

Section slifting_flush_outputT.
Variable Z : UU0.
Definition flush_outputT (X : UU0) (t : outputT R M X) (h : Z -> outputT R M X)
  : outputT R M X := let: (p, w) := t in (p, [::]).

Let flush_outputT' : E \o outputT R M ~~> outputT R M :=
  fun (X : UU0) e => let: (pw, w') := e in (pw, [::]).

Lemma flush_outputTE (X : UU0) :
  (slifting flush [the fmt of outputT R] naturality_MK) X = @flush_outputT' X.
Proof. by rewrite slifting_outputT; exact: funext. Qed.
End slifting_flush_outputT.

End slifting_flush.
