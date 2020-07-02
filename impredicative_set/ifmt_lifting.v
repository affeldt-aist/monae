From mathcomp Require Import all_ssreflect.
Require Import imonae_lib ihierarchy imonad_lib imonad_transformer.

(******************************************************************************)
(*         Formalization of Sect. 5 of modular monad transformers             *)
(*                                                                            *)
(* This file corresponds to the formalization of [Mauro Jaskelioff,           *)
(* Modular Monad Transformers, ESOP 2009] (from Sect. 5, definition 23).      *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.

Import Univ.

Definition k_type (m : UU0 -> UU0) (A : UU0) :=
  forall (B : UU0), (A -> m B) -> m B.

Section codensity.
Variable (M : monad).

Definition K_type (A : UU0) : UU0 := k_type M A.

Definition K_ret (A : UU0) (a : A) : K_type A :=
  fun (B : UU0) (k : A -> M B) => k a.

Definition K_bind (A B : UU0) (m : K_type A) f : K_type B :=
  fun (C : UU0) (k : B -> M C) => m C (fun a : A => (f a) C k).

Definition K_fmap (A B : UU0) (f : A -> B) (m : K_type A) : K_type B :=
  fun (C : UU0) (k : B -> M C) => m C (fun a : A => k (f a)).

Lemma K_fmap_id : FunctorLaws.id K_fmap.
Proof.
move=> A; rewrite /K_fmap; apply fun_ext => m /=.
apply FunctionalExtensionality.functional_extensionality_dep => B.
apply fun_ext => k.
by rewrite -FunctionalExtensionality.eta_expansion.
Qed.

Lemma K_fmap_comp : FunctorLaws.comp K_fmap.
Proof. by []. Qed.

Definition K_functor :=
  Functor.Pack (Functor.Mixin K_fmap_id K_fmap_comp).

Lemma naturality_K_ret : naturality FId K_functor K_ret.
Proof.
move=> A B h.
rewrite /K_functor /Actm /= /K_fmap /K_ret /=.
apply fun_ext => a /=.
by apply FunctionalExtensionality.functional_extensionality_dep.
Qed.

Definition K_ret_natural : FId ~> K_functor :=
  Natural.Pack (Natural.Mixin naturality_K_ret).

Program Definition eK_MonadM : monad :=
  @Monad_of_ret_bind K_functor K_ret_natural K_bind _ _ _.
Next Obligation.
move=> A B a f; rewrite /K_bind /=.
apply FunctionalExtensionality.functional_extensionality_dep => C.
by apply fun_ext.
Qed.
Next Obligation.
move=> A m.
rewrite /K_bind /K_ret.
apply FunctionalExtensionality.functional_extensionality_dep => C.
by apply fun_ext.
Qed.
Next Obligation.
move=> A B C m f g; rewrite /K_bind.
by apply FunctionalExtensionality.functional_extensionality_dep.
Qed.

Definition K_lift (A : UU0) (m : M A) : eK_MonadM A :=
  fun (B : UU0) (k : A -> M B) => @Bind M A B m k.

Program Definition K_MonadM : monadM M eK_MonadM :=
  locked (monadM.Pack (@monadM.Mixin _ _ K_lift _ _)).
Next Obligation.
move=> A; rewrite /K_lift /= /K_ret /=.
apply fun_ext => a.
apply FunctionalExtensionality.functional_extensionality_dep => B /=.
by apply fun_ext => b; rewrite bindretf.
Qed.
Next Obligation.
move=> A B m f; rewrite /K_lift.
apply FunctionalExtensionality.functional_extensionality_dep => C /=.
apply fun_ext => g.
by rewrite bindA.
Qed.

End codensity.

Definition K_MonadT : monadT :=
  MonadT.Pack (@MonadT.Mixin eK_MonadM K_MonadM).

Section kappa.
Variables (M : monad) (E : functor) (op : E.-operation M).

Definition kappa' : E ~~> K_MonadT M :=
  fun (A : UU0) (s : E A) (B : UU0) (k : A -> M B) =>
    op B ((E # k) s).

Lemma natural_kappa' : naturality _ _ kappa'.
Proof.
move=> A B h; rewrite /kappa'; apply fun_ext => ea; rewrite [in RHS]/=.
transitivity (fun B0 (k : B -> M B0) => op B0 ((E # (k \o h)) ea)) => //.
apply FunctionalExtensionality.functional_extensionality_dep => C.
by apply fun_ext => D; rewrite functor_o.
Qed.

Definition kappa := Natural.Pack (Natural.Mixin natural_kappa').

Lemma kappaE X : kappa X = (fun (s : E X) (B : UU0) (k : X -> M B) => op B ((E # k) s)).
Proof. by []. Qed.

End kappa.

Definition naturality_k_type (M : functor) (A : UU0) (m : k_type M A) :=
  naturality (exponential_F A \O M) M m.

Section from.
Variables (M : monad).

Definition from_component : K_MonadT M ~~> M :=
  fun (A : UU0) (c : K_MonadT M A) => c A Ret.

Hypothesis naturality_k_type : forall (A : UU0) (m : k_type M A),
  naturality_k_type m.

Lemma natural_from_component : naturality (K_MonadT M) M from_component.
Proof.
move=> A B h; apply fun_ext => m /=.
transitivity (m B (Ret \o h)) => //. (* by definition of from *)
rewrite -(natural RET).
transitivity ((M # h \o m A) Ret) => //. (* by definition of from *)
by rewrite naturality_k_type.
Qed.

Definition from := Natural.Pack (Natural.Mixin natural_from_component).

Lemma from_component_liftK A : (@from_component A) \o (Lift K_MonadT M A) = id.
Proof.
apply fun_ext => m /=.
rewrite /from_component /= /Lift /=.
rewrite /K_MonadM /=.
(* TODO *) unlock => /=.
rewrite /K_lift /=.
by rewrite bindmret.
Qed.

End from.

Section k_op.
Variables (E : functor) (M : monad) (op : E.-operation M).

Definition K_op : E.-aoperation (K_MonadT M) := psi (kappa op).

Lemma K_opE (A : UU0) : op A =
  (@from_component M A) \o (@K_op A) \o ((E ## (monadM_nt (Lift K_MonadT M))) A).
Proof.
apply fun_ext => m /=.
rewrite /from_component /K_op /= /psi' /kappa' /fun_app_nt /=.
rewrite /K_bind /=.
rewrite -[in RHS]compE.
rewrite -[in RHS]compE.
rewrite -compA.
rewrite -functor_o.
rewrite from_component_liftK.
rewrite functor_id.
by rewrite compfid.
Qed.

End k_op.

Section theorem27.
Variables (E : functor) (M : monad) (op : E.-operation M) (t : FMT).
Hypothesis naturality_type : forall (A : UU0) (m : k_type M A),
  naturality_k_type m.

Let op1 : t (K_MonadT M) ~> t M := Hmap t (from naturality_type).
Let op2 := alifting (K_op op) (Lift t _).
Let op3 : E \O t M ~> E \O t (K_MonadT M) :=
  E ## Hmap t (monadM_nt (Lift K_MonadT M)).

Definition hlifting : E.-operation (t M) := op1 \v op2 \v op3.

Lemma theorem27 : lifting_monadT op hlifting.
Proof.
rewrite /lifting_monadT /hlifting => X.
apply/esym.
transitivity ((op1 \v op2) X \o op3 X \o E # Lift t M X).
  by rewrite (vassoc op1).
rewrite -compA.
transitivity ((op1 \v op2) X \o
  ((E # Lift t (K_MonadT M) X) \o (E # Lift K_MonadT M X))).
  congr (_ \o _); rewrite /op3.
  by rewrite -functor_o -natural_hmap functor_o functor_app_naturalE.
transitivity (op1 X \o
  (op2 X \o E # Lift t (K_MonadT M) X) \o E # Lift K_MonadT M X).
  by rewrite vcompE -compA.
rewrite -theorem19.
transitivity (Lift t M X \o from naturality_type X \o (K_op op) X \o
  E # Lift K_MonadT M X).
  congr (_ \o _).
  by rewrite compA natural_hmap.
rewrite -2!compA.
congr (_ \o _).
by rewrite compA -K_opE.
Qed.
End theorem27.

Section proposition_28.

Variables (E : functor) (M : monad) (aop : E.-aoperation M) (t : FMT).
Hypothesis naturality_k_type : forall (A : UU0) (m : k_type M A),
  naturality_k_type m.

Lemma proposition_28 :
  hlifting aop t naturality_k_type = alifting aop (Lift t M).
Proof.
rewrite /hlifting /K_op.
rewrite {1}/alifting.
rewrite psiK.
rewrite /alifting.
apply/nattrans_ext => A.
rewrite 2!vcompE.
rewrite functor_app_naturalE.
rewrite 2!psiE.
rewrite vcompE.
transitivity (
(Hmap t (from naturality_k_type) A \o
     Join \o monadM_nt (Lift t (K_MonadT M)) (t (K_MonadT M) A)) \o (kappa aop (t (K_MonadT M) A) \o
    E # Hmap t (monadM_nt (Lift K_MonadT M)) A)
) => //.
rewrite -natural.
transitivity (
  (Hmap t (from naturality_k_type) A \o Join) \o (monadM_nt (Lift t (K_MonadT M)) (t (K_MonadT M) A) \o
    (K_MonadT M # Hmap t (monadM_nt (Lift K_MonadT M)) A) \o kappa aop (t M A))
) => //.
rewrite -natural.
rewrite kappaE vcompE phiE.
Abort.

End proposition_28.

Section example_29_stateT.
Variables (E : functor) (M : monad) (op : E.-operation M).
Hypothesis naturality_k_type : forall (A : UU0) (m : k_type M A),
  naturality_k_type m.
Variable S : UU0.

Let tau (X : UU0) s (f : S -> M (X * S)%type) := f s.

Let op' X : (E \O stateFMT S M) X -> stateFMT S M X :=
  fun t s => op (X * S)%type ((E # tau s) t).

Lemma hlifting_stateT (X : UU0) :
  (hlifting op (stateFMT S) naturality_k_type) X = @op' _.
Proof.
apply fun_ext => emx.
rewrite /op'.
apply fun_ext => s.
rewrite /hlifting.
rewrite 2!vcompE.
set h := Hmap _.
rewrite (K_opE op).
rewrite 2!functor_app_naturalE.
rewrite /=.
congr (from_component _).
apply FunctionalExtensionality.functional_extensionality_dep => A.
apply fun_ext => f.
rewrite {1}/psi' /=.
rewrite /bindS /=.
rewrite -liftSE /liftS /=.
rewrite -(compE _ _ emx) -functor_o.
rewrite -[in RHS](compE _ _ emx) -functor_o.
rewrite bindA.
set ret_id := (X in _ >>= X).
have -> : ret_id = fun (x : MS S (eK_MonadM M) X) (C : UU0) => (fun t => x s C t).
  exact: fun_ext.
rewrite {1}/Bind /= /K_bind /= {1}/Actm /=.
rewrite /Monad_of_ret_bind.Map /= /K_bind /=.
rewrite /psi' /= /K_bind /kappa' /=.
rewrite /K_ret /= /K_type /= /k_type /=.
rewrite -(compE _ _ emx).
rewrite -functor_o.
rewrite -[in RHS](compE _ _ emx).
by rewrite -functor_o.
Qed.

End example_29_stateT.

Section example_29_errorT.
Variables (E : functor) (M : monad) (op : E.-operation M).
Hypothesis naturality_k_type : forall (A : UU0) (m : k_type M A),
  naturality_k_type m.
Variable Z : UU0.

Let op' Y : (E \O errorFMT Z M) Y -> errorFMT Z M Y := @op _.

Lemma hlifting_errorT (X : UU0) :
  (hlifting op (errorFMT Z) naturality_k_type) X = @op' X.
Proof.
apply fun_ext => emx.
rewrite /op'.
rewrite (K_opE op (Z + X)%type).
rewrite /hlifting.
rewrite 2!vcompE.
set h := Hmap _.
rewrite /=.
congr (from_component (psi' _ _)).
apply FunctionalExtensionality.functional_extensionality_dep => A.
apply fun_ext => B.
apply FunctionalExtensionality.functional_extensionality_dep => C.
rewrite /=.
rewrite /psi'.
rewrite /K_ret /= /K_bind /=.
apply fun_ext => D.
rewrite /kappa'.
congr (op C _).
rewrite -(compE (E # _)).
by rewrite -functor_o.
Qed.

End example_29_errorT.

Section example_29_envT.
Variables (E : functor) (M : monad) (op : E.-operation M).
Hypothesis naturality_k_type : forall (A : UU0) (m : k_type M A),
  naturality_k_type m.
Variable Env : UU0.

Let tau (X : UU0) e (f : Env -> M X) := f e.

Let op' X : (E \O envFMT Env M) X -> envFMT Env M X :=
  fun t => fun e => op X ((E # tau e) t).

Lemma hlifting_envT (X : UU0) :
  (hlifting op (envFMT Env) naturality_k_type) X = @op' _.
Proof.
apply fun_ext => emx.
rewrite /op'.
apply fun_ext => s.
rewrite /hlifting.
rewrite 2!vcompE.
set h := Hmap _.
rewrite (K_opE op).
rewrite 2!functor_app_naturalE.
rewrite /=.
congr (from_component _).
apply FunctionalExtensionality.functional_extensionality_dep => A.
apply fun_ext => f.
rewrite {1}/psi' /=.
rewrite /bindEnv /=.
rewrite -liftEnvE /liftEnv /=.
rewrite -(compE _ _ emx) -functor_o.
rewrite -[in RHS](compE _ _ emx) -functor_o.
rewrite /Bind /Join /= /K_bind /=.
rewrite {1}/Actm /= /Monad_of_ret_bind.Map /=.
rewrite /K_bind.
rewrite /psi' /= /K_bind /= /kappa' /=.
congr (op A).
rewrite -(compE _ _ emx) -[in RHS](compE _ _ emx).
by rewrite -2!functor_o.
Qed.

End example_29_envT.

Section example_29_outputT.
Variables (E : functor) (M : monad) (op : E.-operation M).
Hypothesis naturality_k_type : forall (A : UU0) (m : k_type M A),
  naturality_k_type m.
Variable R : UU0.

Let op' X : (E \O outputFMT R M) X -> outputFMT R M X :=
  @op (X * seq R)%type.

Lemma hlifting_outputT (X : UU0) :
  (hlifting op (outputFMT R) naturality_k_type) X = @op' _.
Proof.
apply fun_ext => emx.
rewrite /op'.
rewrite /hlifting.
rewrite 2!vcompE.
set h := Hmap _.
rewrite (K_opE op).
rewrite 2!functor_app_naturalE.
rewrite /=.
congr (from_component _).
apply FunctionalExtensionality.functional_extensionality_dep => A.
apply fun_ext => f.
rewrite {1}/psi' /=.
rewrite /bindO /=.
rewrite -liftOE /liftO /=.
rewrite -(compE _ _ emx) -functor_o.
rewrite /Bind /Join /= /K_bind /=.
rewrite {1}/Actm /= /Monad_of_ret_bind.Map /=.
rewrite /K_bind.
rewrite /psi' /= /K_bind /= /kappa' /=.
congr (op A).
rewrite -(compE _ _ emx) -[in RHS](compE _ _ emx).
rewrite -2!functor_o.
congr ((E # _) _).
apply fun_ext => rmx /=.
rewrite /K_ret /= /Actm /= /Monad_of_ret_bind.Map /K_bind.
congr (Lift K_MonadT M _ _ _ _).
by apply fun_ext; case.
Qed.

End example_29_outputT.

Section example_31. (* error monad with Z = unit *)
Let E := imonad_model.ExceptOps.Handle.func unit.
Let M := imonad_model.ModelExcept.t.
Let handle : E.-operation M:= @imonad_model.ExceptOps.handle_op unit.
Hypothesis naturality_k_type : forall (A : UU0) (m : k_type M A),
  naturality_k_type m.

Section example_31_stateT.
Variable S : UU0.
Definition handle_stateT (X : UU0) (t : stateFMT S M X) (h : unit -> stateFMT S M X)
  : stateFMT S M X := fun s => match t s with
    | inl z(*unit*) => h z s
    | inr x => inr x
    end.

Let handle_stateT' (X : UU0) : (E \O stateFMT S M) X -> (stateFMT S M) X :=
  uncurry (@handle_stateT X).

Lemma handle_stateTE (X : UU0) :
  (hlifting handle (stateFMT S) naturality_k_type) X = @handle_stateT' X.
Proof.
rewrite hlifting_stateT.
apply fun_ext => -[m f].
by apply fun_ext.
Qed.
End example_31_stateT.

Section example_31_errorT.
Variable Z : UU0.
Definition handle_errorT (X : UU0) (t : errorFMT Z M X) (h : unit -> errorFMT Z M X)
  : errorFMT Z M X := match t with
    | inl z(*unit*) => h z
    | inr x => inr x
    end.

Let handle_errorT' (X : UU0) : (E \O errorFMT Z M) X -> (errorFMT Z M) X :=
  uncurry (@handle_errorT X).

Lemma handle_errorTE (X : UU0) :
  (hlifting handle (errorFMT Z) naturality_k_type) X = @handle_errorT' X.
Proof.
rewrite hlifting_errorT.
by apply fun_ext.
Qed.
End example_31_errorT.

Section example_31_envT.
Variable Z : UU0.
Definition handle_envT (X : UU0) (t : envFMT Z M X) (h : unit -> envFMT Z M X)
  : envFMT Z M X := fun e => match t e with
    | inl z(*unit*) => h z e
    | inr x => inr x
    end.

Let handle_envT' (X : UU0) : (E \O envFMT Z M) X -> (envFMT Z M) X :=
  uncurry (@handle_envT X).

Lemma handle_envTE (X : UU0) :
  (hlifting handle (envFMT Z) naturality_k_type) X = @handle_envT' X.
Proof.
rewrite hlifting_envT.
apply fun_ext => -[m f].
by apply fun_ext.
Qed.
End example_31_envT.

Section example_31_outputT.
Variable R : UU0.
Definition handle_outputT (X : UU0) (t : outputFMT R M X) (h : unit -> outputFMT R M X)
  : outputFMT R M X := match t with
    | inl z(*unit*) => h z
    | inr x => inr x
    end.

Let handle_outputT' (X : UU0) : (E \O outputFMT R M) X -> (outputFMT R M) X :=
  uncurry (@handle_outputT X).

Lemma handle_outputTE (X : UU0) :
  (hlifting handle (outputFMT R) naturality_k_type) X = @handle_outputT' X.
Proof.
rewrite hlifting_outputT.
by apply fun_ext; case.
Qed.
End example_31_outputT.

End example_31.
