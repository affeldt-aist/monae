From mathcomp Require Import all_ssreflect.
From mathcomp Require boolp.
Require Import monae_lib monad monad_transformer.

(******************************************************************************)
(*         Formalization of Sect. 5 of modular monad transformers             *)
(*                            Work in progress!                               *)
(*                                                                            *)
(* This file corresponds to the formalization of [Mauro Jaskelioff,           *)
(* Modular Monad Transformers, ESOP 2009] (from Sect. 5, definition 23). Do   *)
(* `make sect5` to compile it, `make clean5` to clean it. Unlike the rest of  *)
(* monae, it requires some form of impredicativity. For the time being, it is *)
(* type-checked with Unset Universe Checking because monae requires monads to *)
(* be Type -> Type because of some examples using MathComp. This file can     *)
(* also be compiled with -impredicative-set provided the universes are        *)
(* lowered by one level (however, some examples using MathComp may not        *)
(* compile anymore).                                                          *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Unset Universe Checking.

Import Univ.

Definition k_type (m : UU1 -> UU1) (A : UU1) :=
  forall (B : UU1), (A -> m B) -> m B.

Section codensity.
Variable (M : monad).

Definition K_type (A : UU1) : UU1 := k_type M A.

Definition K_ret (A : UU1) (a : A) : K_type A :=
  fun (B : UU1) (k : A -> M B) => k a.

Definition K_bind (A B : UU1) (m : K_type A) f : K_type B :=
  fun (C : UU1) (k : B -> M C) => m C (fun a : A => (f a) C k).

Definition K_fmap (A B : UU1) (f : A -> B) (m : K_type A) : K_type B :=
  fun (C : UU1) (k : B -> M C) => m C (fun a : A => k (f a)).

Lemma K_fmap_id : FunctorLaws.id K_fmap.
Proof.
move=> A; rewrite /K_fmap boolp.funeqE => m /=.
apply FunctionalExtensionality.functional_extensionality_dep => B.
rewrite boolp.funeqE => k.
by rewrite -FunctionalExtensionality.eta_expansion.
Qed.

Lemma K_fmap_comp : FunctorLaws.comp K_fmap.
Proof. by []. Qed.

Definition K_functor :=
  Functor.Pack (Functor.Mixin K_fmap_id K_fmap_comp).

Lemma naturality_K_ret : naturality FId K_functor K_ret.
Proof.
move=> A B h.
rewrite /K_functor /Fun /= /K_fmap /K_ret /=.
rewrite boolp.funeqE => a /=.
by apply FunctionalExtensionality.functional_extensionality_dep.
Qed.

Definition K_ret_natural : FId ~> K_functor :=
  Natural.Pack (Natural.Mixin naturality_K_ret).

Program Definition eK_MonadM : monad :=
  @Monad_of_ret_bind K_functor K_ret_natural K_bind _ _ _.
Next Obligation.
move=> A B a f; rewrite /K_bind /=.
apply FunctionalExtensionality.functional_extensionality_dep => C.
by rewrite boolp.funeqE.
Qed.
Next Obligation.
move=> A m.
rewrite /K_bind /K_ret.
apply FunctionalExtensionality.functional_extensionality_dep => C.
by rewrite boolp.funeqE.
Qed.
Next Obligation.
move=> A B C m f g; rewrite /K_bind.
by apply FunctionalExtensionality.functional_extensionality_dep.
Qed.

Definition K_lift (A : UU1) (m : M A) : eK_MonadM A :=
  fun (B : UU1) (k : A -> M B) => @Bind M A B m k.

Program Definition K_MonadM : monadM M eK_MonadM :=
  locked (monadM.Pack (@monadM.Mixin _ _ K_lift _ _)).
Next Obligation.
move=> A; rewrite /K_lift /= /K_ret /=.
rewrite boolp.funeqE => a.
apply FunctionalExtensionality.functional_extensionality_dep => B /=.
by rewrite boolp.funeqE => b; rewrite bindretf.
Qed.
Next Obligation.
move=> A B m f; rewrite /K_lift.
apply FunctionalExtensionality.functional_extensionality_dep => C /=.
rewrite boolp.funeqE => g.
by rewrite bindA.
Qed.

End codensity.

Definition K_MonadT : monadT :=
  MonadT.Pack (@MonadT.Mixin eK_MonadM K_MonadM).

Section kappa.
Variables (M : monad) (E : functor) (op : E.-operation M).

Definition kappa' : E ~~> K_MonadT M :=
  fun (A : UU1) (s : E A) (B : UU1) (k : A -> M B) =>
    op B ((E # k) s).

Lemma natural_kappa' : naturality _ _ kappa'.
Proof.
move=> A B h; rewrite /kappa' boolp.funeqE => ea; rewrite [in RHS]/=.
transitivity (fun B0 (k : B -> M B0) => op B0 ((E # (k \o h)) ea)) => //.
apply FunctionalExtensionality.functional_extensionality_dep => C.
by rewrite boolp.funeqE => D; rewrite functor_o.
Qed.

Definition kappa := Natural.Pack (Natural.Mixin natural_kappa').

End kappa.

Definition naturality_k_type (M : functor) (A : UU1) (m : k_type M A) :=
  naturality (exponential_F A \O M) M m.

Section from.
Variables (M : monad).

Definition from' : K_MonadT M ~~> M :=
  fun (A : UU1) (c : K_MonadT M A) => c A Ret.

Hypothesis naturality_m : forall (A : UU1) (m : k_type M A),
  naturality_k_type m.

Lemma natural_from' : naturality (K_MonadT M) M from'.
Proof.
move=> A B h; rewrite boolp.funeqE => m /=.
transitivity (m B (Ret \o h)) => //. (* by definition of from *)
rewrite -(natural RET).
transitivity ((M # h \o m A) Ret) => //. (* by definition of from *)
by rewrite naturality_m.
Qed.

Definition from := Natural.Pack (Natural.Mixin natural_from').

Lemma from'_liftK A : (@from' A) \o (Lift K_MonadT M A) = id.
Proof.
rewrite boolp.funeqE => m /=.
rewrite /from' /= /Lift /=.
rewrite /K_MonadM /=.
(* TODO *) unlock => /=.
rewrite /K_lift /=.
by rewrite bindmret.
Qed.

End from.

Section k_op.
Variables (E : functor) (M : monad) (op : E.-operation M).

Definition K_op : E.-aoperation (K_MonadT M) := psi (kappa op).

Lemma K_opE (A : UU1) : op A =
  (@from' M A) \o (@K_op A) \o ((E ## (monadM_nt (Lift K_MonadT M))) A).
Proof.
rewrite boolp.funeqE => m /=.
rewrite /from' /K_op /= /psi' /kappa' /fun_app_nt /=.
rewrite /K_bind /=.
rewrite -[in RHS]compE.
rewrite -[in RHS]compE.
rewrite -compA.
rewrite -functor_o.
rewrite from'_liftK.
rewrite functor_id.
by rewrite compfid.
Qed.

End k_op.

Section theorem27.
Variables (E : functor) (M : monad) (op : E.-operation M) (t : FMT).
Hypothesis naturality_m : forall (A : UU1) (m : k_type M A),
  naturality_k_type m.

Let op1 : t (K_MonadT M) ~> t M := Hmap t (from naturality_m).
Let op2 := alifting (K_op op) (Lift t _).
Let op3 : E \O t M ~> E \O t (K_MonadT M) :=
  E ## Hmap t (monadM_nt (Lift K_MonadT M)).

Definition hlifting : E.-operation (t M) := op1 \v op2 \v op3.

Lemma theorem27 : lifting_monadT op hlifting.
Proof.
rewrite /lifting_monadT => X.
rewrite /hlifting.
apply/esym.
transitivity ((op1 \v op2) X \o op3 X \o E # Lift t M X).
  by rewrite (vassoc op1).
rewrite -compA.
transitivity ((op1 \v op2) X \o (
  (E # Lift t (K_MonadT M) X) \o (E # Lift K_MonadT M X))).
  congr (_ \o _).
  by rewrite /op3 -functor_o -natural_hmap functor_o functor_app_naturalE.
transitivity (op1 X \o
  (op2 X \o E # Lift t (K_MonadT M) X) \o E # Lift K_MonadT M X).
  by rewrite vcompE -compA.
rewrite -theorem19.
transitivity (Lift t M X \o from naturality_m X \o (K_op op) X \o
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
Hypothesis naturality_m : forall (A : UU1) (m : k_type M A),
  naturality_k_type m.

Lemma proposition_28 : hlifting aop t naturality_m = alifting aop (Lift t M).
Proof.
rewrite /hlifting /K_op.
rewrite {1}/alifting.
rewrite psiK.
rewrite /alifting.

Abort.

End proposition_28.

Section example_29_errorT.
Variables (E : functor) (M : monad) (op : E.-operation M).
Hypothesis naturality_m : forall (A : UU1) (m : k_type M A),
  naturality_k_type m.
Variable X : Type.

Let op' Y : (E \O errorFMT X M) Y -> errorFMT X M Y := fun x => @op _ x.

Lemma hlifting_errorT Y : (hlifting op (errorFMT X) naturality_m) Y = @op' Y.
Proof.
rewrite /hlifting /op'.
rewrite 2!vcompE.
set h := Hmap _.
rewrite (_ : h = hmapX X) //.
rewrite /alifting.
Abort.

End example_29_errorT.
