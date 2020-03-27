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

Definition K_ret_natural : FId ~> K_functor := Natural.Pack naturality_K_ret.

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

Section kappa_def.
Variables (M : monad) (E : functor).

Definition kappa (tau : operation E M) : E ~~> K_MonadT M :=
  fun (A : UU1) (s : E A) (B : UU1) (k : A -> M B) =>
    tau B ((E # k) s).

End kappa_def.

Section kappa_lemmas.

Variables (E : functor) (M : monad) (op : operation E M).

Lemma natural_kappa : naturality _ _ (kappa op).
Proof.
move=> A B h; rewrite /kappa boolp.funeqE => ea; rewrite [in RHS]/=.
transitivity (fun B0 (k : B -> M B0) => op B0 ((E # (k \o h)) ea)) => //.
apply FunctionalExtensionality.functional_extensionality_dep => C.
by rewrite boolp.funeqE => D; rewrite functor_o.
Qed.

End kappa_lemmas.

Section from_def.

Definition from (M : monad) : K_MonadT M ~~> M :=
  fun (A : UU1) (c : K_MonadT M A) => c A Ret.

End from_def.

Definition naturality_k_type (M : functor) (A : UU1) (m : k_type M A) :=
  naturality (exponential_F A \O M) M m.

Section from_prop.

Variable M : monad.
Hypothesis naturality_m : forall (A : UU1) (m : k_type M A),
  naturality_k_type m.

Lemma from_liftK A : (@from M A) \o (Lift K_MonadT M A) = id.
Proof.
rewrite boolp.funeqE => m /=.
rewrite /from /= /Lift /=.
rewrite /K_MonadM /=.
(* TODO *) unlock => /=.
rewrite /K_lift /=.
by rewrite bindmret.
Qed.

Lemma natural_from : naturality (K_MonadT M) M (@from M).
Proof.
move=> A B h; rewrite /from.
rewrite /K_MonadT /=.
rewrite /K_type /=.
rewrite boolp.funeqE => m.
rewrite /=.
transitivity ((K_MonadT M # h) m B Ret) => //.
rewrite [in RHS]/Fun /=.
rewrite /Monad_of_ret_bind.Map /=.
rewrite /K_bind /K_ret /=.
transitivity (m B (Ret \o h)) => //.
rewrite -(natural RET).
transitivity ((M # h \o m A) Ret) => //.
by rewrite naturality_m.
Qed.

End from_prop.

Section k_op_def.
Variables (E : functor) (M : monad) (op : (E \O M) ~> M).

Definition K_op : (E \O K_MonadT M) ~~> K_MonadT M := psi_g (kappa op).

End k_op_def.

Section k_op_prop.

Variables (M : monad) (E : functor) (op : operation E M).

Lemma natural_K_op : naturality _ _ (K_op op).
Proof.
by move=> A B h; rewrite /K_op (natural_psi (Natural.Pack (natural_kappa op))).
Qed.

Lemma K_opE (A : UU1) :
  op A = (@from M A) \o (@K_op _ _ op A) \o
    ((E ## [natural of Lift K_MonadT M]) A).
Proof.
rewrite boolp.funeqE => m /=.
rewrite /from /K_op /= /psi_g /kappa /fun_app_nt /=.
rewrite /K_bind /=.
rewrite -[in RHS]compE.
rewrite -[in RHS]compE.
rewrite -compA.
rewrite -functor_o.
rewrite from_liftK.
rewrite functor_id.
by rewrite compfid.
Qed.

Lemma algebraic_K_op : algebraicity (K_op op).
Proof.
by move=> *; rewrite /K_op (algebraic_psi (Natural.Pack (natural_kappa op))).
Qed.

End k_op_prop.

Section theorem_27.

Variables (E : functor) (M : monad) (op : operation E M) (t : FMT).
Hypothesis naturality_m : forall (A : UU1) (m : k_type M A),
  naturality_k_type m.

Let from_nt := Natural.Pack (natural_from naturality_m).
Let op1 : t (K_MonadT M) ~> t M := Hmap t from_nt.
Let op3 : E \O t M ~> E \O t (K_MonadT M) :=
  E ## Hmap t [natural of Lift K_MonadT M].
Let aop : aoperation E (K_MonadT M) :=
  @AOperation.Pack _ _ (Natural.Pack (natural_K_op op))
                       (AOperation.Mixin (algebraic_K_op op)).
Let op2 := Natural.Pack (@natural_alifting _ _ aop _ (Lift t _)).

Let op' : E \O t M ~> t M := op1 \v op2 \v op3.

Lemma thm27 : lifting_monadT op op'.
Proof.
rewrite /lifting_monadT => X.
rewrite /op'.
apply/esym.
transitivity ((op1 \v op2) X \o op3 X \o E # Lift t M X).
  by rewrite (vassoc op1).
rewrite -compA.
transitivity ((op1 \v op2) X \o (
  (E # Lift t (K_MonadT M) X) \o (E # Lift K_MonadT M X))).
  congr (_ \o _).
  rewrite /op3.
  rewrite functor_app_naturalE.
  rewrite /=.
  rewrite compidf.
  rewrite -!functor_o.
  by rewrite (natural_hmap t).
transitivity (op1 X \o
  (op2 X \o E # Lift t (K_MonadT M) X) \o E # Lift K_MonadT M X).
  by rewrite vcompE -compA.
transitivity (
  op1 X \o (Lift t (K_MonadT M) X \o (K_op op) X) \o
  E # Lift K_MonadT M X).
  by rewrite -(theorem19b aop (Lift t (K_MonadT M))).
transitivity (
  Lift t M X \o from_nt X \o (K_op op) X \o
  E # Lift K_MonadT M X).
  congr (_ \o _).
  rewrite compA.
  congr (_ \o _).
  by rewrite (natural_hmap t).
rewrite -2!compA.
congr (_ \o _).
rewrite compA.
by rewrite K_opE.
Qed.

End theorem_27.
