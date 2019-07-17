Require Import ssreflect ssrmatching ssrfun ssrbool.
From mathcomp Require Import eqtype ssrnat seq choice fintype tuple.
From mathcomp Require Import boolp classical_sets.
From infotheo Require Import Reals_ext ssr_ext dist.
Require Import monad proba_monad model.

(*
  This file provides a model for the probability monad.
      depends on the formalization of distributions from the infotheo library
      (https://github.com/affeldt-aist/infotheo).
*)

Module MonadProbModel.
Local Obligation Tactic := idtac.

Definition _ret : forall A : Type, A -> Dist (choice_of_Type A) :=
  fun A a => Dist1.d (a : choice_of_Type A).

Definition _bind : forall A B : Type, Dist (choice_of_Type A) -> (A -> Dist (choice_of_Type B)) -> Dist (choice_of_Type B) :=
  fun A B m f => DistBind.d m f.

Program Definition monad : Monad.t :=
  @Monad_of_ret_bind _ _ret _bind _ _ _.
Next Obligation. move=> ? ? ? ?; exact: DistBind1f. Qed.
Next Obligation. move=> ? ?; exact: DistBindp1. Qed.
Next Obligation. move=> A B C m f g; exact: DistBindA. Qed.

Lemma BindE (A B : choiceType) m (f : A -> monad B) :
  (m >>= f) = DistBind.d m f.
Proof.
rewrite /Bind /Join /= /Monad_of_ret_bind.join /Fun /=.
rewrite /Monad_of_ret_bind.fmap /_bind DistBindA; congr DistBind.d.
by rewrite funeqE => a; rewrite /= DistBind1f.
Qed.

Program Definition prob_mixin : MonadProb.mixin_of monad :=
  @MonadProb.Mixin monad (fun p (A : Type) (m1 m2 : Dist (choice_of_Type A)) =>
    (@Conv2Dist.d (choice_of_Type A) m1 m2 p)) _ _ _ _ _ _.
Next Obligation. move=> ? ? ?; exact: Conv2Dist.conv0. Qed.
Next Obligation. move=> ? ? ?; exact: Conv2Dist.conv1. Qed.
Next Obligation. move=> ? ? ?; exact: Conv2Dist.convC. Qed.
Next Obligation. move=> ? ? ?; exact: Conv2Dist.convmm. Qed.
Next Obligation. move=> ? ? ? ? ? ? ? ? [? ?] /=; exact: Conv2Dist.convA. Qed.
Next Obligation.
move=> p A B m1 m2 k.
rewrite !(@BindE (choice_of_Type A) (choice_of_Type B)).
by rewrite Conv2Dist.bind_left_distr.
Qed.

Definition prob_class : MonadProb.class_of (fun A : Type => Dist (choice_of_Type A)) :=
  @MonadProb.Class _ _ prob_mixin.

Definition prob : MonadProb.t := MonadProb.Pack prob_class.

End MonadProbModel.

(*NB: from monad_model.v, which can't be loaded because of universe inconsistency *)
Lemma bigset1U A B a (f : A -> set B) : bigsetU [set a] f = f a.
Proof.
rewrite funeqE => b; rewrite propeqE; split => [[a' <-] //| ?]; by exists a.
Qed.
Lemma bigsetU1 A (s : set A) : bigsetU s (@set1 A) = s.
Proof.
rewrite funeqE => b; rewrite propeqE; split.
- by move=> -[a ?]; rewrite /set1 => ->.
- by move=> ?; rewrite /bigsetU; exists b.
Qed.
Lemma bigsetUA A B C (s : set A) (f : A -> set B) (g : B -> set C) :
  bigsetU (bigsetU s f) g = bigsetU s (fun x => bigsetU (f x) g).
Proof.
rewrite funeqE => c; rewrite propeqE.
split => [[b [a' aa' ?] ?]|[a' aa' [b ? ?]]].
by exists a' => //; exists b.
by exists b => //; exists a'.
Qed.
Section set.
Local Obligation Tactic := idtac.
Program Definition set := @Monad_of_ret_bind _ (@set1) (fun I A => @bigsetU A I) _ _ _.
Next Obligation. move=> ? ? ? ?; exact: bigset1U. Qed.
Next Obligation. move=> ? ?; exact: bigsetU1. Qed.
Next Obligation. move=> ? ? ? ? ? ?; exact: bigsetUA. Qed.
End set.

Section sketch.

Definition choice_fun {A B} (h : A -> B) : choice_of_Type A -> choice_of_Type B :=
  fun a => h a.

Let F0 : functor := MonadProbModel.monad.
Let F0E : forall (A B : Type) (h : A -> B), F0 # h = Distfmap (choice_fun h).
Proof. by []. Qed.
Let U0 : functor := FId. (* given a convex space, discards the operations,
  keeping only the carrier set *)
Let eta0 : FId ~> U0 \O F0 := fun A : Type => @Dist1.d (choice_of_Type A).
Variable eps0' : forall A : Type, Dist (choice_of_Type A) -> A.
(* eps0 is gcm.v? *)
Definition eps0 : F0 \O U0 ~> FId := fun A : Type => @eps0' A.
Lemma eta0_eps0 : adjointP eta0 eps0.
Proof.
split=> A B h.
- (* eps0 is natural *)
  rewrite FIdf.
  (* see gcm.v *)
  admit.
- (* eta0 is natural *)
  rewrite FIdf /eta0 /U0.
  transitivity (F0 # h \o Dist1.d (A := choice_of_Type A)); first by [].
  rewrite F0E funeqE => /= a /=.
  by rewrite /Distfmap DistBind1f.
Admitted.

Local Open Scope classical_set_scope.

Let F : functor := set.
Let FE : forall (A B : Type) (h : A -> B), F # h = (fun X => h @` X).
Proof.
move=> A B h.
rewrite /F /set /= funeqE => /= a.
rewrite /Monad_of_ret_bind /= /image funeqE => b /=.
rewrite propeqE; split.
- case => a' aa' /=.
  rewrite /set1 => ->{b}.
  by exists a'.
- case=> /= a' aa' <-{b} /=.
  rewrite /Fun /= /Monad_of_ret_bind.fmap.
  by exists a'.
Qed.
Let U : functor := FId. (* discarding the semilattice operation *)
Let eta : FId ~> U \O F := fun A => (fun a => [set a]).
Variable eps' : forall A : Type, set (choice_of_Type A) -> A.
  (* TODO *)
Definition eps : F \O U ~> FId := fun A : Type => @eps' A.

Lemma eta_eps : adjointP eta eps.
Proof.
split => A B h; rewrite FIdf.
- (* eps is natural *)
  admit.
- rewrite /U.
  transitivity (F # h \o eta A); first by [].
  rewrite /F /eta /= funeqE => a /=.
  rewrite /Fun /= /Monad_of_ret_bind.fmap funeqE => b /=.
  by rewrite bigset1U.
Admitted.

Let uni : @eta_type (F \O F0) (U0 \O U) := fun A => U0 # (@eta (F0 A)) \o (@eta0 A).
Let couni : @eps_type (F \O F0) (U0 \O U) := fun A => (@eps _) \o F # (@eps0 (U A)).

Lemma composite : adjointP uni couni.
Proof. exact: (composite_adjoint eta0_eps0 eta_eps). Qed.

Definition gcf : functor := monad_of_adjoint.M (F \O F0) (U0 \O U).

Goal forall A, triangular_law1 couni uni A.
Admitted.
Goal forall A, triangular_law2 couni uni A.
Admitted.

(* and then we know that gcf is actually the monad gcm by the module Module monad_of_adjoint... *)

End sketch.
