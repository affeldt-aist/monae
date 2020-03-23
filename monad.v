Ltac typeof X := type of X.

Require Import ssrmatching.
Require FunctionalExtensionality.
From mathcomp Require Import all_ssreflect.
From mathcomp Require boolp.
Require Import monae_lib.

(*Set Polymorphic Inductive Cumulativity.
Unset Universe Minimization ToSet.*)

(******************************************************************************)
(*               A formalization of monads over the category Set              *)
(*                                                                            *)
(* We consider the type Type of Coq as the category Set and define functors   *)
(* and monads on top of it. These monads are used to develop the basics of    *)
(* monadic equational reasoning. The file category.v provides a more generic  *)
(* definition of monads as well as a bridge to this file.                     *)
(*                                                                            *)
(* Module FunctorLaws == map laws of a functor                                *)
(*            functor == type of functors                                     *)
(*              F # g == application of functor F to the morphism g           *)
(*             F ~> G == natural transformation from functor F to functor G   *)
(*             F -| G == adjoint functors                                     *)
(*              monad == type of monads                                       *)
(*      operation E M == sigma operation                                      *)
(******************************************************************************)

(* Contents:
- Module FunctorLaws/Module Functor
- various sections about functors
- Section fcomp
- Module natural
    natural transformations
- Module AdjointFunctor
- Module BindLaws.
    definition of algebraic laws to be used with monads
- Section monad_of_adjoint.
- Section composite_adjoint.
- Module JoinLaws.
- Module Monad.
    with ret and join
- Module Monad_of_ret_bind.
    with bind and ret
- Section kleisli
- Section fmap_and_join
- Section rep.
    simple effect of counting
- Section MonadCount.
*)

Reserved Notation "A `2" (format "A `2", at level 3).
Reserved Notation "f ^`2" (format "f ^`2", at level 3).
Reserved Notation "m >> f" (at level 49).
Reserved Notation "f (o) g" (at level 11).
Reserved Notation "'fmap' f" (at level 4).

Declare Scope mprog.
Declare Scope do_notation.
Declare Scope monae_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation "f ~~> g" := (forall A, f A -> g A) (at level 51, only parsing).
Module Univ.
Definition UU2 : Type := Type.
Definition UU1 : UU2 := Type.
Definition UU0 : UU1 := Set.
End Univ.
Import Univ.

(* NB: not putting M in UU0 -> UU0 because of expressions like:
  M (A * (size s).-1.-tuple A)%type *)
Module FunctorLaws.
Section def.
Variable (M : UU1 -> UU1) (f : forall A B : UU1, (A -> B) -> M A -> M B).
Definition id := forall A, f id = id :> (M A -> M A).
Definition comp := forall (A B C : UU1) (g : B -> C) (h : A -> B),
  f (g \o h) = f g \o f h :> (M A -> M C).
End def.
End FunctorLaws.

Module Functor.
Record mixin_of (m : UU1 -> UU1) : UU2 := Mixin {
  f : forall (A B : UU1), (A -> B) -> m A -> m B ;
  _ : FunctorLaws.id f ;
  _ : FunctorLaws.comp f }.
Structure t : UU2 := Pack { m : UU1 -> UU1 ; class : mixin_of m }.
Module Exports.
Definition Fun (F : t) : forall (A B : UU1), (A -> B) -> m F A -> m F B :=
  let: Pack _ (Mixin f _ _) := F return forall (A B : UU1), (A -> B) -> m F A -> m F B in f.
Arguments Fun _ [A] [B] : simpl never.
Notation functor := t.
Coercion m : functor >-> Funclass.
End Exports.
End Functor.
Export Functor.Exports.
Notation "F # g" := (Fun F g).
Notation "'fmap' f" := (_ # f) : mprog.

Section functor_lemmas.
Variable F : functor.
Lemma functor_id : FunctorLaws.id (Fun F). Proof. by case: F => [? []]. Qed.
Lemma functor_o : FunctorLaws.comp (Fun F). Proof. by case: F => [? []]. Qed.
End functor_lemmas.

Definition Squaring (A : UU1) := (A * A)%type.
Notation "A `2" := (Squaring A).
Definition squaring_f (A B : UU1) (f : A -> B) : A`2 -> B`2 := fun x => (f x.1, f x.2).
Lemma squaring_f_id : FunctorLaws.id squaring_f.
Proof. by move=> A /=; rewrite boolp.funeqE => -[x1 x2]. Qed.
Lemma squaring_f_comp : FunctorLaws.comp squaring_f.
Proof. by move=> A B C g h /=; rewrite boolp.funeqE => -[x1 x2]. Qed.
Definition squaring : functor :=
  Functor.Pack (Functor.Mixin squaring_f_id squaring_f_comp).
Notation "f ^`2" := (squaring # f).
Lemma squaringE (A B : UU1) (f : A -> B) x : (f ^`2) x = (f x.1, f x.2).
Proof. by []. Qed.

Section functorid.
Definition id_f (A B : UU1) (f : A -> B) := f.
Lemma id_id : FunctorLaws.id id_f. Proof. by []. Qed.
Lemma id_comp : FunctorLaws.comp id_f. Proof. by []. Qed.
Definition FId : functor := Functor.Pack (Functor.Mixin id_id id_comp).
End functorid.

Section functorcomposition.
Variables f g : functor.
Definition functorcomposition (A B : UU1) := fun h : A -> B => f # (g # h).
Lemma functorcomposition_id : FunctorLaws.id functorcomposition.
Proof.
by rewrite /FunctorLaws.id => A; rewrite /functorcomposition 2!functor_id.
Qed.
Lemma functorcomposition_comp : FunctorLaws.comp functorcomposition.
Proof.
rewrite /FunctorLaws.comp => A B C g' h; rewrite /functorcomposition.
rewrite boolp.funeqE => m; by rewrite [in RHS]compE 2!functor_o.
Qed.
Definition FComp : functor :=
  Functor.Pack (Functor.Mixin functorcomposition_id functorcomposition_comp).
End functorcomposition.

Notation "f \O g" := (FComp f g).

Section functorcomposition_lemmas.
Lemma FCompId f : f \O FId = f.
Proof.
case: f => [? [???]]; congr (Functor.Pack (Functor.Mixin _ _));
  exact/boolp.Prop_irrelevance.
Qed.
Lemma FIdComp f : FId \O f = f.
Proof.
case: f => [? [???]]; congr (Functor.Pack (Functor.Mixin _ _));
  exact/boolp.Prop_irrelevance.
Qed.
Lemma FIdf (A B : UU1) (f : A -> B) : FId # f = f. Proof. by []. Qed.
Lemma FCompA (f g h : functor) : (f \O g) \O h = f \O (g \O h).
Proof.
move: f g h => [f [???]] [g [???]] [h [???]].
congr (Functor.Pack (Functor.Mixin  _ _)); exact/boolp.Prop_irrelevance.
Qed.
Lemma FCompE (f g : functor) (A B : UU1) (k : A -> B) : (f \O g) # k = f # (g # k).
Proof. by []. Qed.
End functorcomposition_lemmas.

Section curry_functor.
Definition curry_M (X : UU1) : UU1 -> UU1 := fun B => (X * B)%type.
Definition curry_f (X A B : UU1) (f : A -> B) : curry_M X A -> curry_M X B :=
  fun x : X * A => (x.1, f x.2).
Lemma curry_f_id X : FunctorLaws.id (@curry_f X).
Proof.
by rewrite /FunctorLaws.id => A; rewrite /curry_f boolp.funeqE; case.
Qed.
Lemma curry_f_comp X : FunctorLaws.comp (@curry_f X).
Proof.
by rewrite /FunctorLaws.comp => A B C g h; rewrite /curry_f boolp.funeqE; case.
Qed.
Definition curry_F X : functor :=
  Functor.Pack (Functor.Mixin (curry_f_id X) (curry_f_comp X)).
End curry_functor.

Section uncurry_functor.
Definition uncurry_M (X : UU1) : UU1 -> UU1 := fun B => X -> B.
Definition uncurry_f (X A B : UU1) (f : A -> B) : uncurry_M X A -> uncurry_M X B :=
  fun g : X -> A => f \o g.
Lemma uncurry_f_id X : FunctorLaws.id (@uncurry_f X).
Proof.
rewrite /FunctorLaws.id => A; rewrite /uncurry_f boolp.funeqE => ?.
by rewrite compidf.
Qed.
Lemma uncurry_f_comp X : FunctorLaws.comp (@uncurry_f X).
Proof.
rewrite /FunctorLaws.comp => A B C g h; rewrite /uncurry_f boolp.funeqE => ?.
by rewrite compE compA.
Qed.
Definition uncurry_F X : functor :=
  Functor.Pack (Functor.Mixin (uncurry_f_id X) (uncurry_f_comp X)).
End uncurry_functor.

Section exponential_functor.
Variable A : UU1.
Definition exponential_M (X : UU1) := A -> X.
Definition exponential_f (X Y : UU1) (f : X -> Y) :
  exponential_M X -> exponential_M Y := fun e => f \o e.
Lemma exponential_f_id : FunctorLaws.id exponential_f. Proof. by []. Qed.
Lemma exponential_f_comp : FunctorLaws.comp exponential_f.
Proof. by []. Qed.
Definition exponential_F : functor :=
  Functor.Pack (Functor.Mixin exponential_f_id exponential_f_comp).
End exponential_functor.

Lemma fmap_oE (M : functor) (A B C : UU1) (f : A -> B) (g : C -> A) (m : M C) :
  (M # (f \o g)) m = (M # f) ((M # g) m).
Proof. by rewrite functor_o. Qed.

(* monadic counterpart of function composition:
   composes a pure function after a monadic function *)
Section fcomp.
Variable M : functor.

Definition fcomp (A B C : UU1) (f : A -> B) (g : C -> M A) := locked ((M # f) \o g).
Arguments fcomp : simpl never.
Local Notation "f (o) g" := (fcomp f g).

Lemma fcomp_def (A B C : UU1) (f : A -> B) (g : C -> M A) : f (o) g = ((M # f)) \o g.
Proof. by rewrite /fcomp; unlock. Qed.

Lemma fcompE (A B C : UU1) (f : A -> B) (g : C -> M A) c : (f (o) g) c = (M # f) (g c).
Proof. by rewrite fcomp_def. Qed.

Lemma fcomp_comp (A B C D : UU1) (f : A -> B) (g : C -> A) (m : D -> M C) :
  (f \o g) (o) m = f (o) (g (o) m).
Proof. by rewrite 3!fcomp_def functor_o compA. Qed.

End fcomp.
Notation "f (o) g" := (fcomp f g) : mprog.
Arguments fcomp : simpl never.

Definition naturality (M N : functor) (m : M ~~> N) :=
  forall (A B : UU1) (h : A -> B), (N # h) \o m A = m B \o (M # h).
Arguments naturality : clear implicits.

Module Natural.
Structure t (M N : functor) :=
  Pack { m : M ~~> N ; class : naturality M N m }.
Module Exports.
Coercion m : t >-> Funclass.
Notation "f ~> g" := (t f g).
End Exports.
End Natural.
Export Natural.Exports.

Section natrans_lemmas.
Variables (M N : functor) (phi : M ~> N).
Lemma natural (A B : UU1) (h : A -> B) : (N # h) \o phi A = phi B \o (M # h).
Proof. by case: phi => ?. Qed.
Lemma nattrans_ext (f g : M ~> N) :
  f = g <-> forall a, (f a = g a :> (_ -> _)).
Proof.
split => [ -> // |]; move: f g => [f Hf] [g Hg] /= fg.
have ? : f = g by exact: FunctionalExtensionality.functional_extensionality_dep.
subst g; congr (Natural.Pack _); exact/boolp.Prop_irrelevance.
Qed.
End natrans_lemmas.

Section id_natural_transformation.
Variables C : functor.
Definition natural_id : naturality _ _ (fun A => @id (C A)). Proof. by []. Qed.
Definition NId : C ~> C := Natural.Pack natural_id.
End id_natural_transformation.

Section vertical_composition.
Variables C D E : functor.
Variables (g : D ~> E) (f : C ~> D).
Definition ntcomp := fun A => g A \o f A.
Definition natural_vcomp : naturality _ _ ntcomp.
Proof. by move=> A B h; rewrite compA (natural g) -compA (natural f). Qed.
Definition VComp : C ~> E := Natural.Pack natural_vcomp.
End vertical_composition.

Notation "f \v g" := (VComp f g).

Lemma vassoc (F1 F2 G H : functor) (f : F1 ~> F2) (g : G ~> F1) (h : H ~> G) :
  f \v g \v h = f \v (g \v h).
Proof. by apply nattrans_ext => a /=. Qed.

Section horizontal_composition.
Variables (F G F' G' : functor) (s : F ~> G) (t : F' ~> G').
Lemma natural_hcomp :
  naturality (F' \O F) (G' \O G) (fun A => @t (G A) \o F' # (@s A)).
Proof.
move=> A B h; rewrite compA (natural t) -compA -[in RHS]compA.
by congr (_ \o _); rewrite FCompE -2!functor_o (natural s).
Qed.
Definition HComp : (F' \O F) ~> (G' \O G) := Natural.Pack natural_hcomp.
End horizontal_composition.

Notation "f \h g" := (HComp g f).

Section natural_transformation_example.
Definition fork' : FId ~~> squaring := fun A (a : A) => (a, a).
Lemma fork_natural : naturality _ _ fork'. Proof. by []. Qed.
Definition fork : FId ~> squaring := Natural.Pack fork_natural.
End natural_transformation_example.

Section functor_natural_transformation.
Variables (S F G : functor) (nt : F ~> G).
Definition fun_app_nt : S \O F ~~> S \O G :=
  fun (A : UU1) => S # (nt A).
Lemma natural_fun_app_nt : naturality (S \O F) (S \O G) fun_app_nt.
Proof.
by move=> *; rewrite /fun_app_nt 2!FCompE -2!(functor_o S) natural.
Qed.
Definition functor_app_natural : (S \O F) ~> (S \O G) :=
  Natural.Pack natural_fun_app_nt.
End functor_natural_transformation.

Lemma functor_app_naturalE (S F G : functor) (nt : F ~> G) :
  functor_app_natural S nt = NId S \h nt.
Proof. by apply nattrans_ext => a /=; rewrite compidf. Qed.

Definition eta_type (f g : functor) := FId ~> g \O f.
Definition eps_type (f g : functor) := f \O g ~> FId.
Module TriangularLaws.
Section triangularlaws.
Variables (F G : functor).
Variables (eps : eps_type F G) (eta : eta_type F G).
Definition left := forall A, @eps (F A) \o (F # @eta A) = @id (F A).
Definition right := forall A, (G # @eps A) \o @eta (G A) = @id (G A).
End triangularlaws.
End TriangularLaws.

Module AdjointFunctor.
Section adjointfunctor.
Variables F G : functor.
Record t := mk {
  eta : eta_type F G ;
(*  nat_eta : naturality _ _ eta ;*)
  eps : eps_type F G ;
(*  nat_eps : naturality _ _ eps ;*)
  tri_left : TriangularLaws.left eps eta ;
  tri_right : TriangularLaws.right eps eta}.
End adjointfunctor.
Section lemmas.
Variables (F G : functor) (H : t F G).
Definition hom_iso (A B : UU1) (h : F A -> B) : A -> G B := (G # h) \o @eta _ _ H A.
Definition hom_inv (A B : UU1) (h : A -> G B) : F A -> B := @eps _ _ H B \o (F # h).
End lemmas.
End AdjointFunctor.
Arguments AdjointFunctor.t : clear implicits.

Notation "F -| G" := (AdjointFunctor.t F G).

Section adjoint_example.
Variable (X : UU1).
Lemma curry_naturality :
  naturality (curry_F X \O uncurry_F X) FId (fun A (af : X * (X -> A)) => af.2 af.1).
Proof. by []. Qed.
Definition curry_eps : eps_type (curry_F X) (uncurry_F X) := Natural.Pack curry_naturality.
Lemma curry_naturality2 :
  naturality FId (uncurry_F X \O curry_F X) (fun (A : Type) (a : A) => pair^~ a).
Proof. by []. Qed.
Definition curry_eta : eta_type (curry_F X) (uncurry_F X) := Natural.Pack curry_naturality2.
Lemma adjoint_currry : curry_F X -| uncurry_F X.
Proof.
apply: (@AdjointFunctor.mk _ _ curry_eta curry_eps).
by move=> A; rewrite /TriangularLaws.left boolp.funeqE; case.
move=> A; rewrite /TriangularLaws.right /uncurry_F /curry_eps /curry_eta /uncurry_M.
by rewrite /= /uncurry_f /= /comp /= boolp.funeqE => f; rewrite boolp.funeqE.
Qed.
End adjoint_example.

Module BindLaws.
Section bindlaws.
Variable M : functor.

Variable b : forall (A B : UU1), M A -> (A -> M B) -> M B.

Local Notation "m >>= f" := (b m f).

Definition associative := forall A B C (m : M A) (f : A -> M B) (g : B -> M C),
  (m >>= f) >>= g = m >>= (fun x => (f x >>= g)).

Definition right_distributive (add : forall B, M B -> M B -> M B) :=
  forall A B (m : M A) (k1 k2 : A -> M B),
    m >>= (fun x => add _ (k1 x) (k2 x)) = add _ (m >>= k1) (m >>= k2).

Definition left_distributive (add : forall B, M B -> M B -> M B) :=
  forall A B (m1 m2 : M A) (k : A -> M B),
    (add _ m1 m2) >>= k = add _ (m1 >>= k) (m2 >>= k).

Definition left_zero (f : forall A, M A) :=
  forall (A B : UU1) (g : A -> M B), f A >>= g = f B.

Definition right_zero (f : forall A, M A) :=
  forall (A B : UU1) (g : M B), g >>= (fun _ => f A) = f A.

Definition left_neutral (r : FId ~> M) :=
  forall (A B : UU1) (a : A) (f : A -> M B), r _ a >>= f = f a.

Definition right_neutral (r : forall A : UU1, A -> M A) :=
  forall A (m : M A), m >>= r _ = m.

Definition left_id (r : forall A, M A) (op : forall B, M B -> M B -> M B) :=
  forall A (m : M A), op _ (r _) m = m.

Definition right_id (r : forall A, M A) (op : forall B, M B -> M B -> M B) :=
  forall A (m : M A), op _ m (r _) = m.

End bindlaws.
End BindLaws.

Module monad_of_adjoint.
Section def.
Variables (F G : functor) (eps : eps_type F G) (eta : eta_type F G).
Definition M := G \O F.
Definition mu : M \O M ~~> M := fun A => G # (@eps (F A)).
Definition bind A B (m : M A) (f : A -> M B) : M B := mu ((M # f) m).
End def.
Section prop.
Variables (f g : functor).
Hypothesis Had : f -| g.
Let eps : eps_type f g := AdjointFunctor.eps Had.
Let eta : eta_type f g := AdjointFunctor.eta Had.
Section mu_eps_natural.
Notation M := (M f g).
Notation mu := (mu eps).
Lemma muM_natural : naturality _ _ mu.
Proof.  move => A B h.
rewrite (_ : (M \O M) # h = g # ((f \O g) # (f # h))) //.
rewrite (_ : _ \o g # ((f \O g) # (f # h)) =
  g # (@eps (f B) \o ((f \O g) # (f # h)))); last by rewrite -functor_o.
by rewrite -natural FIdf FCompE functor_o.
Qed.
Lemma epsC A : @eps _ \o @eps _ = @eps _ \o f # (g # (@eps _)) :> ((f \o g) ((f \o g) A) -> A).
Proof. by rewrite -natural. Qed.
Lemma muMA A : @mu A \o @mu (M A) = @mu A \o (M # @mu A).
Proof.
have -> : g # @eps (f A) \o g # @eps (f (M A)) =
  g # (@eps (f A) \o @eps (f (M A))) by rewrite functor_o.
by rewrite epsC functor_o.
Qed.
End mu_eps_natural.
Lemma bindetaf : BindLaws.left_neutral (bind eps) eta.
Proof.
rewrite /BindLaws.left_neutral => A B a h.
rewrite /bind /mu.
rewrite -(compE ((g \O f) # h)) (natural eta) -(compE (g # _)) compA.
by rewrite AdjointFunctor.tri_right.
Qed.
Lemma bindmeta : BindLaws.right_neutral (bind eps) eta.
Proof.
rewrite /BindLaws.right_neutral => A m.
rewrite /bind /mu -(compE (g # _)).
by rewrite -functor_o AdjointFunctor.tri_left functor_id.
Qed.
Lemma law3 : BindLaws.associative (bind eps).
Proof.
rewrite /BindLaws.associative => A B C x ab bc.
rewrite /bind.
set N := M f g.  set j := mu eps.
rewrite [X in _ = j C X](_ : _ = (N # (j C)) ((N # (N # bc)) ((N # ab) x))); last first.
  rewrite functor_o /comp.
  congr (N # j C).
  by rewrite functor_o.
move: muMA (muM_natural bc).
rewrite -/N -/j.
move=> muMA.
rewrite FCompE.
have -> : (N # bc) (j B ((N # ab) x)) = (N # bc \o j B) ((N # ab) x) by [].
move=> ->.
rewrite compE.
rewrite [LHS](_ : _ = (j C \o j (N C)) ((N # (N # bc)) ((N # ab) x))) //.
by rewrite muMA.
Qed.
End prop.
End monad_of_adjoint.

Section composite_adjoint.
Variables (F0 U0 : functor).
Hypothesis H0 : F0 -| U0.
Let eta0 : eta_type F0 U0 := AdjointFunctor.eta H0.
Let eps0 : eps_type F0 U0 := AdjointFunctor.eps H0.
Variables (F U : functor).
Hypothesis H : F -| U.
Let eta : eta_type F U := AdjointFunctor.eta H.
Let eps : eps_type F U := AdjointFunctor.eps H.

Lemma uni_naturality :
  naturality FId ((U0 \O U) \O (F \O F0)) (fun A : UU1 => U0 # eta (F0 A) \o eta0 A).
Proof.
move=> A B h; rewrite FIdf.
rewrite -[in RHS]compA -[in RHS](natural (AdjointFunctor.eta H0)) compA [in RHS]compA.
congr (_ \o _).
rewrite (FCompE U0 F0).  rewrite -[in RHS](functor_o U0).
rewrite -[in LHS](functor_o U0).
congr (_ # _).
by rewrite -(natural (AdjointFunctor.eta H)).
Qed.

Let uni : @eta_type (F \O F0) (U0 \O U) := Natural.Pack uni_naturality.

Lemma couni_naturality :
  naturality ((F \O F0) \O (U0 \O U)) FId (fun A : UU1 => eps A \o F # eps0 (U A)).
Proof.
move=> A B h.
rewrite [in LHS]compA {}(natural (AdjointFunctor.eps H)) -compA.
rewrite -[in RHS]compA; congr (_ \o _).
rewrite [in LHS]FCompE -[in LHS](functor_o F) [in LHS](natural (AdjointFunctor.eps H0)).
by rewrite -[in RHS](functor_o F).
Qed.

Let couni : @eps_type (F \O F0) (U0 \O U) := Natural.Pack couni_naturality.

Lemma composite_adjoint : F \O F0 -| U0 \O U.
Proof.
apply: (@AdjointFunctor.mk _ _ uni couni).
rewrite /TriangularLaws.left => A.
rewrite /couni /uni /=.
rewrite FCompE -compA -functor_o.
rewrite (_ : @eps0 _ \o F0 # _ = @eta (F0 A)); first exact: (AdjointFunctor.tri_left H).
rewrite functor_o compA -FCompE.
by rewrite -(natural (AdjointFunctor.eps H0)) /= FIdf -compA (AdjointFunctor.tri_left H0) compfid.
rewrite /TriangularLaws.right => A.
rewrite /couni /uni /=.
rewrite compA -[RHS](AdjointFunctor.tri_right H0 (U A)); congr (_ \o _).
rewrite FCompE -functor_o; congr (_ # _).
rewrite functor_o -compA -FCompE.
by rewrite (natural (AdjointFunctor.eta H)) FIdf compA (AdjointFunctor.tri_right H) compidf.
Qed.

End composite_adjoint.

Module JoinLaws.
Section join_laws.
Context {M : functor}.
Variables (ret : FId ~> M) (join : M \O M ~> M).

Definition left_unit := forall A, @join _ \o @ret _ = id :> (M A -> M A).

Definition right_unit := forall A, @join _ \o M # @ret _ = id :> (M A -> M A).

Definition associativity :=
  forall A, @join _ \o M # @join _ = @join _ \o @join _ :> (M (M (M A)) -> M A).

End join_laws.
End JoinLaws.

Section from_join_laws_to_bind_laws.
Variable F : functor.
Variable (ret : FId ~> F) (join : F \O F ~> F).

Hypothesis joinretM : JoinLaws.left_unit ret join.
Hypothesis joinMret : JoinLaws.right_unit ret join.
Hypothesis joinA : JoinLaws.associativity join.

Let bind (A B : UU1) (m : F A) (f : A -> F B) : F B := join _ ((F # f) m).

Lemma bindretf_derived : BindLaws.left_neutral bind ret.
Proof.
move=> A B a f; rewrite /bind -(compE (@join _)) -(compE _ (@ret _)) -compA.
by rewrite (natural ret) compA joinretM compidf.
Qed.

Lemma bindmret_derived : BindLaws.right_neutral bind ret.
Proof. by move=> A m; rewrite /bind -(compE (@join _)) joinMret. Qed.

Lemma bindA_derived : BindLaws.associative bind.
Proof.
move=> A B C m f g; rewrite /bind.
rewrite [LHS](_ : _ = ((@join _ \o (F # g \o @join _) \o F # f) m)) //.
rewrite (natural join) (compA (@join C)) -joinA -(compE (@join _)).
transitivity ((@join _ \o F # (@join _ \o (F # g \o f))) m) => //.
by rewrite -2!compA functor_o FCompE -[in LHS](functor_o F).
Qed.

End from_join_laws_to_bind_laws.

Module Monad.
Record mixin_of (M : functor) : UU2 := Mixin {
  ret : FId ~> M ;
  join : M \O M ~> M ;
  _ : JoinLaws.left_unit ret join ;
  _ : JoinLaws.right_unit ret join ;
  _ : JoinLaws.associativity join }.
Record class_of (M : UU1 -> UU1) := Class {
  base : Functor.mixin_of M ; mixin : mixin_of (Functor.Pack base) }.
Structure t : UU2 := Pack { m : UU1 -> UU1 ; class : class_of m }.
Definition baseType (M : t) := Functor.Pack (base (class M)).
Module Exports.
Definition RET (M : t) : FId ~> baseType M :=
  let: Pack _ (Class _ (Mixin ret _ _ _ _) ) := M
  return FId ~> baseType M in ret.
Arguments RET {M} : simpl never.
Definition JOIN (M : t) : baseType M \O baseType M ~> baseType M :=
  let: Pack _ (Class _ (Mixin _ join _ _ _)) := M in join.
Arguments JOIN {M} : simpl never.
Notation monad := t.
Coercion baseType : monad >-> functor.
Canonical baseType.
End Exports.
End Monad.
Export Monad.Exports.

Notation Ret := (@RET _ _).
Notation Join := (@JOIN _ _).

Section monad_interface.
Variable M : monad.
Lemma joinretM : JoinLaws.left_unit (@RET M) (@JOIN M).
Proof. by case: M => ? [? []]. Qed.
Lemma joinMret : JoinLaws.right_unit (@RET M) (@JOIN M).
Proof. by case: M => ? [? []]. Qed.
Lemma joinA : JoinLaws.associativity (@JOIN M).
Proof. by case: M => ? [? []]. Qed.
End monad_interface.

Section monad_lemmas.
Variable M : monad.

Definition Bind A B (x : M A) (f : A -> M B) : M B := Join ((M # f) x).
Arguments Bind {A B} : simpl never.
Local Notation "m >>= f" := (Bind m f).
Lemma bindE (A B : UU1) : forall x (f : A -> M B), x >>= f = Join ((M # f) x).
Proof. by []. Qed.
Lemma bindretf : BindLaws.left_neutral (@Bind) (@RET _).
Proof. apply: bindretf_derived; exact: joinretM. Qed.
Lemma bindmret : BindLaws.right_neutral (@Bind) (@RET _).
Proof. apply: bindmret_derived; exact: joinMret. Qed.
Lemma bindA : BindLaws.associative (@Bind).
Proof. apply bindA_derived; exact: joinA. Qed.

(*Lemma bindE' (A B : Type) : Bind = fun x (f : A -> M B) => Join ((M # f) x).
Proof. by []. Qed.*)
(*Lemma joinretM' A C (f:C->_) : @Join M A \o (@Ret M (M A) \o f) = f.
Proof. by rewrite compA joinretM. Qed.*)
(*Lemma joinMret' A C (f:C->_) : @Join M A \o (M # @Ret M A \o f) = f.
Proof. by rewrite compA joinMret. Qed.*)
(*Lemma joinA' A C (f:C->_) : @Join M A \o (M # @Join M A \o f) = @Join M A \o (@Join M (M A) \o f).
Proof. by rewrite compA joinA. Qed.*)
End monad_lemmas.
Arguments Bind {M A B} : simpl never.

Definition operation (E : functor) (M : monad) := E \O M ~> M.

Notation "'do' x <- m ; e" := (Bind m (fun x => e)) : do_notation.
Notation "'do' x : T <- m ; e" := (Bind m (fun x : T => e)) (only parsing) : do_notation.
Delimit Scope do_notation with Do.
Notation "m >>= f" := (Bind m f) : monae_scope.
Notation "m >> f" := (Bind m (fun _ => f)) : monae_scope.
Delimit Scope monae_scope with monae.
Local Open Scope monae_scope.

Definition skip M := @RET M _ tt.
Arguments skip {M} : simpl never.

Ltac bind_ext :=
  let congr_ext m := ltac:(congr (Bind m); rewrite boolp.funeqE) in
  match goal with
    | |- @Bind _ _ _ ?m ?f1 = @Bind _ _ _ ?m ?f2 =>
      congr_ext m
    | |- @Bind _ _ _ ?m1 ?f1 = @Bind _ _ _ ?m2 ?f2 =>
      first[ simpl m1; congr_ext m1 | simpl m2; congr_ext m2 ]
  end.

(* experimental *)
Tactic Notation "With" tactic(tac) "Open" ssrpatternarg(pat) :=
  ssrpattern pat;
  let f := fresh "f" in
  intro f;
  let g := fresh "g" in
  let typ := typeof f in
  let x := fresh "x" in
  evar (g : typ);
  rewrite (_ : f = g);
  [rewrite {}/f {}/g|
   rewrite boolp.funeqE => x; rewrite {}/g {}/f; tac]; last first.

Tactic Notation "Open" ssrpatternarg(pat) :=
  With (idtac) Open pat.

Tactic Notation "Inf" tactic(tac) :=
  (With (tac; reflexivity) Open (X in @Bind _ _ _ _ X = _ )) ||
  (With (tac; reflexivity) Open (X in _ = @Bind _ _ _ _ X)).

Tactic Notation "rewrite_" constr(lem) :=
  (With (rewrite lem; reflexivity) Open (X in @Bind _ _ _ _ X = _ )) ||
  (With (rewrite lem; reflexivity) Open (X in _ = @Bind _ _ _ _ X)).

Lemma bindmskip (M : monad) (m : M unit) : m >> skip = m.
Proof. rewrite -[RHS]bindmret; bind_ext; by case. Qed.

Lemma bindskipf (M : monad) A (m : M A) : skip >> m = m.
Proof. exact: bindretf. Qed.

Fixpoint sequence (M : monad) A (s : seq (M A)) : M (seq A) :=
  (if s isn't h :: t then Ret [::] else
  do v <- h; do vs <- sequence t; Ret (v :: vs))%Do.

Lemma sequence_nil (M : monad) (A : UU1) : sequence [::] = Ret [::] :> M (seq A).
Proof. by []. Qed.

Lemma sequence_cons (M : monad) A h (t : seq (M A)) :
  (sequence (h :: t) = do x <- h ; do vs <- sequence t ; Ret (x :: vs))%Do.
Proof. by []. Qed.

Module Monad_of_ret_bind.
Section monad_of_ret_bind.
Variable M : functor.
Variable ret : FId ~> M.
Variable bind : forall (A B : UU1), M A -> (A -> M B) -> M B.
Hypothesis bindretf : BindLaws.left_neutral bind ret.
Hypothesis bindmret : BindLaws.right_neutral bind ret.
Hypothesis bindA : BindLaws.associative bind.

Definition Map (A B : UU1) (f : A -> B) (m : M A) := bind m (@ret B \o f).
Lemma Map_id : FunctorLaws.id Map.
Proof. by move=> A; rewrite boolp.funeqE => m; rewrite /Map bindmret. Qed.
Lemma Map_o : FunctorLaws.comp Map.
Proof.
move=> A B C g h; rewrite boolp.funeqE => m.
rewrite /Map compE bindA; congr bind.
by rewrite boolp.funeqE => a; rewrite bindretf.
Qed.
Definition functor_mixin := Functor.Mixin Map_id Map_o.
Let M' := Functor.Pack functor_mixin.

Lemma MapE (A B : UU1) (f : A -> B) m : (M' # f) m = bind m (ret B \o f).
Proof. by []. Qed.

Lemma naturality_ret : naturality FId M' ret.
Proof.
move=> A B h; rewrite FIdf boolp.funeqE => ?.
by rewrite compE /= /Map MapE /= bindretf.
Qed.

Let ret' : FId ~> M' := Natural.Pack naturality_ret.

Let bind_Map (A B C : UU1) (f : A -> B) (m : M A) (g : B -> M C) :
  bind (Map f m) g = bind m (g \o f).
Proof.
rewrite /Map bindA; congr bind; by rewrite boolp.funeqE => ?; rewrite bindretf.
Qed.

Lemma naturality_join : naturality (M' \O M') M' (fun A : UU1 => (bind (B:=A))^~ id).
Proof.
move=> A B h; rewrite boolp.funeqE => mma.
by rewrite /Fun 2!compE /Map bind_Map [in LHS] bindA.
Qed.

Definition join : M' \O M' ~> M' := Natural.Pack naturality_join.

Let bindE (A B : UU1) m (f : A -> M' B) : bind m f = join _ ((M' # f) m).
Proof. by rewrite /join /= bind_Map. Qed.

Lemma joinretM : JoinLaws.left_unit ret' join.
Proof.
rewrite /join => A; rewrite boolp.funeqE => ma /=.
by rewrite bindretf. Qed.

Lemma joinMret : JoinLaws.right_unit ret' join.
Proof.
rewrite /join => A; rewrite boolp.funeqE => ma /=.
by rewrite bind_Map compidf bindmret.
Qed.

Lemma joinA : JoinLaws.associativity join.
Proof.
move=> A; rewrite boolp.funeqE => mmma.
by rewrite /join /= bind_Map compidf bindA.
Qed.

Definition monad_mixin := Monad.Mixin joinretM joinMret joinA.
End monad_of_ret_bind.
Module Exports.
Definition Monad_of_ret_bind M ret bind a b c :=
  Monad.Pack (Monad.Class (@monad_mixin M ret bind a b c)).
End Exports.
End Monad_of_ret_bind.
Export Monad_of_ret_bind.Exports.

Section kleisli.
Variable M : monad.

Definition kleisli (A B C : UU1) (m : B -> M C) (n : A -> M B) : A -> M C :=
  Join \o (M # m) \o n.
Local Notation "m <=< n" := (kleisli m n).
Local Notation "m >=> n" := (kleisli n m).

Lemma bind_kleisli (A B C : UU1) m (f : A -> M B) (g : B -> M C) :
  m >>= (f >=> g) = (m >>= f) >>= g.
Proof. by rewrite bindA; bind_ext => a; rewrite /kleisli !compE join_fmap. Qed.

Lemma ret_kleisli (A B : UU1) (k : A -> M B) : Ret >=> k = k.
Proof. by rewrite /kleisli -compA (natural RET) FIdf compA joinretM. Qed.

Local Open Scope mprog.
Lemma fcomp_kleisli (A B C D : UU1) (f : A -> B) (g : C -> M A) (h : D -> M C) :
  f (o) (g <=< h) = (f (o) g) <=< h.
Proof.
by rewrite /kleisli 2!fcomp_def 2!(compA (fmap f)) (natural JOIN) functor_o compA.
Qed.

Lemma kleisli_fcomp (A B C : UU1) (f : A -> M B) (g : B -> A) (h : C -> M B) :
  ((f \o g) <=< h) = f <=< (g (o) h).
Proof. by rewrite /kleisli fcomp_def functor_o 2!compA. Qed.
Local Close Scope mprog.

End kleisli.
Notation "m <=< n" := (kleisli m n) : monae_scope.
Notation "m >=> n" := (kleisli n m) : monae_scope.

Section fmap_and_join.
Variable M : monad.
Local Open Scope mprog.

Lemma fmapE (A B : UU1) (f : A -> B) (m : M _) : fmap f m = m >>= (Ret \o f).
Proof.
by rewrite bindE [in RHS]functor_o [in RHS]compE -[in RHS](compE Join) joinMret.
Qed.

Lemma bind_fmap (A B C : UU1) (f : A -> B) (m : M A) (g : B -> M C) :
  fmap f m >>= g = m >>= (g \o f).
Proof. by rewrite fmapE bindA; rewrite_ bindretf. Qed.

Lemma fmap_if (A B : UU1) (f : A -> B) b (m : M A) a :
  fmap f (if b then m else Ret a) = if b then fmap f m else Ret (f a).
Proof. case: ifPn => Hb //; by rewrite fmapE bindretf. Qed.

Lemma fmap_bind (A B C : UU1) (f : A -> B) m (g : C -> M A) :
  fmap f (m >>= g) = m >>= (f (o) g).
Proof.
rewrite fcomp_def fmapE bindA; bind_ext => c; by rewrite compE -/(fmap _ _) fmapE.
Qed.

Lemma skip_fmap (A B : UU1) (f : A -> B) (mb : M B) ma :
  mb >> (fmap f ma) = fmap f (mb >> ma).
Proof. by rewrite fmap_bind fcomp_def. Qed.

(*Lemma rev_map A B (f : A -> B) : rev \o map f = map f \o rev.
Proof.
apply functional_extensionality.
by elim=> // h t /= IH; rewrite !rev_cons IH map_rcons.
Qed.*)

(* TODO: move? *)
Lemma foldl_revE (T R : Type) (f : R -> T -> R) (z : R) :
  foldl f z \o rev = foldr (fun x : T => f^~ x) z.
Proof. by rewrite boolp.funeqE => s; rewrite -foldl_rev. Qed.

Lemma mfoldl_rev (T R : UU1) (f : R -> T -> R) (z : R) (s : seq T -> M (seq T)) :
  foldl f z (o) (rev (o) s) = foldr (fun x => f^~ x) z (o) s.
Proof.
rewrite boolp.funeqE => x; rewrite !fcompE 3!fmapE !bindA.
bind_ext => ?; by rewrite bindretf /= -foldl_rev.
Qed.

Lemma joinE A (pp : M (M A)) : Join pp = pp >>= id.
Proof. rewrite bindE; congr Join; by rewrite functor_id. Qed.

Lemma join_fmap (A B : UU1) (f : A -> M B) (m : M A) : Join (fmap f m) = m >>= f.
Proof. by rewrite bindE. Qed.

End fmap_and_join.

(*
(* monads on Type are strong monads *)
Section strength.
Variable M : monad.
Definition strength A B (xy : (A * M B)%type) : M (A * B)%type :=
  let (x,my) := xy in my >>= (fun y => Ret (x,y)).
Lemma strengthE A B (x:A) (my:M B) : strength (x,my) = my >>= (fun y => Ret (x,y)).
Proof. done. Qed.
Lemma strength_unit A : snd = M # snd \o strength (A:=unit) (B:=A).
Proof.
apply functional_extensionality => x.
case: x => i ma.
rewrite compE strengthE.
rewrite -fmapE fmap_bind fcomp_def.
rewrite bindE.
have ->: Join ((M # (M # snd \o (fun y : A => Ret (i, y)))) ma) =
((M # snd \o Join) \o M # (fun y : A => Ret (i, y))) ma
  by rewrite functor_o join_naturality.
rewrite functor_o.
have ->: ((M # snd \o Join) \o (M # Ret \o M # pair i)) ma =
(M # snd \o (Join \o M # Ret) \o M # pair i) ma by done.
rewrite joinMret compfid.
rewrite -functor_o.
have ->: snd \o pair i = id by done.
by rewrite functor_id.
Qed.
End strength.
*)

Definition mpair {M : monad} {A} (xy : (M A * M A)%type) : M (A * A)%type :=
  let (mx, my) := xy in
  mx >>= (fun x => my >>= fun y => Ret (x, y)).

Lemma mpairE (M : monad) A (mx my : M A) :
  mpair (mx, my) = mx >>= (fun x => my >>= fun y => Ret (x, y)).
Proof. by []. Qed.

Lemma naturality_mpair (M : monad) (A B : UU1) (f : A -> B) (g : A -> M A):
  (M # f^`2) \o (mpair \o g^`2) = mpair \o ((M # f) \o g)^`2.
Proof.
rewrite boolp.funeqE => -[a0 a1].
rewrite compE fmap_bind.
rewrite compE mpairE compE bind_fmap; bind_ext => a2.
rewrite fcompE fmap_bind 2!compE bind_fmap; bind_ext => a3.
by rewrite fcompE -(compE (M # f^`2)) (natural RET) FIdf.
Qed.

(*Local Notation "[ \o f , .. , g , h ]" := (f \o .. (g \o h) ..)
  (at level 0) (*, format "[ \o '['  f , '/' .. , '/' g , '/' h ']' ]"
  ).*) : test_scope.

Local Open Scope test_scope.

Lemma naturality_mpair' (M : monad) A B (f : A -> B) (g : A -> M A):
  (M # f^`2) \o (mpair \o g^`2) = mpair \o ((M # f) \o g)^`2.
Proof.
rewrite funeqE => -[a0 a1].
change ((M # f^`2 \o (mpair \o g^`2)) (a0, a1)) with
    ((M # f^`2) (mpair (g a0, g a1))).
change ((mpair \o (M # f \o g)^`2) (a0, a1)) with
    (mpair ((M # f \o g) a0,(M # f \o g) a1)).
rewrite !mpairE.
rewrite !bindE.
evar (T : Type);evar (RHS : A -> T).
have ->: (fun x : A => do y <- g a1; Ret (x, y)) = RHS.
  rewrite funeqE => x; rewrite bindE.
  rewrite functor_o.
  change (Join ([\o M # Ret,M # pair x] (g a1))) with
        ([\o Join,M # Ret,M # pair x] (g a1)).
    rewrite joinMret'.
  exact: erefl.
rewrite /RHS {RHS}; rewrite {T}.
change ((M # f^`2) (Join ((M # (fun x : A => (M # pair x) (g a1))) (g a0)))) with
    ((M # f^`2 \o Join) ((M # (fun x : A => (M # pair x) (g a1))) (g a0))).
rewrite join_naturality.
evar (T : Type);evar (RHS : T).
have->:(M # (fun x : B => do y <- (M # f \o g) a1; Ret (x, y))) = RHS.
- rewrite functor_o.
  rewrite bindE'.
  rewrite functor_o.
  exact: erefl.
rewrite/RHS{RHS};rewrite{T}.
change
  (
    Join
    (((M # Join \o M # (Fun M (B:=M (B * B)%type))^~ ((M # f \o g) a1)) \o
        M # (fun x y : B => Ret (x, y))) ((M # f \o g) a0))
  ) with
    (
      (
        [ \o Join ,
          (M # Join) ,
          (M # (Fun M (B:=M (B * B)%type))^~ ((M # f \o g) a1)) ,
          (M # (fun x y : B => Ret (x, y))) ,
          (M # f \o g) ]
      ) a0)
    .
rewrite joinA'.
(*
rewrite fmap_bind. compE [in RHS]/= bind_fmap; bind_ext => a2.
rewrite fcompE fmap_bind compE bind_fmap; bind_ext => a3.
by rewrite fcompE -(compE (fmap M # f^`2)) fmap_ret.
Qed.
*)
Abort.

Local Close Scope test_scope.
*)

Section rep.

Variable M : monad.

Fixpoint rep (n : nat) (mx : M unit) : M unit :=
  if n is n.+1 then mx >> rep n mx else skip.

Lemma repS mx n : rep n.+1 mx = rep n mx >> mx.
Proof.
elim: n => /= [|n IH]; first by rewrite bindmskip bindskipf.
by rewrite bindA IH.
Qed.

Lemma rep1 mx : rep 1 mx = mx. Proof. by rewrite repS bindskipf. Qed.

Lemma rep_addn m n mx : rep (m + n) mx = rep m mx >> rep n mx.
Proof.
elim: m n => [|m IH /=] n; by
  [rewrite bindskipf add0n | rewrite -addnE IH bindA].
Qed.

End rep.

Section MonadCount.

Variable M : monad.
Variable tick : M unit.

Fixpoint hanoi n : M unit :=
  if n is n.+1 then hanoi n >> tick >> hanoi n else skip.

Lemma hanoi_rep n : hanoi n = rep (2 ^ n).-1 tick.
Proof.
elim: n => // n IH /=.
rewrite IH -repS prednK ?expn_gt0 // -rep_addn.
by rewrite -subn1 addnBA ?expn_gt0 // addnn -muln2 -expnSr subn1.
Qed.

End MonadCount.
