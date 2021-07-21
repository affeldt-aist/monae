(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2020 monae authors, license: LGPL-2.1-or-later               *)
Ltac typeof X := type of X.

Require Import ssrmatching Reals.
From mathcomp Require Import all_ssreflect.
From mathcomp Require boolp.
From infotheo Require Import Reals_ext.
Require Import monae_lib.
From HB Require Import structures.

(******************************************************************************)
(*        A formalization of monadic effects over the category Set            *)
(*                                                                            *)
(* We consider the type Type of Coq as the category Set and define functors   *)
(* and a hierarchy of monads on top of functors. These monads are used to     *)
(* develop the basics of monadic equational reasoning. The file category.v    *)
(* provides a more generic definition of functors and monads as well as a     *)
(* bridge to this file.                                                       *)
(*                                                                            *)
(* Module FunctorLaws == map laws of a functor                                *)
(*            functor == type of functors                                     *)
(*              F # g == application of the functor F to the morphism g       *)
(*                FId == the identity functor                                 *)
(*                 \O == composition of functors                              *)
(*             F ~> G == natural transformation from functor F to functor G   *)
(*            f ~~> g == forall A, f A -> g A, notation used for the          *)
(*                       components of a natural transformation               *)
(*   naturality F G f == the components f form a natural transformation       *)
(*                       F ~> G                                               *)
(*    Module JoinLaws == join laws of a monad                                 *)
(*            isMonad == mixin of monad                                       *)
(*              monad == type of monads                                       *)
(*                Ret == natural transformation FId ~> M for a monad M        *)
(*               Join == natural transformation M \O M ~> M for a monad M     *)
(*    Module BindLaws == bind laws of a monad                                 *)
(*                >>= == notation for the standard bind operator              *)
(*                                                                            *)
(* Failure and nondeterministic monads:                                       *)
(*          failMonad == failure monad                                        *)
(*        failR0Monad == fail is right zero of bind                           *)
(*           altMonad == monad with nondeterministic choice                   *)
(*       prePlusMonad == nondeterminism + failR0 + distributivity             *)
(*          plusMonad == preplusMonad + commutativity and idempotence         *)
(*         altCIMonad == monadAlt + commutativity + idempotence               *)
(*        nondetMonad == monadFail + monadAlt                                 *)
(*      nondetCIMonad == monadFail + monadAltCI                               *)
(*        exceptMonad == monadFail + catch                                    *)
(*                                                                            *)
(* Control monads (wip):                                                      *)
(*   contMonad, shiftresetMonad, jumpMonad                                    *)
(*                                                                            *)
(* State monads:                                                              *)
(*         stateMonad S == state monad with a state of type S                 *)
(*        stateRunMonad == state + RunStateT                                  *)
(*                         let N be a monad and S be the type of states, then *)
(*                         when m is a computation in the monad               *)
(*                         stateRunMonad S N, RunStateT m s runs m in a       *)
(*                         state s and returns a computation in the monad N   *)
(*  exceptStateRunMonad == stateRun + except                                  *)
(*           reifyMonad == reify interface                                    *)
(*      stateReifyMonad == monadState + reify                                 *)
(*  failStateReifyMonad == stateReify + fail                                  *)
(*     nondetStateMonad == backtrackable state                                *)
(*           arrayMonad == array monad                                        *)
(*                                                                            *)
(* Trace monads:                                                              *)
(*            traceMonad == trace monad                                       *)
(*       traceReifyMonad == trace + reify                                     *)
(*       stateTraceMonad == state + trace                                     *)
(*  stateTraceReifyMonad == stateTrace + reify                                *)
(*                                                                            *)
(* Probability monads:                                                        *)
(*         probaMonad == probabilistic choice and bind left-distributes over  *)
(*                       choice                                               *)
(*        probDrMonad == probaMonad + bind right-distributes over choice      *)
(*       altProbMonad == combined (probabilistic and nondeterministic) choice *)
(*    exceptProbMonad == exceptions + probabilistic choice                    *)
(*                                                                            *)
(* Freshness monads:                                                          *)
(*         freshMonad == monad with freshness                                 *)
(*     failFreshMonad == freshMonad + failure                                 *)
(*                                                                            *)
(* references:                                                                *)
(* - R. Affeldt, D. Nowak, Extending Equational Monadic Reasoning with Monad  *)
(* Transformers, https://arxiv.org/abs/2011.03463                             *)
(* - R. Affeldt, D. Nowak, T. Saikawa, A Hierarchy of Monadic Effects for     *)
(* Program Verification using Equational Reasoning, MPC 2019                  *)
(* - J. Gibbons, R. Hinze, Just do it: simple monadic equational reasoning,   *)
(* ICFP 2011                                                                  *)
(* - J. Gibbons, Unifying Theories of Programming with Monads, UTP 2012       *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope do_notation.
Declare Scope mprog.
Declare Scope monae_scope.
Delimit Scope monae_scope with monae.
Declare Scope proba_monad_scope.

Reserved Notation "f (o) g" (at level 11).
Reserved Notation "m >> f" (at level 49).
Reserved Notation "'fmap' f" (at level 4).
Reserved Notation "x '[~]' y" (at level 50).
Reserved Notation "mx <| p |> my" (format "mx  <| p |>  my", at level 49).

Notation "f ~~> g" := (forall A, f A -> g A)
  (at level 51, only parsing) : monae_scope.

Local Open Scope monae_scope.

Notation UU1 := Type.
Notation UU0 := Type.

(* NB: not putting M in Set -> Set because of expressions like:
  M (A * (size s).-1.-tuple A)%type *)
Module FunctorLaws.
Section def.
Variable (M : UU0 -> UU0) (f : forall A B : UU0, (A -> B) -> M A -> M B).
Definition id := forall A : UU0, f id = id :> (M A -> M A).
Definition comp := forall (A B C : UU0) (g : B -> C) (h : A -> B),
  f (g \o h) = f g \o f h :> (M A -> M C).
End def.
End FunctorLaws.

HB.mixin Record isFunctor (M : UU0 -> UU0) := {
  actm : forall A B : UU0, (A -> B) -> M A -> M B ;
  functor_id : FunctorLaws.id actm ;
  functor_o : FunctorLaws.comp actm }.

HB.structure Definition Functor := {M of isFunctor M}.
Notation functor := Functor.type.

Notation "F # g" := (@actm F _ _ g) : monae_scope.
Notation "'fmap' f" := (_ # f) : mprog.

Section functorid.
Definition id_f (A B : UU0) (f : A -> B) : idfun A -> idfun B := f.
Lemma id_id : FunctorLaws.id id_f. Proof. by []. Qed.
Lemma id_comp : FunctorLaws.comp id_f. Proof. by []. Qed.
End functorid.

HB.instance Definition _ := isFunctor.Build idfun id_id id_comp.

(* NB: consider eliminating *)
Definition FId := [the functor of idfun].

Section functorcomposition.
Variables f g : functor.
Definition functorcomposition (A B : UU0) := fun h : A -> B => f # (g # h).
Lemma functorcomposition_id : FunctorLaws.id functorcomposition.
Proof.
by rewrite /FunctorLaws.id => A; rewrite /functorcomposition 2!functor_id.
Qed.
Lemma functorcomposition_comp : FunctorLaws.comp functorcomposition.
Proof.
rewrite /FunctorLaws.comp => A B C g' h; rewrite /functorcomposition.
rewrite boolp.funeqE => m; by rewrite [in RHS]compE 2!functor_o.
Qed.
HB.instance Definition _ :=
  isFunctor.Build (f \o g) functorcomposition_id functorcomposition_comp.

(* TODO: consider eliminating *)
Definition FComp := [the functor of f \o g].
End functorcomposition.

Notation "f \O g" := (FComp f g) : monae_scope.

Section functorcomposition_lemmas.
Lemma FCompId f : f \O FId = f.
Proof.
case: f => M [[? ? ?]]; congr (Functor.Pack (Functor.Class _)).
by congr (isFunctor.Axioms_ _); exact/proof_irr.
Qed.
Lemma FIdComp f : FId \O f = f.
Proof.
case: f => M [[? ? ?]]; congr (Functor.Pack (Functor.Class _)).
by congr (isFunctor.Axioms_ _); exact/proof_irr.
Qed.
Lemma FIdf (A B : UU0) (f : A -> B) : FId # f = f. Proof. by []. Qed.
Lemma FCompA (f g h : functor) : (f \O g) \O h = f \O (g \O h).
Proof.
move: f g h => [f [[? ? ?]]] [g [[? ? ?]]] [h [[? ? ?]]].
congr (Functor.Pack (Functor.Class _)).
by congr (isFunctor.Axioms_ _); exact/proof_irr.
Qed.
Lemma FCompE (f g : functor) (A B : UU0) (k : A -> B) :
  (f \O g) # k = f # (g # k).
Proof. by []. Qed.
End functorcomposition_lemmas.

(* monadic counterpart of function composition:
   composes a pure function after a monadic function *)
Section fcomp.
Variable M : functor.

Definition fcomp (A B C : UU0) (f : A -> B) (g : C -> M A) :=
  locked ((M # f) \o g).
Arguments fcomp : simpl never.
Local Notation "f (o) g" := (fcomp f g).

Lemma fcomp_def (A B C : UU0) (f : A -> B) (g : C -> M A) :
  f (o) g = ((M # f)) \o g.
Proof. by rewrite /fcomp; unlock. Qed.

Lemma fcompE (A B C : UU0) (f : A -> B) (g : C -> M A) c :
  (f (o) g) c = (M # f) (g c).
Proof. by rewrite fcomp_def. Qed.

Lemma fcomp_comp (A B C D : UU0) (f : A -> B) (g : C -> A) (m : D -> M C) :
  (f \o g) (o) m = f (o) (g (o) m).
Proof. by rewrite 3!fcomp_def functor_o compA. Qed.

End fcomp.
Notation "f (o) g" := (fcomp f g) : mprog.
Arguments fcomp : simpl never.

Lemma functor_ext (F G : functor) :
  forall (H : Functor.sort F = Functor.sort G),
  @actm G =
  eq_rect _ (fun m : UU0 -> UU0 => forall A B : UU0, (A -> B) -> m A -> m B) (@actm F) _ H  ->
  G = F.
Proof.
move: F G => [F [[HF1 HF2 HF3]]] [G [[HG1 HG2 HG3]]] /= H.
subst F => /= H.
congr (Functor.Pack (Functor.Class _)).
have ? : HG1 = HF1.
  rewrite /actm /= in H.
  apply fun_ext_dep => x.
  apply fun_ext_dep => y.
  apply fun_ext_dep => z.
  by move/(congr1 (fun i => i x y z)) : H.
subst HG1.
congr (isFunctor.Axioms_ _); exact/proof_irr.
Defined.

Definition naturality (M N : functor) (f : M ~~> N) :=
  forall (A B : UU0) (h : A -> B), (N # h) \o f A = f B \o (M # h).
Arguments naturality : clear implicits.

(*HB.mixin Record isNatural (M N : functor) (f : M ~~> N) := {
  natural : naturality M N f
}.

#[infer(M), infer(N)]
(* TODO: need to add one line of code, see https://github.com/math-comp/hierarchy-builder/blob/0af7531ecacf591f97f663dc2fad5033c8ca61fe/HB/structure.elpi#L542-L544 *)
HB.structure Definition nattrans (M N : functor) := {f of isNatural M N f}.*)

Module Natural.
Record mixin_of (M N : functor) (f : M ~~> N) := Mixin { _ : naturality M N f }.
Structure type (M N : functor) := Pack
  { cpnt : M ~~> N ; mixin : mixin_of cpnt }.
Definition type_of (M N : functor) (phM : @phantom (UU0 -> UU0) M) (phN : @phantom (UU0 -> UU0) N) :=
  @type M N.
Module Exports.
Notation nattrans := type.
Coercion cpnt : type >-> Funclass.
Notation "f ~> g" := (@type_of _ _ (@Phantom (UU0 -> UU0) f) (@Phantom (UU0 -> UU0) g)) : monae_scope.
Identity Coercion type_of_type : type_of >-> type.
End Exports.
End Natural.
Export Natural.Exports.

Section natrans_lemmas.
Variables (M N : functor) (phi : M ~> N).
Lemma natural (A B : UU0) (h : A -> B) : (N # h) \o phi A = phi B \o (M # h).
Proof. by case: phi => ? []. Qed.
Lemma nattrans_ext (f g : M ~> N) :
  f = g <-> forall a, (f a = g a :> (_ -> _)).
Proof.
split => [ -> // |]; move: f g => [f Hf] [g Hg] /= fg.
have ? : f = g by exact: fun_ext_dep.
subst g; congr (Natural.Pack _); exact/proof_irr.
Qed.
End natrans_lemmas.

Require Import Logic.Eqdep.

Lemma natural_ext (F G G' : functor) (t : F ~> G) (t' : F ~> G') :
  forall (H : G = G'),
  forall (K : forall X (x : F X), Natural.cpnt t' x = eq_rect _ (fun m : functor => m X) (Natural.cpnt t x) _ H),
  t' = eq_rect _ (fun m : functor => F ~> m) t _ H.
Proof.
move : t t' => [t t1] [t' t'1] /= H; subst G' => H /=.
have ? : t = t'.
  apply fun_ext_dep => A; apply fun_ext_dep => x.
  by rewrite H -[in RHS]eq_rect_eq.
subst t'.
congr Natural.Pack; exact/proof_irr.
Qed.

Lemma natural_ext2 (F F' : functor) (t : F \O F ~> F) (t' : F' \O F' ~> F') :
  forall (K : F = F'),
  forall L : (forall X (x : (F' \O F') X),
    Natural.cpnt t' x = eq_rect _ (fun m : functor => m X)
      (Natural.cpnt t (eq_rect _ (fun m : functor => (m \O m) X) x _ (esym K)))
      _ K),
  t' = eq_rect _ (fun m => m \O m ~> m) t _ K.
Proof.
move: t t' => [t t1] [t' t'1] /= H L; subst F.
rewrite -[in RHS]eq_rect_eq /=.
have ? : t = t'.
  apply fun_ext_dep => A; apply fun_ext_dep => x.
  by rewrite L -[in RHS]eq_rect_eq.
subst t'.
congr Natural.Pack; exact/proof_irr.
Qed.

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

HB.mixin Record isMonad (M : UU0 -> UU0) of Functor M := {
  ret : idfun ~> M ;
  join : M \o M ~> M ;
  bind : forall (A B : UU0), M A -> (A -> M B) -> M B ;
  fmapE : forall (A B : UU0) (f : A -> B) (m : M A),
    ([the functor of M] # f) m = bind _ _ m (@ret _ \o f);
  bindE : forall (A B : UU0) (f : A -> M B) (m : M A),
    bind _ _ m f = join _ (([the functor of M] # f) m) ;
  joinretM : JoinLaws.left_unit ret join ;
  joinMret : JoinLaws.right_unit ret join ;
  joinA : JoinLaws.associativity join }.

HB.structure Definition Monad := {M of isMonad M &}.
Notation monad := Monad.type.

Module BindLaws.
Section bindlaws.
Variable M : functor.

Variable b : forall (A B : UU0), M A -> (A -> M B) -> M B.

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
  forall (A B : UU0) (g : A -> M B), f A >>= g = f B.

Definition right_zero (f : forall A, M A) :=
  forall (A B : UU0) (g : M B), g >>= (fun _ => f A) = f A.

Definition left_neutral (r : forall A : UU0, A -> M A) :=
  forall (A B : UU0) (a : A) (f : A -> M B), r _ a >>= f = f a.

Definition right_neutral (r : forall A : UU0, A -> M A) :=
  forall A (m : M A), m >>= r _ = m.

Definition left_id (r : forall A, M A) (op : forall B, M B -> M B -> M B) :=
  forall A (m : M A), op _ (r _) m = m.

Definition right_id (r : forall A, M A) (op : forall B, M B -> M B -> M B) :=
  forall A (m : M A), op _ m (r _) = m.

End bindlaws.
End BindLaws.

HB.factory Record Monad_of_ret_bind (M : UU0 -> UU0) of isFunctor M := {
  ret : idfun ~> M ;
  bind : forall (A B : UU0), M A -> (A -> M B) -> M B ;
  fmapE : forall (A B : UU0) (f : A -> B) (m : M A),
    ([the functor of M] # f) m = bind _ _ m (@ret _ \o f) ;
  bindretf : BindLaws.left_neutral bind ret ;
  bindmret : BindLaws.right_neutral bind ret ;
  bindA : BindLaws.associative bind
}.

Definition join_of_bind (F : functor)
  (b : forall (A B : UU0), F A -> (A -> F B) -> F B) := (fun A : UU0 => (b _ A)^~ id).

HB.builders Context M of Monad_of_ret_bind M.

(*Let Map (A B : UU0) (f : A -> B) (m : M A) := bind m (@ret B \o f).
Lemma Map_id : FunctorLaws.id Map.
Proof. by move=> A; rewrite boolp.funeqE => m; rewrite /Map bindmret. Qed.
Lemma Map_o : FunctorLaws.comp Map.
Proof.
move=> A B C g h; rewrite boolp.funeqE => m.
rewrite /Map compE bindA; congr bind.
by rewrite boolp.funeqE => a; rewrite bindretf.
Qed.
#[verbose]
HB.instance Definition _(*func_mixin*) :=
  isFunctor.Build (coucou M) Map_id Map_o.
(*Let M' := Functor.Pack (Functor.Class func_mixin).*)
*)
(*Let Map (A B : UU0) (f : A -> B) := M # f.
Lemma MapE (A B : UU0) (f : A -> B) m :
  Map f m = (M # f) m.
Proof.
by rewrite /Map.
Qed.
Lemma FMapE (A B : UU0) (f : A -> B) m :
  (M # f) m = bind m (ret B \o f).
Proof.
rewrite /Map.
Admitted.
(* by []. Qed.*)
*)

Notation M' := ([the functor of M]).

(*
Lemma naturality_ret : naturality FId M' ret.
Proof.
move=> A B h; rewrite FIdf boolp.funeqE => ?.
(*by rewrite compE /= /Map MapE /= bindretf.
Qed.*) Admitted.

Let ret' : idfun ~> M' := Natural.Pack (Natural.Mixin naturality_ret).
*)

Let bind_Map (A B C : UU0) (f : A -> B) (m : M A) (g : B -> M C) :
  bind ((M' # f) m) g = bind m (g \o f).
Proof.
rewrite fmapE.
by rewrite bindA; congr bind; rewrite boolp.funeqE => ?; rewrite bindretf.
Qed.

Lemma naturality_join : naturality (M' \O M') M' (join_of_bind bind).
Proof.
move=> A B h; rewrite boolp.funeqE => mma.
rewrite /=.
rewrite fmapE.
rewrite /join_of_bind.
rewrite bind_Map.
rewrite bindA.
congr bind.
rewrite boolp.funeqE => /= ma.
by rewrite compidf fmapE.
Qed.

Definition join : M' \O M' ~> M' := Natural.Pack (Natural.Mixin naturality_join).

(*Let bindE (A B : UU0) m (f : A -> M' B) : bind m f = join _ ((M' # f) m).
Proof. by rewrite /join /= /join_of_bind bind_Map. Qed.
*)

Lemma joinretM : JoinLaws.left_unit ret join.
Proof.
rewrite /join => A; rewrite boolp.funeqE => ma /=.
by rewrite /join_of_bind bindretf.
Qed.

Lemma joinMret : JoinLaws.right_unit ret join.
Proof.
rewrite /join => A; rewrite boolp.funeqE => ma /=.
by rewrite /join_of_bind bind_Map compidf bindmret.
Qed.

Lemma joinA : JoinLaws.associativity join.
Proof.
move=> A; rewrite boolp.funeqE => mmma.
by rewrite /join /= /join_of_bind bind_Map compidf bindA.
Qed.

Lemma bindE : forall (A B : UU0) (f : A -> M B) (m : M A),
  bind m f = (join) _ (([the functor of M] # f) m).
Proof.
move=> A B f m.
rewrite /join /join_of_bind /=.
by rewrite bind_Map compidf.
Qed.

HB.instance Definition _ := isMonad.Build M fmapE bindE joinretM joinMret joinA.
HB.end.

Notation Ret := (@ret _ _).
Notation Join := (@join _ _).

Section from_join_laws_to_bind_laws.
Variable F : functor.
Variable (ret : FId ~> F) (join : F \O F ~> F).

Hypothesis joinretM : JoinLaws.left_unit ret join.
Hypothesis joinMret : JoinLaws.right_unit ret join.
Hypothesis joinA : JoinLaws.associativity join.

Definition bind_of_join (A B : UU0) (m : F A) (f : A -> F B) : F B :=
  join _ ((F # f) m).

Lemma bindretf_derived : BindLaws.left_neutral bind_of_join ret.
Proof.
move=> A B a f; rewrite /bind_of_join -(compE (@join _)) -(compE _ (@ret _)) -compA.
by rewrite (natural ret) compA joinretM compidf.
Qed.

Lemma bindmret_derived : BindLaws.right_neutral bind_of_join ret.
Proof. by move=> A m; rewrite /bind_of_join -(compE (@join _)) joinMret. Qed.

Lemma bindA_derived : BindLaws.associative bind_of_join.
Proof.
move=> A B C m f g; rewrite /bind_of_join.
rewrite [LHS](_ : _ = ((@join _ \o (F # g \o @join _) \o F # f) m)) //.
rewrite (natural join) (compA (@join C)) -joinA -(compE (@join _)).
transitivity ((@join _ \o F # (@join _ \o (F # g \o f))) m) => //.
by rewrite -2!compA functor_o FCompE -[in LHS](@functor_o F).
Qed.

End from_join_laws_to_bind_laws.

Section monad_lemmas.
Variable M : monad.
Local Notation M' := (Monad.sort M).
(*Definition Bind A B (x : M A) (f : A -> M B) : M B := @bind_of_join M (@join M) A B x f.
Arguments Bind {A B} : simpl never.*)
Local Notation "m >>= f" := (bind _ _ m f).
(*Lemma bindE (A B : UU0) : forall x (f : A -> M B), x >>= f = Join ((M' # f) x).
Proof. by []. Qed.*)
Lemma bindretf : BindLaws.left_neutral (@bind M) (@ret _).
Proof.
move: (@bindretf_derived M ret join joinretM).
rewrite (_ : bind_of_join _ = bind) //.
apply fun_ext_dep => A.
apply fun_ext_dep => B.
apply fun_ext_dep => m.
apply fun_ext_dep => f.
by rewrite bindE.
Qed.
Lemma bindmret : BindLaws.right_neutral (@bind M) (@ret _).
Proof.
move: (@bindmret_derived M ret join joinMret).
rewrite (_ : bind_of_join _ = bind) //.
apply fun_ext_dep => A.
apply fun_ext_dep => B.
apply fun_ext_dep => m.
apply fun_ext_dep => f.
by rewrite bindE.
Qed.
Lemma bindA : BindLaws.associative (@bind M).
Proof.
move: (@bindA_derived M join joinA).
rewrite (_ : bind_of_join _ = bind) //.
apply fun_ext_dep => A.
apply fun_ext_dep => B.
apply fun_ext_dep => m.
apply fun_ext_dep => f.
by rewrite bindE.
Qed.

(*Lemma bindE' (A B : Type) : Bind = fun x (f : A -> M B) => Join ((M # f) x).
Proof. by []. Qed.*)
(*Lemma joinretM' A C (f:C->_) : @Join M A \o (@Ret M (M A) \o f) = f.
Proof. by rewrite compA joinretM. Qed.*)
(*Lemma joinMret' A C (f:C->_) : @Join M A \o (M # @Ret M A \o f) = f.
Proof. by rewrite compA joinMret. Qed.*)
(*Lemma joinA' A C (f:C->_) : @Join M A \o (M # @Join M A \o f) = @Join M A \o (@Join M (M A) \o f).
Proof. by rewrite compA joinA. Qed.*)
End monad_lemmas.
Arguments bind {s A B} : simpl never.

Notation "'do' x <- m ; e" := (bind m (fun x => e)) : do_notation.
Notation "'do' x : T <- m ; e" := (bind m (fun x : T => e)) (only parsing) : do_notation.
Delimit Scope do_notation with Do.
Notation "m >>= f" := (bind m f) : monae_scope.
Notation "m >> f" := (bind m (fun _ => f)) : monae_scope.

Fixpoint sequence (M : monad) A (s : seq (M A)) : M (seq A) :=
  (if s isn't h :: t then Ret [::] else
  do v <- h; do vs <- sequence t; Ret (v :: vs))%Do.

Lemma sequence_nil (M : monad) (A : UU0) : sequence [::] = Ret [::] :> M (seq A).
Proof. by []. Qed.

Lemma sequence_cons (M : monad) A h (t : seq (M A)) :
  (sequence (h :: t) = do x <- h ; do vs <- sequence t ; Ret (x :: vs))%Do.
Proof. by []. Qed.

Definition skip M := @ret M _ tt.
Arguments skip {M} : simpl never.

Ltac bind_ext :=
  let congr_ext m := ltac:(congr (bind m); rewrite boolp.funeqE) in
  match goal with
    | |- @bind _ _ _ ?m ?f1 = @bind _ _ _ ?m ?f2 =>
      congr_ext m
    | |- @bind _ _ _ ?m1 ?f1 = @bind _ _ _ ?m2 ?f2 =>
      first[ simpl m1; congr_ext m1 | simpl m2; congr_ext m2 ]
  end.

Section bindskip.
Lemma bindmskip (M : monad) (m : M unit) : m >> skip = m.
Proof. rewrite -[RHS]bindmret; bind_ext; by case. Qed.

Lemma bindskipf (M : monad) A (m : M A) : skip >> m = m.
Proof. exact: bindretf. Qed.
End bindskip.

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

Lemma eq_bind (M : monad) (A B : UU0) (m : M A) (f1 f2 : A -> M B) :
  f1 =1 f2 -> m >>= f1 = m >>= f2.
Proof. by move=> f12; congr bind; rewrite boolp.funeqE. Qed.

Section fmap_and_join.
Variable M : monad.
Local Open Scope mprog.

Lemma fmapE' (A B : UU0) (f : A -> B) (m : M _) : fmap f m = m >>= (Ret \o f).
Proof.
by rewrite fmapE.
(*by rewrite bindE [in RHS]functor_o [in RHS]compE -[in RHS](compE Join) joinMret. TODO *)
Qed.

Lemma bind_fmap (A B C : UU0) (f : A -> B) (m : M A) (g : B -> M C) :
  fmap f m >>= g = m >>= (g \o f).
Proof. by rewrite fmapE bindA; under eq_bind do rewrite bindretf. Qed.

Lemma fmap_if (A B : UU0) (f : A -> B) b (m : M A) a :
  fmap f (if b then m else Ret a) = if b then fmap f m else Ret (f a).
Proof. case: ifPn => Hb //; by rewrite fmapE bindretf. Qed.

Lemma fmap_bind (A B C : UU0) (f : A -> B) m (g : C -> M A) :
  fmap f (m >>= g) = m >>= (f (o) g).
Proof.
rewrite fcomp_def fmapE bindA; bind_ext => c; by rewrite compE -/(fmap _ _) fmapE.
Qed.

Lemma skip_fmap (A B : UU0) (f : A -> B) (mb : M B) ma :
  mb >> (fmap f ma) = fmap f (mb >> ma).
Proof. by rewrite fmap_bind fcomp_def. Qed.

(*Lemma rev_map A B (f : A -> B) : rev \o map f = map f \o rev.
Proof.
apply functional_extensionality.
by elim=> // h t /= IH; rewrite !rev_cons IH map_rcons.
Qed.*)

Lemma joinE A (pp : M (M A)) : Join pp = pp >>= id.
Proof. rewrite bindE; congr Join; by rewrite functor_id. Qed.

Lemma join_fmap (A B : UU0) (f : A -> M B) (m : M A) : Join (fmap f m) = m >>= f.
Proof. by rewrite bindE. Qed.

End fmap_and_join.

Section kleisli.
Variable M : monad.

Definition kleisli (A B C : UU0) (m : B -> M C) (n : A -> M B) : A -> M C :=
  Join \o (M # m) \o n.
Local Notation "m <=< n" := (kleisli m n).
Local Notation "m >=> n" := (kleisli n m).

Lemma kleisliE (A B C : UU0) (g : B -> M C) (f : A -> M B) :
  (f >=> g) = Join \o (M # g) \o f.
Proof. by []. Qed.

Lemma bind_kleisli (A B C : UU0) m (f : A -> M B) (g : B -> M C) :
  m >>= (f >=> g) = (m >>= f) >>= g.
Proof. by rewrite bindA; bind_ext => a; rewrite /kleisli !compE join_fmap. Qed.

Lemma ret_kleisli (A B : UU0) (k : A -> M B) : Ret >=> k = k.
Proof. by rewrite /kleisli -compA (natural ret) FIdf compA joinretM. Qed.

Local Open Scope mprog.
Lemma fcomp_kleisli (A B C D : UU0) (f : A -> B) (g : C -> M A) (h : D -> M C) :
  f (o) (g <=< h) = (f (o) g) <=< h.
Proof.
rewrite /kleisli 2!fcomp_def 2!(compA (fmap f)) natural [in RHS]functor_o.
by rewrite -compA.
Qed.

Lemma kleisli_fcomp (A B C : UU0) (f : A -> M B) (g : B -> A) (h : C -> M B) :
  ((f \o g) <=< h) = f <=< (g (o) h).
Proof. by rewrite /kleisli fcomp_def functor_o 2!compA. Qed.
Local Close Scope mprog.

End kleisli.
Notation "m <=< n" := (kleisli m n) : monae_scope.
Notation "m >=> n" := (kleisli n m) : monae_scope.

HB.mixin Record isMonadFail (M : UU0 -> UU0) of Monad M := {
  fail : forall A : UU0, M A;
  (* exceptions are left-zeros of sequential composition *)
  bindfailf : BindLaws.left_zero (@bind [the monad of M]) fail (* fail A >>= f = fail B *)
}.

HB.structure Definition MonadFail := {M of isMonadFail M & }.
Notation failMonad := MonadFail.type.

Arguments bindfailf [_].

(*Definition Fail (M : failMonad) := @fail M.*)
Arguments fail {_} {_}.

Section guard_assert.
Variable M : failMonad.

Definition guard (b : bool) : M unit := locked (if b then skip else fail).

Lemma guardPn (b : bool) : if_spec b skip fail (~~ b) b (guard b).
Proof. by rewrite /guard; unlock; case: ifPn => ?; constructor. Qed.

Lemma guardT : guard true = skip. Proof. by rewrite /guard; unlock. Qed.

Lemma guardF : guard false = fail. Proof. by rewrite /guard; unlock. Qed.

(* guard distributes over conjunction *)
Lemma guard_and a b : guard (a && b) = guard a >> guard b.
Proof.
move: a b => -[|] b /=; by [rewrite guardT bindskipf | rewrite guardF bindfailf].
Qed.

Definition assert {A : UU0} (p : pred A) (a : A) : M A :=
  locked (guard (p a) >> Ret a).

Lemma assertE {A : UU0} (p : pred A) (a : A) : assert p a = guard (p a) >> Ret a.
Proof. by rewrite /assert; unlock. Qed.

Lemma assertT {A : UU0} (a : A) : assert xpredT a = Ret a.
Proof. by rewrite assertE guardT bindskipf. Qed.

Lemma assertF {A : UU0} (a : A) : assert xpred0 a = fail.
Proof. by rewrite assertE guardF bindfailf. Qed.

Lemma assertPn {A : UU0} (p : pred A) (a : A) :
  if_spec (p a) (Ret a) fail (~~ (p a)) (p a) (assert p a).
Proof.
rewrite assertE; case: guardPn => pa;
  by [rewrite bindskipf; constructor | rewrite bindfailf; constructor].
Qed.

Definition bassert {A : UU0} (p : pred A) (m : M A) : M A := m >>= assert p.

(* follows from guards commuting with anything *)
Lemma commutativity_of_assertions A q :
  Join \o (M # (bassert q)) = bassert q \o Join :> (_ -> M A).
Proof.
by rewrite boolp.funeqE => x; rewrite !compE join_fmap /bassert joinE bindA.
Qed.

(* guards commute with anything *)
Lemma guardsC (HM : BindLaws.right_zero (@bind M) (@fail _)) b B (m : M B) :
  guard b >> m = m >>= assert (fun=> b).
Proof.
case: guardPn => Hb.
- rewrite bindskipf.
  under eq_bind do rewrite assertT.
  by rewrite bindmret.
- under [RHS]eq_bind do rewrite assertF.
  by rewrite bindfailf HM.
Qed.

End guard_assert.
Arguments assert {M} {A}.
Arguments guard {M}.

HB.mixin Record isMonadAlt (M : UU0 -> UU0) of Monad M := {
  alt : forall T : UU0, M T -> M T -> M T ;
  altA : forall T : UU0, associative (@alt T) ;
  (* composition distributes leftwards over choice *)
  alt_bindDl : BindLaws.left_distributive (@bind [the monad of M]) alt
(* in general, composition does not distribute rightwards over choice *)
(* NB: no bindDr to accommodate both angelic and demonic interpretations of nondeterminism *)
}.

HB.structure Definition MonadAlt := {M of isMonadAlt M & }.

Notation "a [~] b" := (@alt _ _ a b). (* infix notation *)

Notation altMonad := MonadAlt.type.

HB.mixin Record isMonadAltCI (M : UU0 -> UU0) of MonadAlt M := {
  altmm : forall A : UU0, idempotent (@alt [the altMonad of M] A) ;
  altC : forall A : UU0, commutative (@alt [the altMonad of M] A)
}.

HB.structure Definition MonadAltCI := {M of isMonadAltCI M & }.
Notation altCIMonad := MonadAltCI.type.

Arguments altC {_} {_}.
Arguments altmm {_} {_}.

Section altci_lemmas.
Variable (M : altCIMonad).
Lemma altCA A : @left_commutative (M A) (M A) (fun x y => x [~] y).
Proof. by move=> x y z; rewrite altA altC altA altC (altC x). Qed.
Lemma altAC A : @right_commutative (M A) (M A) (fun x y => x [~] y).
Proof. move=> x y z; by rewrite altC altA (altC x). Qed.
Lemma altACA A : @interchange (M A) (fun x y => x [~] y) (fun x y => x [~] y).
Proof. move=> x y z t; rewrite !altA; congr (_ [~] _); by rewrite altAC. Qed.
End altci_lemmas.

HB.mixin Record isMonadNondet (M : UU0 -> UU0) of MonadFail M & MonadAlt M := {
  altfailm : @BindLaws.left_id [the functor of M] (@fail [the failMonad of M]) (@alt [the altMonad of M]);
  altmfail : @BindLaws.right_id [the functor of M] (@fail [the failMonad of M]) (@alt [the altMonad of M])
}.

HB.structure Definition MonadNondet := {M of isMonadNondet M & MonadFail M & MonadAlt M}.
Notation nondetMonad := MonadNondet.type.

HB.structure Definition MonadCINondet := {M of MonadAltCI M & MonadNondet M}.
Notation nondetCIMonad := MonadCINondet.type.

Section nondet_big.
Variables (M : nondetMonad) (A : UU0).
Canonical alt_monoid :=
  Monoid.Law (@altA M A) (@altfailm _ _) (@altmfail _ _).

Lemma test_bigop n : \big[(@alt _ _)/fail]_(i < n) (fail : M A) = fail.
Proof.
elim: n => [|n IH]; first by rewrite big_ord0.
by rewrite big_ord_recr /= IH altmfail.
Qed.

End nondet_big.

HB.mixin Record isMonadFailR0 (M : UU0 -> UU0) of MonadFail M := {
  bindmfail : BindLaws.right_zero (@bind [the monad of M]) (@fail _)
}.

HB.structure Definition MonadFailR0 := {M of isMonadFailR0 M & }.
Notation failR0Monad := MonadFailR0.type.

HB.mixin Record isMonadPrePlus (M : UU0 -> UU0) of MonadNondet M & MonadFailR0 M := {
  alt_bindDr : BindLaws.right_distributive (@bind [the monad of M]) (@alt _)
}.

HB.structure Definition MonadPrePlus := {M of isMonadPrePlus M & }.
Notation prePlusMonad := MonadPrePlus.type.

HB.structure Definition MonadPlus := {M of MonadCINondet M & MonadPrePlus M}.
Notation plusMonad := MonadPlus.type.

HB.mixin Record isMonadExcept (M : UU0 -> UU0) of MonadFail M := {
  catch : forall A, M A -> M A -> M A ;
  (* monoid *)
  catchmfail : forall A, right_id fail (@catch A) ;
  catchfailm : forall A, left_id fail (@catch A) ;
  catchA : forall A, associative (@catch A) ;
  (* unexceptional bodies need no handler *)
  catchret : forall A x, @left_zero (M A) (M A) (Ret x) (@catch A)
  (* NB: left-zero of sequential composition inherited from failMonad *)
}.

HB.structure Definition MonadExcept := {M of isMonadExcept M & }.
Notation exceptMonad := MonadExcept.type.

(*Definition Catch (M : exceptMonad) := @catch M.*)
Arguments catch {_} {_}.

HB.mixin Record isMonadContinuation (M : UU0 -> UU0) of Monad M := {
(* NB: interface is wip *)
   callcc : forall A B : UU0, ((A -> M B) -> M A) -> M A;
   callcc0 : forall (A B : UU0) (g : (A -> M B) -> M A) (k : B -> M B),
     @callcc _ _ (fun f => g (fun x => f x >>= k)) = @callcc _ _ g; (* see Sect. 7.2 of [Schrijvers, 19] *)
   callcc1 : forall (A B : UU0) (m : M B), @callcc _ _ (fun _ : B -> M A => m) = m ; (* see Sect. 3.3 of [Wadler, 94] *)
   callcc2 : forall (A B C : UU0) (m : M A) x (k : A -> B -> M C),
     @callcc _ _ (fun f : _ -> M _ => m >>= (fun a => f x >>= (fun b => k a b))) =
     @callcc _ _ (fun f : _ -> M _ => m >> f x) ;
   callcc3 : forall (A B : UU0) (m : M A) b,
     @callcc _ _ (fun f : B -> M B => m >> f b) =
     @callcc _ _ (fun _ : B -> M B => m >> Ret b)
}.

HB.structure Definition MonadContinuation := {M of isMonadContinuation M & }.
Notation contMonad := MonadContinuation.type.
(*Definition Callcc (M : contMonad) := @callcc M.*)
Arguments callcc {_} {_} {_}.

HB.mixin Record isMonadShiftReset (U : UU0) (M : UU0 -> UU0) of MonadContinuation M := {
  shift : forall A : UU0, ((A -> M U) -> M U) -> M A ;
  reset : M U -> M U ;
  shiftreset0 : forall (A : UU0) (m : M A), @shift _ (fun k => m >>= k) = m ;
    (* see Sect. 3.3 of [Wadler, 94] *)
  shiftreset1 : forall (A B : UU0) (h : (A -> M B) -> M A),
    callcc h = @shift _ (fun k' => h (fun x => @shift _ (fun k'' => k' x)) >>= k') ;
    (* see Sect. 3.3 of [Wadler, 94] *)
  shiftreset2 : forall (A : UU0) (c : A) (c': U) (k : A -> U -> _),
    (reset (do x <- Ret c; do y <- @shift _ (fun _ => Ret c'); k x y) = Ret c >> Ret c')%Do ;
  shiftreset3 : forall (c c' : U) (k : U -> U -> _),
    (reset (do x <- Ret c; do y <- @shift _ (fun f => do v <- f c'; f v); Ret (k x y)) =
     reset (do x <- Ret c; do y <- @shift _ (fun f => f c'); Ret (k x (k x y))))%Do ;
  shiftreset4 : forall (c : U) k,
    (reset (do y <- @shift _ (@^~ c); Ret (k y)) = Ret (k c))%Do
}.

HB.structure Definition MonadShiftReset U := {M of isMonadShiftReset U M & }.
Notation shiftresetMonad := MonadShiftReset.type.
(*Definition Shift U (M : shiftresetMonad U) := @shift U M.*)
Arguments shift {_} {_} {_}.
(*Definition Reset U (M : shiftresetMonad U) := @reset U M.
Arguments Reset {_} {_}.*)

(* NB: wip, no model *)
(* Sect. 7.2 of [Tom Schrijvers & al., Monad Transformers and Modular
Algebraic Eﬀects: What Binds Them Together, Haskell 2019] *)
HB.mixin Record isMonadJump (ref : UU0 -> UU0) (M : UU0 -> UU0) of Monad M := {
   jump : forall A B : UU0, ref A -> A -> M B;
   sub : forall A B : UU0, (ref A -> M B) -> (A -> M B) -> M B;
   jump0 : forall (A B : UU0) k x, @sub _ _ (fun r => @jump A B r x) k = k x ;
   jump1 : forall (A B : UU0) p k, @sub A B (fun _ => p) k = p;
   jump2 : forall (A B : UU0) p r', @sub _ _ p (@jump A B r') = p r';
   jump3 : forall (A B : UU0) (p : ref A -> ref B -> M B) (k1 : A -> M B) k2,
     @sub _ _ (fun r1 : ref A => @sub _ _ (fun r2 => p r1 r2) (k2 r1)) k1 =
     @sub _ _ (fun r2 : ref B => @sub _ _ (fun r1 => p r1 r2) k1) (fun x => @sub _ _ (k2^~ x) k1); (*NB: differs from [Schrijvers et al. 19]*)
   jump4 : forall (A B : UU0) r x k, (@jump A B r x) >>= k = @jump A B r x;
   jump5 : forall (A B : UU0) p q k, @sub A B p q >>= k = @sub A B (p >=> k) (q >=> k)
}.
HB.structure Definition MonadJump ref := {M of isMonadJump ref M & }.
Notation jumpMonad := MonadJump.type.
Definition Jump ref (M : jumpMonad ref) := @jump ref M.
Arguments Jump {_} {_} {_} {_}.
Definition Sub ref (M : jumpMonad ref) := @sub ref M.
Arguments sub {_} {_} {_} {_}.

HB.mixin Record isMonadState (S : UU0) (M : UU0 -> UU0) of Monad M := {
  get : M S ;
  put : S -> M unit ;
  putput : forall s s', put s >> put s' = put s' ;
  putget : forall s, put s >> get = put s >> Ret s ;
  getputskip : get >>= put = skip ;
  getget : forall (A : UU0) (k : S -> S -> M A),
    get >>= (fun s => get >>= k s) = get >>= fun s => k s s }.

HB.structure Definition MonadState (S : UU0) := { M of isMonadState S M & }.
Notation stateMonad := MonadState.type.

(*NB: explicit join newly added*)
HB.structure Definition MonadFailState (S : UU0) :=
  { M of isMonadFail M & isMonadState S M & isMonad M & isFunctor M }.
Notation failStateMonad := MonadFailState.type.

(*NB: explicit join newly added*)
HB.structure Definition MonadFailR0State (S : UU0) :=
  { M of isMonadFailR0 M & isMonadState S M & isMonadFail M & isMonad M & isFunctor M }.
Notation failR0StateMonad := MonadFailR0State.type.

HB.structure Definition MonadNondetState (S : UU0) :=
  { M of MonadPrePlus M & MonadState S M }.
Notation nondetStateMonad := MonadNondetState.type.

HB.mixin Record isMonadStateRun (S : UU0) (N : monad)
   (M : UU0 -> UU0) of MonadState S M := {
  runStateT : forall A : UU0, M A -> S -> N (A * S)%type ;
  runStateTret : forall (A : UU0) (a : A) (s : S), @runStateT _ (Ret a) s = Ret (a, s) ;
  runStateTbind : forall (A B : UU0) (m : M A) (f : A -> M B) (s : S),
    @runStateT _ (m >>= f) s = @runStateT _ m s >>= fun x => @runStateT _ (f x.1) x.2 ;
  runStateTget : forall s : S, @runStateT _ get s = Ret (s, s) ;
  runStateTput : forall s' s : S, @runStateT _ (put s') s = Ret (tt, s') }.

HB.structure Definition MonadStateRun (S : UU0) (N : monad) :=
  {M of isMonadStateRun S N M & }.
Notation stateRunMonad := MonadStateRun.type.
Arguments runStateT {_} {_} {_} {_}.

HB.mixin Record isMonadExceptStateRun (S : UU0) (N : exceptMonad)
   (M : UU0 -> UU0) of MonadStateRun S N M & MonadExcept M
  := Mixin {
  runStateTfail : forall (A : UU0) (s : S),
    runStateT (@fail [the exceptMonad of M] A) s = @fail N _ ;
  runStateTcatch : forall (A : UU0) (s : S) (m1 m2 : M A),
    runStateT (@catch [the exceptMonad of M] _ m1 m2) s = @catch N _ (runStateT m1 s) (runStateT m2 s) }.

HB.structure Definition MonadExceptStateRun (S : UU0) (N : exceptMonad) :=
  {M of isMonadExceptStateRun S N M & }.
Notation exceptStateRunMonad := MonadExceptStateRun.type.

HB.mixin Record isMonadReify (S : UU0) (M : UU0 -> UU0) of Monad M := {
  reify : forall A : UU0, M A -> S -> option (A * S)%type ;
  reifyret : forall (A : UU0) (a : A) s, @reify _ (Ret a) s = Some (a, s) ;
  reifybind : forall (A B : UU0) (m : M A) (f : A -> M B) s,
      @reify _ (m >>= f) s = match @reify _ m s with
                             | Some a's' => @reify _ (f a's'.1) a's'.2
                             | None => None
                             end
}.

HB.structure Definition MonadReify (S : UU0) := {M of isMonadReify S M & }.
Notation reifyMonad := MonadReify.type.
Arguments reify {_} {_} {_}.

HB.mixin Record isMonadStateReify (S : UU0) (M : UU0 -> UU0) of MonadReify S M & MonadState S M := {
  reifyget : forall s, reify (@get _ [the stateMonad S of M]) s = Some (s, s) ;
  reifyput : forall s s', reify (@put _ [the stateMonad S of M] s') s = Some (tt, s')
}.

HB.structure Definition MonadStateReify (S : UU0) := {M of isMonadStateReify S M &}.
Notation stateReifyMonad := MonadStateReify.type.

HB.mixin Record isMonadFailReify (S : UU0) (M : UU0 -> UU0) of MonadReify S M & MonadFail M := {
  reifyfail : forall S' (s : S), reify (@fail [the failMonad of M] S') s = None
}.

HB.structure Definition MonadFailReify (S : UU0) := {M of isMonadFailReify S M & }.
Notation failReifyMonad := MonadFailReify.type.

HB.structure Definition MonadFailFailR0Reify (S : UU0) := {M of MonadFailReify S M & MonadFailR0 M}.
Notation failFailR0ReifyMonad := MonadFailFailR0Reify.type.

HB.structure Definition MonadFailStateReify (S : UU0) := {M of MonadStateReify S M & MonadFailFailR0Reify S M}.
Notation failStateReifyMonad := MonadFailStateReify.type.


(*
Module MonadFailStateReify.
Record class_of (S : UU0) (M : UU0 -> UU0) := Class {
  base : MonadStateReify.class_of S M ;
  mixin_fail : MonadFail.mixin_of (Monad.Pack (MonadReify.base (MonadStateReify.base base))) ;
  mixin_failReify : @MonadFailReify.mixin_of S (MonadReify.Pack (MonadStateReify.base base)) (@Fail (MonadFail.Pack (MonadFail.Class mixin_fail))) ;
  mixin_failR0 : @MonadFailR0.mixin_of (MonadFail.Pack (MonadFail.Class mixin_fail)) ;
 }.
Structure type (S : UU0) := Pack { acto : UU0 -> UU0 ; class : class_of S acto }.
Definition failStateMonadType (S : UU0) (M : type S) := MonadStateReify.Pack (base (class M)).
Definition fail_of_failStateReify (S : UU0) (M : type S) :=
  MonadFail.Pack (MonadFail.Class (mixin_fail (class M))).
Definition failReify_of_failStateReify (S : UU0) (M : type S) :=
  MonadFailReify.Pack (MonadFailReify.Class (mixin_failReify (class M))).
Definition failR0_of_failStateReify (S : UU0) (M : type S) :=
  MonadFailR0.Pack (MonadFailR0.Class (mixin_failR0 (class M))).
Definition failFailR0_of_failStateReify (S : UU0) (M : type S) :=
  MonadFailFailR0Reify.Pack (@MonadFailFailR0Reify.Class _ _ (MonadFailReify.class (failReify_of_failStateReify M)) (mixin_failR0 (class M))).
Module Exports.
Notation failStateReifyMonad := type.
Coercion failStateMonadType : failStateReifyMonad >-> stateReifyMonad.
Canonical failStateMonadType.
Coercion fail_of_failStateReify : failStateReifyMonad >-> failMonad.
Canonical fail_of_failStateReify.
Coercion failReify_of_failStateReify : failStateReifyMonad >-> failReifyMonad.
Canonical failReify_of_failStateReify.
Coercion failR0_of_failStateReify : failStateReifyMonad >-> failR0Monad.
Canonical failR0_of_failStateReify.
Coercion failFailR0_of_failStateReify : failStateReifyMonad >-> failFailR0ReifyMonad.
Canonical failFailR0_of_failStateReify.
End Exports.
End MonadFailStateReify.
Export MonadFailStateReify.Exports.*)

(* NB: this is experimental, may disappear, see rather foreach in
monad_transformer because it is more general *)
HB.mixin Record isMonadStateLoop (S : UU0) (M : UU0 -> UU0) of MonadState S M := {
  foreach : nat -> nat -> (nat -> M unit) -> M unit ;
  loop0 : forall m body, foreach m m body = Ret tt ;
  loop1 : forall m n body, foreach (m.+1 + n) m body =
     (body (m + n)) >> foreach (m + n) m body :> M unit }.

HB.structure Definition MonadStateLoop (S : UU0) := {M of isMonadStateLoop S M & }.
Notation loopStateMonad := MonadStateLoop.type.

HB.mixin Record isMonadArray (S : UU0) (I : eqType) (M : UU0 -> UU0) of Monad M := {
  aget : I -> M S ;
  aput : I -> S -> M unit ;
  aputput : forall i s s', aput i s >> aput i s' = aput i s' ;
  aputget : forall i s (A : UU0) (k : S -> M A), aput i s >> aget i >>= k =
      aput i s >> k s ;
  agetpustskip : forall i, aget i >>= aput i = skip ;
  agetget : forall i (A : UU0) (k : S -> S -> M A),
    aget i >>= (fun s => aget i >>= k s) = aget i >>= fun s => k s s ;
  agetC : forall i j (A : UU0) (k : S -> S -> M A),
    aget i >>= (fun u => aget j >>= (fun v => k u v)) =
    aget j >>= (fun v => aget i >>= (fun u => k u v)) ;
  aputC : forall i j u v, (i != j) \/ (u = v) ->
    aput i u >> aput j v = aput j v >> aput i u ;
  aputgetC : forall i j u (A : UU0) (k : S -> M A), i != j ->
    aput i u >> aget j >>= k =
    aget j >>= (fun v => aput i u >> k v)
}.

HB.structure Definition MonadArray (S : UU0) (I : eqType) :=
  { M of isMonadArray S I M & isMonad M & isFunctor M }.
Notation arrayMonad := MonadArray.type.

HB.mixin Record isMonadTrace (T : UU0) (M : UU0 -> UU0) of Monad M := {
  mark : T -> M unit
}.

HB.structure Definition MonadTrace (T : UU0) := {M of isMonadTrace T M & }.
Notation traceMonad := MonadTrace.type.

HB.mixin Record isMonadTraceReify (T : UU0) (M : UU0 -> UU0) of
    MonadReify (seq T) M & MonadTrace T M := {
  reifytmark : forall t l,
    reify (@mark _ [the traceMonad T of M] t) l = Some (tt, rcons l t)
}.

HB.mixin Record isMonadStateTrace (S T : UU0) (M : UU0 -> UU0) of Monad M := {
  st_get : M S ;
  st_put : S -> M unit ;
  st_mark : T -> M unit ;
  st_putput : forall s s', st_put s >> st_put s' = st_put s' ;
  st_putget : forall s, st_put s >> st_get = st_put s >> Ret s ;
  st_getputskip : st_get >>= st_put = skip ;
  st_getget : forall (A : UU0) (k : S -> S -> M A),
      st_get >>= (fun s => st_get >>= k s) = st_get >>= fun s => k s s ;
  st_putmark : forall s e, st_put s >> st_mark e = st_mark e >> st_put s ;
  st_getmark : forall e (k : _ -> M S), st_get >>= (fun v => st_mark e >> k v) =
                         st_mark e >> st_get >>= k
}.

HB.structure Definition MonadStateTrace (S T : UU0) :=
  { M of isMonadStateTrace S T M & isMonad M & isFunctor M }.
Notation stateTraceMonad := MonadStateTrace.type.

HB.mixin Record isMonadStateTraceReify (S T : UU0) (M : UU0 -> UU0)
    of MonadReify (S * seq T)%type M & MonadStateTrace S T M := {
  reifystget : forall s l,
    reify (@st_get _ _ [the stateTraceMonad S T of M]) (s, l) = Some (s, (s, l)) ;
  reifystput : forall s l s',
    reify (@st_put _ _ [the stateTraceMonad S T of M] s') (s, l) = Some (tt, (s', l)) ;
  reifystmark : forall t s l,
    reify (@st_mark _ _ [the stateTraceMonad S T of M] t) (s, l) = Some (tt, (s, rcons l t))
}.
HB.structure Definition MonadStateTraceReify (S T : UU0) :=
  { M of isMonadStateTraceReify S T M & isFunctor M & isMonad M &
         isMonadReify S M & isMonadStateTrace S T M }.
Notation stateTraceReifyMonad := MonadStateTraceReify.type.

Local Open Scope reals_ext_scope.
HB.mixin Record isMonadProb (M : UU0 -> UU0) of Monad M := {
  choice : forall (p : prob) (T : UU0), M T -> M T -> M T ;
  (* identity axioms *)
  choice0 : forall (T : UU0) (a b : M T), choice 0%:pr _ a b = b ;
  choice1 : forall (T : UU0) (a b : M T), choice 1%:pr _ a b = a ;
  (* skewed commutativity *)
  choiceC : forall (T : UU0) p (a b : M T), choice p _ a b = choice (p.~ %:pr) _ b a ;
  choicemm : forall (T : UU0) p, idempotent (@choice p T) ;
  (* quasi associativity *)
  choiceA : forall (T : UU0) (p q r s : prob) (a b c : M T),
    (p = r * s :> R /\ s.~ = p.~ * q.~)%R ->
    (*NB: needed to preserve the notation in the resulting choiceA lemma, report? *)
    let bc := choice q _ b c in
    let ab := choice r _ a b in
    choice p _ a bc = choice s _ ab c;
  (* composition distributes leftwards over [probabilistic] choice *)
  prob_bindDl : forall p, BindLaws.left_distributive (@bind [the monad of M]) (choice p)
}.

HB.structure Definition MonadProb := {M of isMonadProb M & }.
Notation "a <| p |> b" := (choice p _ a b).
Notation probMonad := MonadProb.type.
Arguments choiceA {_} {_} _ _ _ _ {_} {_} {_}.
Arguments choiceC {_} {_} _ _ _.
Arguments choicemm {_} {_} _.

HB.mixin Record isMonadProbDr (M : UU0 -> UU0) of MonadProb M := {
  (* composition distributes rightwards over [probabilistic] choice *)
  (* WARNING: this should not be asserted as an axiom in conjunction with
     distributivity of <||> over [] *)
  prob_bindDr : forall p, BindLaws.right_distributive (@bind [the monad of M]) (choice p) (* NB: not used *)
}.

HB.structure Definition MonadProbDr := {M of isMonadProbDr M & }.
Notation probDrMonad := MonadProbDr.type.

HB.mixin Record isMonadAltProb (M : UU0 -> UU0) of MonadAltCI M & MonadProb M := {
  choiceDr : forall T p,
    right_distributive (@choice [the probMonad of M] p T) (fun a b => a [~] b)
}.
HB.structure Definition MonadAltProb :=
  { M of isMonadAltProb M & isFunctor M & isMonad M & isMonadAlt M &
         isMonadAltCI M & isMonadProb M }.
Notation altProbMonad := MonadAltProb.type.

Section altprob_lemmas.
Local Open Scope proba_monad_scope.
Variable (M : altProbMonad).
Lemma choiceDl A p :
  left_distributive (fun x y : M A => x <| p |> y) (fun x y => x [~] y).
Proof. by move=> x y z; rewrite !(choiceC p) choiceDr. Qed.
End altprob_lemmas.

HB.mixin Record isMonadExceptProb (M : UU0 -> UU0) of MonadExcept M & MonadProb M := {
  catchDl : forall (A : UU0) w,
    left_distributive (@catch [the exceptMonad of M] A) (fun x y => choice w A x y)
}.

HB.structure Definition MonadExceptProb :=
 { M of isMonadExceptProb M & isFunctor M & isMonad M & isMonadFail M &
        isMonadExcept M & isMonadProb M }.
Notation exceptProbMonad := MonadExceptProb.type.

HB.mixin Record isMonadFresh (S : eqType) (M : UU0 -> UU0) of Monad M := {
  fresh : M S
}.

HB.structure Definition MonadFresh (S : eqType) := {M of isMonadFresh S M & }.
Notation freshMonad:= MonadFresh.type.

Module segment_closed.
Record t A := mk {
  p : pred (seq A) ;
  H : forall a b, p (a ++ b) -> p a /\ p b }.
End segment_closed.
Definition segment_closed_p A := @segment_closed.p A.
Coercion segment_closed_p : segment_closed.t >-> pred.

Definition symbols S (M : freshMonad S) := fun n => sequence (nseq n (@fresh _ M)).
Arguments symbols {_} {_}.

HB.mixin Record isMonadFailFresh (S : eqType) (M : UU0 -> UU0)
    of MonadFresh S M & MonadFail M := Mixin {
(*  symbols := fun n => sequence (nseq n fresh);*)
  (* generated symbols are indeed fresh (specification of fresh) *)
  distinct : segment_closed.t S ;
  bassert_symbols : bassert distinct \o (@symbols _ [the freshMonad S of M]) =
                    @symbols _ [the freshMonad S of M] ;
  (* failure is a right zero of composition (backtracking interpretation) *)
  failfresh_bindmfail : BindLaws.right_zero (@bind [the monad of M]) (@fail _)
}.

HB.structure Definition MonadFailFresh (S : eqType) :=
  { M of isMonadFailFresh S M & isFunctor M & isMonad M & isMonadFresh S M &
         isMonadFail M }.
Notation failFreshMonad := MonadFailFresh.type.
