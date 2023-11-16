(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2020 monae authors, license: LGPL-2.1-or-later               *)
Ltac typeof X := type of X.

Require Import ssrmatching Reals JMeq.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp Require boolp.
From mathcomp Require Import Rstruct reals.
From infotheo Require Import Reals_ext.
From infotheo Require Import realType_ext.
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
(*                FId == notation for the identity functor                    *)
(*             F ~> G == natural transformation from functor F to functor G   *)
(*            f ~~> g == forall A, f A -> g A, notation used for the          *)
(*                       components of a natural transformation               *)
(*   naturality F G f == the components f form a natural transformation       *)
(*                       F ~> G                                               *)
(*    Module JoinLaws == join laws of a monad                                 *)
(*            isMonad == mixin of monad                                       *)
(*                >>= == notation for the standard bind operator              *)
(*             m >> f := m >>= (fun _ => f)                                   *)
(*              monad == type of monads                                       *)
(*                Ret == natural transformation FId ~> M for a monad M        *)
(*               Join == natural transformation M \o M ~> M for a monad M     *)
(*    Module BindLaws == bind laws of a monad                                 *)
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
(*      plusArrayMonad  == plus monad + array monad                           *)
(*                                                                            *)
(*          ML_universe == a type with decidable equality to represent an     *)
(*                         OCaml type together with its Coq representation    *)
(*                         in the type of a Tarski universe                   *)
(*      typedStoreMonad == A monad for OCaml computations                     *)
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
(* - R. Affeldt, J. Garrigue, T. Saikawa, Environment-friendly monadic        *)
(* equational reasoning for OCaml, The Coq Workshop 2023                      *)
(* - R. Affeldt, D. Nowak, Extending Equational Monadic Reasoning with Monad  *)
(* Transformers, TYPES 2020, https://arxiv.org/abs/2011.03463                 *)
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
Variable (F : UU0 -> UU0) (f : forall A B : UU0, (A -> B) -> F A -> F B).
Definition id := forall A : UU0, f id = id :> (F A -> F A).
Definition comp := forall (A B C : UU0) (g : B -> C) (h : A -> B),
  f (g \o h) = f g \o f h.
End def.
End FunctorLaws.

HB.mixin Record isFunctor (F : UU0 -> UU0) := {
  actm : forall A B : UU0, (A -> B) -> F A -> F B ;
  functor_id : FunctorLaws.id actm ;
  functor_o : FunctorLaws.comp actm }.

#[short(type=functor)]
HB.structure Definition Functor := {F of isFunctor F}.

Notation "F # g" := (@actm F _ _ g) : monae_scope.
Notation "'fmap' f" := (_ # f) : mprog.

Section functorid.
Let id_actm (A B : UU0) (f : A -> B) : idfun A -> idfun B := f.
Let id_id : FunctorLaws.id id_actm. Proof. by []. Qed.
Let id_comp : FunctorLaws.comp id_actm. Proof. by []. Qed.
HB.instance Definition _ := isFunctor.Build idfun id_id id_comp.
End functorid.

(* NB: consider eliminating? *)
Notation FId := [the functor of idfun].

Lemma FIdE (A B : UU0) (f : A -> B) : FId # f = f. Proof. by []. Qed.

Section functor_composition.
Variables f g : functor.

Let comp_actm (A B : UU0) (h : A -> B) : (f \o g) A -> (f \o g) B :=
  f # (g # h).

Let comp_id : FunctorLaws.id comp_actm.
Proof. by rewrite /FunctorLaws.id => A; rewrite /comp_actm 2!functor_id. Qed.

Let comp_comp : FunctorLaws.comp comp_actm.
Proof.
rewrite /FunctorLaws.comp => A B C g' h; rewrite /comp_actm.
by apply boolp.funext => m; rewrite [in RHS]compE 2!functor_o.
Qed.

HB.instance Definition _ := isFunctor.Build (f \o g) comp_id comp_comp.

End functor_composition.

Lemma FCompE (f g : functor) (A B : UU0) (k : A -> B) :
  [the functor of f \o g] # k = f # (g # k).
Proof. by []. Qed.

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
  eq_rect _ (fun m : UU0 -> UU0 => forall A B : UU0, (A -> B) -> m A -> m B)
            (@actm F) _ H  ->
  G = F.
Proof.
move: F G => [F [[HF1 HF2 HF3]]] [G [[HG1 HG2 HG3]]] /= H.
subst F => /= H.
congr (Functor.Pack (Functor.Class _)).
have ? : HG1 = HF1.
  rewrite /actm /= in H.
  apply funext_dep => x.
  apply funext_dep => y.
  apply funext_dep => z.
  by move/(congr1 (fun i => i x y z)) : H.
subst HG1.
congr (isFunctor.Axioms_ _); exact/proof_irr.
Defined.

Definition naturality (F G : functor) (f : F ~~> G) :=
  forall (A B : UU0) (h : A -> B), (G # h) \o f A = f B \o (F # h).
Arguments naturality : clear implicits.

HB.mixin Record isNatural (F G : functor) (f : F ~~> G) := {
  natural : naturality F G f }.

#[short(type=nattrans)]
HB.structure Definition Nattrans (F G : functor) := {f of isNatural F G f}.
Arguments natural {F G} s.
Notation "f ~> g" := (nattrans f g) : monae_scope.

Section natrans_lemmas.
Variables (F G : functor) (phi : F ~> G).
Lemma nattrans_ext (f g : F ~> G) : f = g <-> forall a, (f a = g a :> (_ -> _)).
Proof.
split => [ -> // |]; move: f g => [f Hf] [g Hg] /= fg.
have ? : f = g by exact: funext_dep.
subst g.
suff : Hf = Hg by move=> ->.
case: Hf => -[Hf].
case: Hg => -[Hg].
do 2 f_equal.
exact: proof_irr.
Qed.
End natrans_lemmas.

(*Require Import Logic.Eqdep.

Lemma natural_ext (F G G' : functor) (t : F ~> G) (t' : F ~> G') :
  forall (H : G = G'),
  forall (K : forall X (x : F X), Natural.cpnt t' x = eq_rect _ (fun m : functor => m X) (Natural.cpnt t x) _ H),
  t' = eq_rect _ (fun m : functor => F ~> m) t _ H.
Proof.
move : t t' => [t t1] [t' t'1] /= H; subst G' => H /=.
have ? : t = t'.
  apply funext_dep => A; apply funext_dep => x.
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
  apply funext_dep => A; apply funext_dep => x.
  by rewrite L -[in RHS]eq_rect_eq.
subst t'.
congr Natural.Pack; exact/proof_irr.
Qed.*)

Module JoinLaws.
Section join_laws.
Context {F : functor}.
Variables (ret : FId ~> F) (join : F \o F ~~> F).

Definition left_unit := forall A, @join A \o ret (F A) = id :> (F A -> F A).

Definition right_unit := forall A, @join A \o F # ret A = id :> (F A -> F A).

Definition associativity :=
  forall A, @join A \o F # @join A = @join A \o @join (F A) :> (F (F (F A)) -> F A).

End join_laws.
End JoinLaws.

HB.mixin Record isMonad (F : UU0 -> UU0) of Functor F := {
  ret : FId ~> F ;
  join : F \o F ~> F ;
  bind : forall (A B : UU0), F A -> (A -> F B) -> F B ;
  __bindE : forall (A B : UU0) (f : A -> F B) (m : F A),
    bind A B m f = join B ((F # f) m) ;
  joinretM : JoinLaws.left_unit ret join ;
  joinMret : JoinLaws.right_unit ret join ;
  joinA : JoinLaws.associativity join }.

#[short(type=monad)]
HB.structure Definition Monad := {F of isMonad F &}.

Notation Ret := (@ret _ _).
Notation Join := (@join _ _).
Arguments bind {s A B} : simpl never.
Notation "m >>= f" := (bind m f) : monae_scope.

Lemma bindE (F : monad) (A B : UU0) (f : A -> F B) (m : F A) :
  m >>= f = join B ((F # f) m).
Proof. by rewrite __bindE. Qed.

Lemma eq_bind (M : monad) (A B : UU0) (m : M A) (f1 f2 : A -> M B) :
  f1 =1 f2 -> m >>= f1 = m >>= f2.
Proof. by move=> f12; congr bind; apply boolp.funext. Qed.

Section monad_lemmas.
Variable M : monad.

Lemma fmapE (A B : UU0) (f : A -> B) (m : M A) :
 (M # f) m = m >>= (ret B \o f).
Proof.
by rewrite bindE [in RHS]functor_o -[in RHS]compE compA joinMret.
Qed.

End monad_lemmas.

Module BindLaws.
Section bindlaws.
Variable F : UU0 -> UU0.
Variable b : forall (A B : UU0), F A -> (A -> F B) -> F B.
Local Notation "m >>= f" := (b m f).

Definition associative := forall A B C (m : F A) (f : A -> F B) (g : B -> F C),
  (m >>= f) >>= g = m >>= (fun x => f x >>= g).

Definition right_distributive (add : forall B, F B -> F B -> F B) :=
  forall A B (m : F A) (k1 k2 : A -> F B),
    m >>= (fun x => add _ (k1 x) (k2 x)) = add _ (m >>= k1) (m >>= k2).

Definition left_distributive (add : forall B, F B -> F B -> F B) :=
  forall A B (m1 m2 : F A) (k : A -> F B),
    (add _ m1 m2) >>= k = add _ (m1 >>= k) (m2 >>= k).

Definition left_zero (f : forall A, F A) :=
  forall (A B : UU0) (g : A -> F B), f A >>= g = f B.

Definition right_zero (f : forall A, F A) :=
  forall (A B : UU0) (g : F B), g >>= (fun _ => f A) = f A.

Definition left_neutral (r : forall A : UU0, A -> F A) :=
  forall (A B : UU0) (a : A) (f : A -> F B), r _ a >>= f = f a.

Definition right_neutral (r : forall A : UU0, A -> F A) :=
  forall A (m : F A), m >>= r _ = m.

Definition left_id (r : forall A, F A) (op : forall B, F B -> F B -> F B) :=
  forall A (m : F A), op _ (r _) m = m.

Definition right_id (r : forall A, F A) (op : forall B, F B -> F B -> F B) :=
  forall A (m : F A), op _ m (r _) = m.

End bindlaws.
End BindLaws.

Definition join_of_bind (F : functor)
    (b : forall (A B : UU0), F A -> (A -> F B) -> F B) : F \o F ~~> F :=
  fun A : UU0 => (b _ A)^~ id.

Definition bind_of_join (F : functor) (j : F \o F ~~> F)
    (A B : UU0) (m : F A) (f : A -> F B) : F B :=
  j B ((F # f) m).

Section from_join_laws_to_bind_laws.
Variable (F : functor) (ret : FId ~> F) (join : [the functor of F \o F] ~> F).

Hypothesis joinretM : JoinLaws.left_unit ret join.
Hypothesis joinMret : JoinLaws.right_unit ret join.
Hypothesis joinA : JoinLaws.associativity join.

Lemma bindretf_derived : BindLaws.left_neutral (bind_of_join join) ret.
Proof.
move=> A B a f; rewrite /bind_of_join -(compE (@join _)) -(compE _ (@ret _)).
by rewrite -compA (natural ret) compA joinretM compidf.
Qed.

Lemma bindmret_derived : BindLaws.right_neutral (bind_of_join join) ret.
Proof. by move=> A m; rewrite /bind_of_join -(compE (@join _)) joinMret. Qed.

Lemma bindA_derived : BindLaws.associative (bind_of_join join).
Proof.
move=> A B C m f g; rewrite /bind_of_join.
rewrite [LHS](_ : _ = ((@join _ \o (F # g \o @join _) \o F # f) m)) //.
rewrite (natural join) (compA (@join C)) -joinA -(compE (@join _)).
transitivity ((@join _ \o F # (@join _ \o (F # g \o f))) m) => //.
by rewrite -2!compA functor_o FCompE -[in LHS](@functor_o F).
Qed.

End from_join_laws_to_bind_laws.

HB.factory Record isMonad_ret_join (F : UU0 -> UU0) of isFunctor F := {
  ret : FId ~> [the functor of F] ;
  join : [the functor of F \o F] ~> [the functor of F] ;
  joinretM : JoinLaws.left_unit ret join ;
  joinMret : JoinLaws.right_unit ret join ;
  joinA : JoinLaws.associativity join }.

HB.builders Context M of isMonad_ret_join M.

Let F := [the functor of M].

Let bind (A B : UU0) (m : F A) (f : A -> F B) : F B :=
  bind_of_join join m f.

Let bindE (A B : UU0) (f : A -> M B) (m : M A) :
  bind m f = join B ((F # f) m).
Proof. by []. Qed.

HB.instance Definition _ := isMonad.Build M bindE joinretM joinMret joinA.
HB.end.

HB.factory Record isMonad_ret_bind (F : UU0 -> UU0) := {
  ret' : forall (A : UU0), A -> F A ;
  bind : forall (A B : UU0), F A -> (A -> F B) -> F B ;
  bindretf : BindLaws.left_neutral bind ret' ;
  bindmret : BindLaws.right_neutral bind ret' ;
  bindA : BindLaws.associative bind }.

HB.builders Context M of isMonad_ret_bind M.

Let actm (a b : UU0) (f : a -> b) m := bind m (@ret' _ \o f).

Let actm_id : FunctorLaws.id actm.
Proof.
move=> a.
rewrite /actm; apply: boolp.funext=> m /=.
by rewrite bindmret.
Qed.

Let actm_comp : FunctorLaws.comp actm.
Proof.
move=> a b c g h.
rewrite /actm; apply: boolp.funext => m /=.
rewrite bindA.
congr bind.
apply: boolp.funext => u /=.
by rewrite bindretf.
Qed.

HB.instance Definition _ := isFunctor.Build M actm_id actm_comp.
Let F := [the functor of M].
Local Notation FF := [the functor of F \o F].

Let ret'_naturality : naturality FId F ret'.
Proof.
move=> a b h.
rewrite FIdE /hierarchy.actm /= /actm; apply: boolp.funext => m /=.
by rewrite bindretf.
Qed.

HB.instance Definition _ :=
  isNatural.Build FId F (ret' : FId ~~> F) ret'_naturality.
Let ret := [the FId ~> F of ret'].

Let join' : FF ~~> F := fun _ m => bind m idfun.

Let actm_bind (a b c : UU0) (f : a -> b) m (g : c -> F a) :
  (actm f) (bind m g) = bind m (actm f \o g).
Proof. by rewrite /actm bindA. Qed.

Let join'_naturality : naturality FF F join'.
Proof.
move=> a b h.
rewrite /join' /=; apply: boolp.funext => mm /=.
rewrite /hierarchy.actm /= /isFunctor.actm /=.
rewrite actm_bind bindA /=.
congr bind.
apply: boolp.funext => m /=.
by rewrite bindretf /=.
Qed.

HB.instance Definition _ := isNatural.Build _ _ _ join'_naturality.
Let join := [the FF ~> F of join'].

Let bind_map (A B C : UU0) (f : A -> B) (m : M A) (g : B -> M C) :
  bind ((F # f) m) g = bind m (g \o f).
Proof.
rewrite bindA; congr bind.
by apply: boolp.funext => ?; rewrite bindretf.
Qed.

Let bindE (a b : UU0) (f : a -> M b) (m : M a) :
  bind m f = join b ((F # f) m).
Proof.
rewrite /join /= /hierarchy.actm /= /join' /=.
by rewrite bind_map.
Qed.

Let joinretM : JoinLaws.left_unit ret join.
Proof.
move=> a; apply: boolp.funext => m.
by rewrite /join /= /join' /= bindretf.
Qed.

Let joinMret : JoinLaws.right_unit ret join.
Proof.
move=> a; apply: boolp.funext => m.
rewrite /join /= /join'.
rewrite /hierarchy.actm /= /actm /=.
rewrite bindA /=.
rewrite [X in bind m X](_ : _ = fun x => ret' x) ?bindmret //=; apply: boolp.funext => ?.
by rewrite bindretf.
Qed.

Let joinA : JoinLaws.associativity join.
Proof.
move => a; apply: boolp.funext => m.
rewrite /join /= /join'.
rewrite /hierarchy.actm /= /actm.
rewrite !bindA.
congr bind.
apply: boolp.funext => u /=.
by rewrite bindretf.
Qed.

HB.instance Definition _ := isMonad.Build M bindE joinretM joinMret joinA.
HB.end.

Section monad_lemmas.
Variable M : monad.

Lemma bindretf : BindLaws.left_neutral (@bind M) ret.
Proof.
move: (@bindretf_derived M ret join joinretM).
rewrite (_ : bind_of_join _ = @bind M) //.
apply funext_dep => A; apply funext_dep => B.
apply funext_dep => m; apply funext_dep => f.
by rewrite bindE.
Qed.

Lemma bindmret : BindLaws.right_neutral (@bind M) ret.
Proof.
move: (@bindmret_derived M ret join joinMret).
rewrite (_ : bind_of_join _ = @bind M) //.
apply funext_dep => A; apply funext_dep => B.
apply funext_dep => m; apply funext_dep => f.
by rewrite bindE.
Qed.

Lemma bindA : BindLaws.associative (@bind M).
Proof.
move: (@bindA_derived M join joinA).
rewrite (_ : bind_of_join _ = @bind M) //.
apply funext_dep => A; apply funext_dep => B.
apply funext_dep => m; apply funext_dep => f.
by rewrite bindE.
Qed.

End monad_lemmas.

Notation "'do' x <- m ; e" := (bind m (fun x => e)) (only parsing) : do_notation.
Notation "'do' x : T <- m ; e" :=
  (bind m (fun x : T => e)) (only parsing) : do_notation.
Delimit Scope do_notation with Do.
Notation "m >> f" := (bind m (fun _ => f)) : monae_scope.

Fixpoint sequence (M : monad) A (s : seq (M A)) : M (seq A) :=
  (if s isn't h :: t then Ret [::] else
  do v <- h; do vs <- sequence t; Ret (v :: vs))%Do.

Lemma sequence_nil (M : monad) (A : UU0) :
  sequence [::] = Ret [::] :> M (seq A).
Proof. by []. Qed.

Lemma sequence_cons (M : monad) A h (t : seq (M A)) :
  (sequence (h :: t) = do x <- h ; do vs <- sequence t ; Ret (x :: vs))%Do.
Proof. by []. Qed.

Definition skip M := @ret M _ tt.
Arguments skip {M} : simpl never.

Ltac bind_ext :=
  let congr_ext m := ltac:(congr (bind m); apply boolp.funext) in
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
   apply boolp.funext => x; rewrite {}/g {}/f; tac]; last first.

Tactic Notation "Open" ssrpatternarg(pat) :=
  With (idtac) Open pat.

Section fmap_and_join.
Variable M : monad.
Local Open Scope mprog.

Lemma bind_fmap (A B C : UU0) (f : A -> B) (m : M A) (g : B -> M C) :
  fmap f m >>= g = m >>= (g \o f).
Proof. by rewrite fmapE bindA; under eq_bind do rewrite bindretf. Qed.

Lemma fmap_if (A B : UU0) (f : A -> B) b (m : M A) a :
  fmap f (if b then m else Ret a) = if b then fmap f m else Ret (f a).
Proof. case: ifPn => Hb //; by rewrite fmapE bindretf. Qed.

Lemma fmap_bind (A B C : UU0) (f : A -> B) m (g : C -> M A) :
  fmap f (m >>= g) = m >>= (f (o) g).
Proof.
rewrite fcomp_def fmapE bindA; bind_ext => c.
by rewrite compE -/(fmap _ _) fmapE.
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
Implicit Types A B C D : UU0.

Definition kleisli A B C (m : B -> M C) (n : A -> M B) : A -> M C :=
  Join \o (M # m) \o n.
Local Notation "m <=< n" := (kleisli m n).
Local Notation "m >=> n" := (kleisli n m).

Lemma kleisli_def A B C (g : B -> M C) (f : A -> M B) :
  (f >=> g) = Join \o (M # g) \o f.
Proof. by []. Qed.

Lemma kleisliE A B C (g : B -> M C) (f : A -> M B) (a : A) :
  (f >=> g) a = (f a) >>= g.
Proof. by rewrite /kleisli /= join_fmap. Qed.

Lemma bind_kleisli A B C m (f : A -> M B) (g : B -> M C) :
  m >>= (f >=> g) = (m >>= f) >>= g.
Proof. by rewrite bindA; bind_ext => a; rewrite /kleisli !compE join_fmap. Qed.

Lemma ret_kleisli A B (k : A -> M B) : Ret >=> k = k.
Proof. by rewrite /kleisli -compA (natural ret) FIdE compA joinretM. Qed.

Local Open Scope mprog.
Lemma fcomp_kleisli A B C D (f : A -> B) (g : C -> M A) (h : D -> M C) :
  f (o) (g <=< h) = (f (o) g) <=< h.
Proof.
rewrite /kleisli 2!fcomp_def 2!(compA (fmap f)) natural [in RHS]functor_o.
by rewrite -compA.
Qed.

Lemma kleisli_fcomp A B C (f : A -> M B) (g : B -> A) (h : C -> M B) :
  ((f \o g) <=< h) = f <=< (g (o) h).
Proof. by rewrite /kleisli fcomp_def functor_o 2!compA. Qed.
Local Close Scope mprog.

Lemma kleisliA A B C D (f : A -> M B) (g : B -> M C) (h : C -> M D) :
  f >=> g >=> h = f >=> (g >=> h).
Proof.
apply: funext_dep => a; rewrite !kleisliE bindA.
by under [in RHS]eq_bind do rewrite kleisliE.
Qed.

End kleisli.
Notation "m <=< n" := (kleisli m n) : monae_scope.
Notation "m >=> n" := (kleisli n m) : monae_scope.

HB.mixin Record isMonadFail (M : UU0 -> UU0) of Monad M := {
  fail : forall A : UU0, M A;
    (* exceptions are left-zeros of sequential composition *)
  bindfailf : BindLaws.left_zero (@bind [the monad of M]) fail
    (* fail A >>= f = fail B *) }.

#[short(type=failMonad)]
HB.structure Definition MonadFail := {M of isMonadFail M & }.

Arguments bindfailf [_].
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

Lemma assertE {A : UU0} (p : pred A) (a : A) :
  assert p a = guard (p a) >> Ret a.
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
by apply boolp.funext => x; rewrite !compE join_fmap /bassert joinE bindA.
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
(* NB: no bindDr to accommodate both angelic and demonic interpretations of
   nondeterminism *) }.

#[short(type=altMonad)]
HB.structure Definition MonadAlt := {M of isMonadAlt M & }.

Notation "a [~] b" := (@alt _ _ a b). (* infix notation *)

HB.mixin Record isMonadAltCI (M : UU0 -> UU0) of MonadAlt M := {
  altmm : forall A : UU0, idempotent (@alt [the altMonad of M] A) ;
  altC : forall A : UU0, commutative (@alt [the altMonad of M] A) }.

#[short(type=altCIMonad)]
HB.structure Definition MonadAltCI := {M of isMonadAltCI M & }.

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
  altfailm :
    @BindLaws.left_id [the functor of M] (@fail [the failMonad of M])
                                         (@alt [the altMonad of M]);
  altmfail :
    @BindLaws.right_id [the functor of M] (@fail [the failMonad of M])
                                          (@alt [the altMonad of M]) }.

#[short(type=nondetMonad)]
HB.structure Definition MonadNondet :=
  {M of isMonadNondet M & MonadFail M & MonadAlt M}.

#[short(type=nondetCIMonad)]
HB.structure Definition MonadCINondet := {M of MonadAltCI M & MonadNondet M}.

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

HB.mixin Record isMonadFailR0 (M : UU0 -> UU0) of MonadFail M :=
 { bindmfail : BindLaws.right_zero (@bind [the monad of M]) (@fail _) }.

#[short(type=failR0Monad)]
HB.structure Definition MonadFailR0 := {M of isMonadFailR0 M & }.

HB.mixin Record isMonadPrePlus (M : UU0 -> UU0)
    of MonadNondet M & MonadFailR0 M :=
  { alt_bindDr : BindLaws.right_distributive (@bind [the monad of M]) alt }.

#[short(type=prePlusMonad)]
HB.structure Definition MonadPrePlus := {M of isMonadPrePlus M & }.

#[short(type=plusMonad)]
HB.structure Definition MonadPlus := {M of MonadCINondet M & MonadPrePlus M}.

HB.mixin Record isMonadExcept (M : UU0 -> UU0) of MonadFail M := {
  catch : forall A, M A -> M A -> M A ;
  (* monoid *)
  catchmfail : forall A, right_id fail (@catch A) ;
  catchfailm : forall A, left_id fail (@catch A) ;
  catchA : forall A, associative (@catch A) ;
  (* unexceptional bodies need no handler *)
  catchret : forall A x, @left_zero (M A) (M A) (Ret x) (@catch A)
  (* NB: left-zero of sequential composition inherited from failMonad *) }.

#[short(type=exceptMonad)]
HB.structure Definition MonadExcept := {M of isMonadExcept M & }.

Arguments catch {_} {_}.

HB.mixin Record isMonadContinuation (M : UU0 -> UU0) of Monad M := {
(* NB: interface is wip *)
  callcc : forall A B : UU0, ((A -> M B) -> M A) -> M A;
  callcc0 : forall (A B : UU0) (g : (A -> M B) -> M A) (k : B -> M B),
    @callcc _ _ (fun f => g (fun x => f x >>= k)) = @callcc _ _ g
    (* see Sect. 7.2 of [Schrijvers, 19] *);
  callcc1 : forall (A B : UU0) (m : M B),
    @callcc _ _ (fun _ : B -> M A => m) = m
    (* see Sect. 3.3 of [Wadler, 94] *);
  callcc2 : forall (A B C : UU0) (m : M A) x (k : A -> B -> M C),
    @callcc _ _ (fun f : _ -> M _ => m >>= (fun a => f x >>= (fun b => k a b)))
    = @callcc _ _ (fun f : _ -> M _ => m >> f x) ;
  callcc3 : forall (A B : UU0) (m : M A) b,
    @callcc _ _ (fun f : B -> M B => m >> f b) =
    @callcc _ _ (fun _ : B -> M B => m >> Ret b) }.

#[short(type=contMonad)]
HB.structure Definition MonadContinuation := {M of isMonadContinuation M & }.
Arguments callcc {_} {_} {_}.

HB.mixin Record isMonadShiftReset (U : UU0) (M : UU0 -> UU0)
    of MonadContinuation M := {
  shift : forall A : UU0, ((A -> M U) -> M U) -> M A ;
  reset : M U -> M U ;
  shiftreset0 : forall (A : UU0) (m : M A), @shift _ (fun k => m >>= k) = m ;
    (* see Sect. 3.3 of [Wadler, 94] *)
  shiftreset1 : forall (A B : UU0) (h : (A -> M B) -> M A), callcc h =
    @shift _ (fun k' => h (fun x => @shift _ (fun k'' => k' x)) >>= k') ;
    (* see Sect. 3.3 of [Wadler, 94] *)
  shiftreset2 : forall (A : UU0) (c : A) (c': U) (k : A -> U -> _),
    (reset (do x <- Ret c; do y <- @shift _ (fun _ => Ret c'); k x y) =
     Ret c >> Ret c')%Do ;
  shiftreset3 : forall (c c' : U) (k : U -> U -> _),
    (reset (do x <- Ret c; do y <- @shift _ (fun f => do v <- f c'; f v);
            Ret (k x y)) =
     reset (do x <- Ret c; do y <- @shift _ (fun f => f c');
            Ret (k x (k x y))))%Do ;
  shiftreset4 : forall (c : U) k,
    (reset (do y <- @shift _ (@^~ c); Ret (k y)) = Ret (k c))%Do }.

#[short(type=shiftresetMonad)]
HB.structure Definition MonadShiftReset U := {M of isMonadShiftReset U M & }.
Arguments shift {_} {_} {_}.

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
    @sub _ _ (fun r2 : ref B => @sub _ _ (fun r1 => p r1 r2) k1)
             (fun x => @sub _ _ (k2^~ x) k1)
    (*NB: differs from [Schrijvers et al. 19]*);
  jump4 : forall (A B : UU0) r x k, (@jump A B r x) >>= k = @jump A B r x;
  jump5 : forall (A B : UU0) p q k,
    @sub A B p q >>= k = @sub A B (p >=> k) (q >=> k) }.

#[short(type=jumpMonad)]
HB.structure Definition MonadJump ref := {M of isMonadJump ref M & }.
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

#[short(type=stateMonad)]
HB.structure Definition MonadState (S : UU0) := { M of isMonadState S M & }.

(*NB: explicit join newly added*)
#[short(type=failStateMonad)]
HB.structure Definition MonadFailState (S : UU0) :=
  { M of isMonadFail M & isMonadState S M & isMonad M & isFunctor M }.

(*NB: explicit join newly added*)
#[short(type=failR0StateMonad)]
HB.structure Definition MonadFailR0State (S : UU0) :=
  { M of isMonadFailR0 M & isMonadState S M & isMonadFail M & isMonad M &
         isFunctor M }.

#[short(type=nondetStateMonad)]
HB.structure Definition MonadNondetState (S : UU0) :=
  { M of MonadPrePlus M & MonadState S M }.

HB.mixin Record isMonadStateRun (S : UU0) (N : monad)
   (M : UU0 -> UU0) of MonadState S M := {
  runStateT : forall A : UU0, M A -> S -> N (A * S)%type ;
  runStateTret : forall (A : UU0) (a : A) (s : S),
    @runStateT _ (Ret a) s = Ret (a, s) ;
  runStateTbind : forall (A B : UU0) (m : M A) (f : A -> M B) (s : S),
    @runStateT _ (m >>= f) s =
    @runStateT _ m s >>= fun x => @runStateT _ (f x.1) x.2 ;
  runStateTget : forall s : S, @runStateT _ get s = Ret (s, s) ;
  runStateTput : forall s' s : S, @runStateT _ (put s') s = Ret (tt, s') }.

#[short(type=stateRunMonad)]
HB.structure Definition MonadStateRun (S : UU0) (N : monad) :=
  {M of isMonadStateRun S N M & }.

Arguments runStateT {_} {_} {_} {_}.

HB.mixin Record isMonadExceptStateRun
    (S : UU0) (N : exceptMonad) (M : UU0 -> UU0)
    of MonadStateRun S N M & MonadExcept M := Mixin {
  runStateTfail : forall (A : UU0) (s : S),
    runStateT (@fail [the exceptMonad of M] A) s = @fail N _ ;
  runStateTcatch : forall (A : UU0) (s : S) (m1 m2 : M A),
    runStateT (@catch [the exceptMonad of M] _ m1 m2) s =
    @catch N _ (runStateT m1 s) (runStateT m2 s) }.

#[short(type=exceptStateRunMonad)]
HB.structure Definition MonadExceptStateRun (S : UU0) (N : exceptMonad) :=
  {M of isMonadExceptStateRun S N M & }.

HB.mixin Record isMonadReify (S : UU0) (M : UU0 -> UU0) of Monad M := {
  reify : forall A : UU0, M A -> S -> option (A * S)%type ;
  reifyret : forall (A : UU0) (a : A) s, @reify _ (Ret a) s = Some (a, s) ;
  reifybind : forall (A B : UU0) (m : M A) (f : A -> M B) s,
      @reify _ (m >>= f) s = match @reify _ m s with
                             | Some a's' => @reify _ (f a's'.1) a's'.2
                             | None => None
                             end }.

#[short(type=reifyMonad)]
HB.structure Definition MonadReify (S : UU0) := {M of isMonadReify S M & }.
Arguments reify {_} {_} {_}.

HB.mixin Record isMonadStateReify (S : UU0) (M : UU0 -> UU0)
    of MonadReify S M & MonadState S M := {
  reifyget : forall s, reify (@get _ [the stateMonad S of M]) s = Some (s, s) ;
  reifyput : forall s s',
    reify (@put _ [the stateMonad S of M] s') s = Some (tt, s') }.

#[short(type=stateReifyMonad)]
HB.structure Definition MonadStateReify (S : UU0) :=
  {M of isMonadStateReify S M &}.

HB.mixin Record isMonadFailReify (S : UU0) (M : UU0 -> UU0)
    of MonadReify S M & MonadFail M :=
  { reifyfail : forall S' (s : S),
      reify (@fail [the failMonad of M] S') s = None }.

#[short(type=failReifyMonad)]
HB.structure Definition MonadFailReify (S : UU0) :=
  {M of isMonadFailReify S M & }.

#[short(type=failFailR0ReifyMonad)]
HB.structure Definition MonadFailFailR0Reify (S : UU0) :=
  {M of MonadFailReify S M & MonadFailR0 M}.

#[short(type=failStateReifyMonad)]
HB.structure Definition MonadFailStateReify (S : UU0) :=
  {M of MonadStateReify S M & MonadFailFailR0Reify S M}.

(* NB: this is experimental, may disappear, see rather foreach in
   monad_transformer because it is more general *)
HB.mixin Record isMonadStateLoop (S : UU0) (M : UU0 -> UU0)
    of MonadState S M := {
  foreach : nat -> nat -> (nat -> M unit) -> M unit ;
  loop0 : forall m body, foreach m m body = Ret tt ;
  loop1 : forall m n body,
    foreach (m.+1 + n) m body = (body (m + n)) >> foreach (m + n) m body }.

#[short(type=loopStateMonad)]
HB.structure Definition MonadStateLoop (S : UU0) :=
  {M of isMonadStateLoop S M & }.

HB.mixin Record isMonadArray (S : UU0) (I : eqType) (M : UU0 -> UU0)
    of Monad M := {
  aget : I -> M S ;
  aput : I -> S -> M unit ;
  aputput : forall i s s', aput i s >> aput i s' = aput i s' ;
  aputget : forall i s (A : UU0) (k : S -> M A), aput i s >> aget i >>= k =
      aput i s >> k s ;
  agetputskip : forall i, aget i >>= aput i = skip ;
  agetget : forall i (A : UU0) (k : S -> S -> M A),
    aget i >>= (fun s => aget i >>= k s) = aget i >>= fun s => k s s ;
  agetC : forall i j (A : UU0) (k : S -> S -> M A),
    aget i >>= (fun u => aget j >>= (fun v => k u v)) =
    aget j >>= (fun v => aget i >>= (fun u => k u v)) ;
  aputC : forall i j u v, (i != j) \/ (u = v) ->
    aput i u >> aput j v = aput j v >> aput i u ;
  aputgetC : forall i j u (A : UU0) (k : S -> M A), i != j ->
    aput i u >> aget j >>= k =
    aget j >>= (fun v => aput i u >> k v) }.

#[short(type=arrayMonad)]
HB.structure Definition MonadArray (S : UU0) (I : eqType) :=
  { M of isMonadArray S I M & isMonad M & isFunctor M }.

#[short(type=plusArrayMonad)]
HB.structure Definition MonadPlusArray (S : UU0) (I : eqType) :=
  { M of MonadPlus M & isMonadArray S I M}.

Variant loc (ml_type : Type) (locT : eqType) : ml_type -> Type :=
  mkloc T : locT -> loc locT T.
Definition loc_id (ml_type : Type) (locT : eqType) {T : ml_type} (l : loc locT T) : locT :=
  let: mkloc _ n := l in n.

HB.mixin Structure isML_universe (ml_type : Type) := {
  eqclass : Equality.class_of ml_type ;
  coq_type : forall M : Type -> Type, ml_type -> Type ;
  ml_nonempty : ml_type ;
  val_nonempty : forall M, coq_type M ml_nonempty }.

#[short(type=ML_universe)]
HB.structure Definition ML_UNIVERSE := {ml_type & isML_universe ml_type}.

Canonical isML_universe_eqType (T : ML_universe) := EqType T eqclass.

HB.mixin Record isMonadTypedStore (MLU : ML_universe) (locT : eqType) (M : UU0 -> UU0)
    of Monad M := {
  cnew : forall {T : MLU}, coq_type M T -> M (loc locT T) ;
  cget : forall {T}, loc locT T -> M (coq_type M T) ;
  cput : forall {T}, loc locT T -> coq_type M T -> M unit ;
  crun : forall {A : UU0}, M A -> option A ; (* execute in empty store *)
  cnewget : forall T (s : coq_type M T) A (k : loc locT T -> coq_type M T -> M A),
    cnew s >>= (fun r => cget r >>= k r) = cnew s >>= (fun r => k r s) ;
  cnewput : forall T (s t : coq_type M T) A (k : loc locT T -> M A),
      cnew s >>= (fun r => cput r t >> k r) = cnew t >>= k ;
  cgetput : forall T (r : loc locT T) (s : coq_type M T),
      cget r >> cput r s = cput r s ;
  cgetputskip : forall T (r : loc locT T), cget r >>= cput r = cget r >> skip ;
  cgetget :
    forall T (r : loc locT T) (A : UU0) (k : coq_type M T -> coq_type M T -> M A),
    cget r >>= (fun s => cget r >>= k s) = cget r >>= fun s => k s s ;
  cputget :
    forall T (r : loc locT T) (s : coq_type M T) (A : UU0) (k : coq_type M T -> M A),
      cput r s >> (cget r >>= k) = cput r s >> k s ;
  cputput : forall T (r : loc locT T) (s s' : coq_type M T),
    cput r s >> cput r s' = cput r s' ;
  cgetC :
    forall T1 T2 (r1 : loc locT T1) (r2 : loc locT T2) (A : UU0)
           (k : coq_type M T1 -> coq_type M T2 -> M A),
    cget r1 >>= (fun u => cget r2 >>= (fun v => k u v)) =
    cget r2 >>= (fun v => cget r1 >>= (fun u => k u v)) ;
  cgetnewD :
    forall T T' (r : loc locT T) (s : coq_type M T') A
           (k : loc locT T' -> coq_type M T -> coq_type M T -> M A),
      cget r >>= (fun u => cnew s >>= (fun r' => cget r >>= k r' u)) =
      cget r >>= (fun u => cnew s >>= (fun r' => k r' u u)) ;
  cgetnewE : forall T1 T2 (r1 : loc locT T1) (s : coq_type M T2) (A : UU0)
                   (k1 k2 : loc locT T2 -> M A),
      (forall r2 : loc locT T2, loc_id r1 != loc_id r2 -> k1 r2 = k2 r2) ->
      cget r1 >> (cnew s >>= k1) = cget r1 >> (cnew s >>= k2) ;
  cgetputC : forall T1 T2 (r1 : loc locT T1) (r2 : loc locT T2) (s : coq_type M T2),
      cget r1 >> cput r2 s = cput r2 s >> cget r1 >> skip ;
  cputC :
    forall T1 T2 (r1 : loc locT T1) (r2 : loc locT T2) (s1 : coq_type M T1)
           (s2 : coq_type M T2) (A : UU0),
      loc_id r1 != loc_id r2 \/ JMeq s1 s2 ->
      cput r1 s1 >> cput r2 s2 = cput r2 s2 >> cput r1 s1 ;
  cputgetC :
    forall T1 T2 (r1 : loc locT T1) (r2 : loc locT T2) (s1 : coq_type M T1)
           (A : UU0) (k : coq_type M T2 -> M A),
      loc_id r1 != loc_id r2 ->
    cput r1 s1 >> cget r2 >>= k =
    cget r2 >>= (fun v => cput r1 s1 >> k v) ;
  cputnewC :
    forall T T' (r : loc locT T) (s : coq_type M T) (s' : coq_type M T') A
           (k : loc locT T' -> M A),
      cget r >> (cnew s' >>= fun r' => cput r s >> k r') =
      cput r s >> (cnew s' >>= k) ;
  crunret : forall (A B : UU0) (m : M A) (s : B),
      crun m -> crun (m >> Ret s) = Some s ;
  crunskip :
      crun skip = Some tt ;
  crunnew : forall (A : UU0) T (m : M A) (s : A -> coq_type M T),
      crun m -> crun (m >>= fun x => cnew (s x)) ;
  crunnewget : forall (A : UU0) T (m : M A) (s : A -> coq_type M T),
      crun m -> crun (m >>= fun x => cnew (s x) >>= cget) ;
  crungetnew : forall (A : UU0) T1 T2 (m : M A) (r : A -> loc locT T1)
                      (s : A -> coq_type M T2),
      crun (m >>= fun x => cget (r x)) ->
      crun (m >>= fun x => cnew (s x) >> cget (r x)) ;
  crungetput : forall (A : UU0) T (m : M A) (r : A -> loc locT T)
                      (s : A -> coq_type M T),
      crun (m >>= fun x => cget (r x)) ->
      crun (m >>= fun x => cput (r x) (s x)) ;
 }.

#[short(type=typedStoreMonad)]
HB.structure Definition MonadTypedStore (ml_type : ML_universe) (locT : eqType) :=
  { M of isMonadTypedStore ml_type locT M & isMonad M & isFunctor M }.

Arguments cnew {ml_type locT s}.
Arguments cget {ml_type locT s} [T].
Arguments cput {ml_type locT s} [T].
Arguments crun {ml_type locT s} [A].

HB.mixin Record isMonadTrace (T : UU0) (M : UU0 -> UU0) of Monad M :=
 { mark : T -> M unit }.

#[short(type=traceMonad)]
HB.structure Definition MonadTrace (T : UU0) := {M of isMonadTrace T M & }.

HB.mixin Record isMonadTraceReify (T : UU0) (M : UU0 -> UU0)
    of MonadReify (seq T) M & MonadTrace T M := {
  reifytmark : forall t l,
    reify (@mark _ [the traceMonad T of M] t) l = Some (tt, rcons l t) }.

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
  st_getmark : forall e (k : _ -> M S),
    st_get >>= (fun v => st_mark e >> k v) = st_mark e >> st_get >>= k }.

#[short(type=stateTraceMonad)]
HB.structure Definition MonadStateTrace (S T : UU0) :=
  { M of isMonadStateTrace S T M & isMonad M & isFunctor M }.

HB.mixin Record isMonadStateTraceReify (S T : UU0) (M : UU0 -> UU0)
    of MonadReify (S * seq T)%type M & MonadStateTrace S T M := {
  reifystget : forall s l,
    reify (@st_get _ _ [the stateTraceMonad S T of M]) (s, l) =
    Some (s, (s, l)) ;
  reifystput : forall s l s',
    reify (@st_put _ _ [the stateTraceMonad S T of M] s') (s, l) =
    Some (tt, (s', l)) ;
  reifystmark : forall t s l,
    reify (@st_mark _ _ [the stateTraceMonad S T of M] t) (s, l) =
    Some (tt, (s, rcons l t)) }.

#[short(type=stateTraceReifyMonad)]
HB.structure Definition MonadStateTraceReify (S T : UU0) :=
  { M of isMonadStateTraceReify S T M & isFunctor M & isMonad M &
         isMonadReify S M & isMonadStateTrace S T M }.

HB.mixin Record isMonadProb {R : realType} (M : UU0 -> UU0) of Monad M := {
  choice : forall (p : {prob R}) (T : UU0), M T -> M T -> M T ;
  (* identity axioms *)
  choice0 : forall (T : UU0) (a b : M T), choice 0%:pr _ a b = b ;
  choice1 : forall (T : UU0) (a b : M T), choice 1%:pr _ a b = a ;
  (* skewed commutativity *)
  choiceC : forall (T : UU0) p (a b : M T),
    choice p _ a b = choice ((Prob.p p).~ %:pr) _ b a ;
  choicemm : forall (T : UU0) p, idempotent (@choice p T) ;
  (* quasi associativity *)
  choiceA : forall (T : UU0) (p q r s : {prob R}) (a b c : M T),
    (p = (r : R) * (s : R) :> R /\ (Prob.p s).~ = (Prob.p p).~ * (Prob.p q).~)%R ->
    (*NB: needed to preserve the notation in the resulting choiceA lemma*)
    let bc := choice q _ b c in
    let ab := choice r _ a b in
    choice p _ a bc = choice s _ ab c;
  (* composition distributes leftwards over [probabilistic] choice *)
  choice_bindDl :
    forall p, BindLaws.left_distributive (@bind [the monad of M]) (choice p) }.

#[short(type=probMonad)]
HB.structure Definition MonadProb {R : realType} := {M of isMonadProb R M & }.
Notation "a <| p |> b" := (choice p _ a b) : proba_monad_scope.
Arguments choiceA {_} {_} {_} _ _ _ _ {_} {_} {_}.
Arguments choiceC {_} {_} {_} _ _ _.
Arguments choicemm {_} {_} {_} _.

HB.mixin Record isMonadProbDr {R : realType} (M : UU0 -> UU0) of MonadProb R M := {
  (* composition distributes rightwards over [probabilistic] choice *)
  (* WARNING: this should not be asserted as an axiom in conjunction with
     distributivity of <||> over [] *)
  prob_bindDr : (* NB: not used *)
    forall p, BindLaws.right_distributive (@bind [the monad of M]) (choice p) }.

#[short(type=probDrMonad)]
HB.structure Definition MonadProbDr {R : realType} := {M of isMonadProbDr R M & }.

HB.mixin Record isMonadAltProb {R : realType} (M : UU0 -> UU0) of MonadAltCI M & MonadProb R M :=
  { choiceDr : forall T p, right_distributive
      (@choice R [the probMonad R of M] p T) (fun a b => a [~] b) }.

#[short(type=altProbMonad)]
HB.structure Definition MonadAltProb {R : realType} :=
  { M of isMonadAltProb R M & isFunctor M & isMonad M & isMonadAlt M &
         isMonadAltCI M & isMonadProb R M }.

Section altprob_lemmas.
Context {R : realType}.
Local Open Scope proba_monad_scope.
Variable (M : altProbMonad R).
Lemma choiceDl A p :
  left_distributive (fun x y : M A => x <| p |> y) (fun x y => x [~] y).
Proof. by move=> x y z; rewrite !(choiceC p) choiceDr. Qed.
End altprob_lemmas.

HB.mixin Record isMonadExceptProb {R : realType} (M : UU0 -> UU0)
    of MonadExcept M & MonadProb R M := {
  catchDl : forall (A : UU0) w,
    left_distributive (@catch [the exceptMonad of M] A) (choice w A) }.

#[short(type=exceptProbMonad)]
HB.structure Definition MonadExceptProb {R : realType} :=
  { M of isMonadExceptProb R M & isFunctor M & isMonad M & isMonadFail M &
         isMonadExcept M & isMonadProb R M }.

HB.mixin Record isMonadFresh (S : eqType) (M : UU0 -> UU0) of Monad M :=
  { fresh : M S }.

#[short(type=freshMonad)]
HB.structure Definition MonadFresh (S : eqType) := {M of isMonadFresh S M & }.

Module segment_closed.
Record t A := mk {
  p : pred (seq A) ;
  H : forall a b, p (a ++ b) -> p a /\ p b }.
End segment_closed.
Definition segment_closed_p A := @segment_closed.p A.
Coercion segment_closed_p : segment_closed.t >-> pred.

Definition symbols {S} {M : freshMonad S} :=
  fun n => sequence (nseq n (@fresh _ M)).

HB.mixin Record isMonadFailFresh (S : eqType) (M : UU0 -> UU0)
    of MonadFresh S M & MonadFail M := Mixin {
  (* generated symbols are indeed fresh (specification of fresh) *)
  distinct : segment_closed.t S ;
  bassert_symbols : bassert distinct \o (@symbols _ [the freshMonad S of M]) =
                    @symbols _ [the freshMonad S of M] ;
  (* failure is a right zero of composition (backtracking interpretation) *)
  failfresh_bindmfail : BindLaws.right_zero (@bind [the monad of M]) (@fail _)
}.

#[short(type=failFreshMonad)]
HB.structure Definition MonadFailFresh (S : eqType) :=
  { M of isMonadFailFresh S M & isFunctor M & isMonad M & isMonadFresh S M &
         isMonadFail M }.
