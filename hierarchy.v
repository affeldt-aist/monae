Ltac typeof X := type of X.

Require Import ssrmatching Reals.
From mathcomp Require Import all_ssreflect.
From mathcomp Require boolp.
From infotheo Require Import Reals_ext.
Require Import monae_lib.

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
(*              F # g == application of functor F to the morphism g           *)
(*             F ~> G == natural transformation from functor F to functor G   *)
(*                NId == identity natural transformation                      *)
(*                 \v == vertical composition                                 *)
(*                 \h == horizontal composition                               *)
(*    Module JoinLaws == join laws of a monad                                 *)
(*              monad == type of monads                                       *)
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
(*        stateRunMonad == state + runStateT                                  *)
(*  exceptStateRunMonad == stateRun + except                                  *)
(*           reifyMonad == reify interface                                    *)
(*      stateReifyMonad == monadState + reify                                 *)
(*  failStateReifyMonad == stateReify + fail                                  *)
(*     nondetStateMonad == backtrackable state                                *)
(*           arrayMonad == array monad                                        *)
(*       loopStateMonad == (wip)                                              *)
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

Notation "f ~~> g" := (forall A, f A -> g A) (at level 51, only parsing) : monae_scope.

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

Module Functor.
Record mixin_of (M : UU0 -> UU0) := Mixin {
  actm : forall (A B : UU0), (A -> B) -> M A -> M B ;
  _ : FunctorLaws.id actm ;
  _ : FunctorLaws.comp actm }.
Structure type := Pack { acto : UU0 -> UU0 ; class : mixin_of acto }.
Module Exports.
Definition Actm (F : type) : forall (A B : UU0), (A -> B) -> acto F A -> acto F B :=
  let: Pack _ (Mixin actm _ _) := F in actm.
Arguments Actm _ [A] [B] : simpl never.
Notation "F # g" := (Actm F g) : monae_scope.
Notation "'fmap' f" := (_ # f) : mprog.
Notation functor := type.
Coercion acto : functor >-> Funclass.
End Exports.
End Functor.
Export Functor.Exports.

Section functor_lemmas.
Variable F : functor.
Lemma functor_id : FunctorLaws.id (Actm F). Proof. by case: F => [? []]. Qed.
Lemma functor_o : FunctorLaws.comp (Actm F). Proof. by case: F => [? []]. Qed.
End functor_lemmas.

Section functorid.
Definition id_f (A B : UU0) (f : A -> B) := f.
Lemma id_id : FunctorLaws.id id_f. Proof. by []. Qed.
Lemma id_comp : FunctorLaws.comp id_f. Proof. by []. Qed.
Definition FId : functor := Functor.Pack (Functor.Mixin id_id id_comp).
End functorid.

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
Definition FComp : functor :=
  Functor.Pack (Functor.Mixin functorcomposition_id functorcomposition_comp).
End functorcomposition.

Notation "f \O g" := (FComp f g) : monae_scope.

Section functorcomposition_lemmas.
Lemma FCompId f : f \O FId = f.
Proof.
case: f => [? [???]]; congr (Functor.Pack (Functor.Mixin _ _)); exact/proof_irr.
Qed.
Lemma FIdComp f : FId \O f = f.
Proof.
case: f => [? [???]]; congr (Functor.Pack (Functor.Mixin _ _)); exact/proof_irr.
Qed.
Lemma FIdf (A B : UU0) (f : A -> B) : FId # f = f. Proof. by []. Qed.
Lemma FCompA (f g h : functor) : (f \O g) \O h = f \O (g \O h).
Proof.
move: f g h => [f [???]] [g [???]] [h [???]].
congr (Functor.Pack (Functor.Mixin  _ _)); exact/proof_irr.
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
  forall (H : Functor.acto F = Functor.acto G),
  Functor.actm (Functor.class G) =
  eq_rect _ (fun m : UU0 -> UU0 => forall A B : UU0, (A -> B) -> m A -> m B) (Functor.actm (Functor.class F)) _ H  ->
  G = F.
Proof.
move: F G => [F [HF1 HF2 HF3]] [G [HG1 HG2 HG3]] /= H; subst G => /= ?; subst HG1.
congr (Functor.Pack (Functor.Mixin _ _)); exact/proof_irr.
Defined.

Definition naturality (M N : functor) (f : M ~~> N) :=
  forall (A B : UU0) (h : A -> B), (N # h) \o f A = f B \o (M # h).
Arguments naturality : clear implicits.

Module Natural.
Record mixin_of (M N : functor) (f : M ~~> N) := Mixin { _ : naturality M N f }.
Structure type (M N : functor) := Pack
  { cpnt : M ~~> N ; mixin : mixin_of cpnt }.
Module Exports.
Notation nattrans := type.
Coercion cpnt : type >-> Funclass.
Notation "f ~> g" := (nattrans f g) : monae_scope.
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
  t' = eq_rect _ (fun m => F ~> m) t _ H.
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

Module Monad.
Record mixin_of (M : functor) := Mixin {
  ret : FId ~> M ;
  join : M \O M ~> M ;
  _ : JoinLaws.left_unit ret join ;
  _ : JoinLaws.right_unit ret join ;
  _ : JoinLaws.associativity join }.
Record class_of (M : UU0 -> UU0) := Class {
  base : Functor.mixin_of M ; mixin : mixin_of (Functor.Pack base) }.
Structure type := Pack { acto : UU0 -> UU0 ; class : class_of acto }.
Definition functorType (M : type) := Functor.Pack (base (class M)).
Module Exports.
Definition RET (M : type) : FId ~> functorType M :=
  let: Pack _ (Class _ (Mixin ret _ _ _ _)) := M in ret.
Arguments RET {M} : simpl never.
Definition JOIN (M : type) : functorType M \O functorType M ~> functorType M :=
  let: Pack _ (Class _ (Mixin _ join _ _ _)) := M in join.
Arguments JOIN {M} : simpl never.
Notation monad := type.
Coercion functorType : monad >-> functor.
Canonical functorType.
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

Definition left_neutral (r : FId ~> M) :=
  forall (A B : UU0) (a : A) (f : A -> M B), r _ a >>= f = f a.

Definition right_neutral (r : forall A : UU0, A -> M A) :=
  forall A (m : M A), m >>= r _ = m.

Definition left_id (r : forall A, M A) (op : forall B, M B -> M B -> M B) :=
  forall A (m : M A), op _ (r _) m = m.

Definition right_id (r : forall A, M A) (op : forall B, M B -> M B -> M B) :=
  forall A (m : M A), op _ m (r _) = m.

End bindlaws.
End BindLaws.

Section from_join_laws_to_bind_laws.
Variable F : functor.
Variable (ret : FId ~> F) (join : F \O F ~> F).

Hypothesis joinretM : JoinLaws.left_unit ret join.
Hypothesis joinMret : JoinLaws.right_unit ret join.
Hypothesis joinA : JoinLaws.associativity join.

Let bind (A B : UU0) (m : F A) (f : A -> F B) : F B := join _ ((F # f) m).

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

Section monad_lemmas.
Variable M : monad.

Definition Bind A B (x : M A) (f : A -> M B) : M B := Join ((M # f) x).
Arguments Bind {A B} : simpl never.
Local Notation "m >>= f" := (Bind m f).
Lemma bindE (A B : UU0) : forall x (f : A -> M B), x >>= f = Join ((M # f) x).
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

Notation "'do' x <- m ; e" := (Bind m (fun x => e)) : do_notation.
Notation "'do' x : T <- m ; e" := (Bind m (fun x : T => e)) (only parsing) : do_notation.
Delimit Scope do_notation with Do.
Notation "m >>= f" := (Bind m f) : monae_scope.
Notation "m >> f" := (Bind m (fun _ => f)) : monae_scope.

Fixpoint sequence (M : monad) A (s : seq (M A)) : M (seq A) :=
  (if s isn't h :: t then Ret [::] else
  do v <- h; do vs <- sequence t; Ret (v :: vs))%Do.

Lemma sequence_nil (M : monad) (A : UU0) : sequence [::] = Ret [::] :> M (seq A).
Proof. by []. Qed.

Lemma sequence_cons (M : monad) A h (t : seq (M A)) :
  (sequence (h :: t) = do x <- h ; do vs <- sequence t ; Ret (x :: vs))%Do.
Proof. by []. Qed.

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

Tactic Notation "Inf" tactic(tac) :=
  (With (tac; reflexivity) Open (X in @Bind _ _ _ _ X = _ )) ||
  (With (tac; reflexivity) Open (X in _ = @Bind _ _ _ _ X)).

Tactic Notation "rewrite_" constr(lem) :=
  (With (rewrite lem; reflexivity) Open (X in @Bind _ _ _ _ X = _ )) ||
  (With (rewrite lem; reflexivity) Open (X in _ = @Bind _ _ _ _ X)).


Section fmap_and_join.
Variable M : monad.
Local Open Scope mprog.

Lemma fmapE (A B : UU0) (f : A -> B) (m : M _) : fmap f m = m >>= (Ret \o f).
Proof.
by rewrite bindE [in RHS]functor_o [in RHS]compE -[in RHS](compE Join) joinMret.
Qed.

Lemma bind_fmap (A B C : UU0) (f : A -> B) (m : M A) (g : B -> M C) :
  fmap f m >>= g = m >>= (g \o f).
Proof. by rewrite fmapE bindA; rewrite_ bindretf. Qed.

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

(* TODO: move? *)
Lemma foldl_revE (T R : UU0) (f : R -> T -> R) (z : R) :
  foldl f z \o rev = foldr (fun x : T => f^~ x) z.
Proof. by rewrite boolp.funeqE => s; rewrite -foldl_rev. Qed.

Lemma mfoldl_rev (T R : UU0) (f : R -> T -> R) (z : R) (s : seq T -> M (seq T)) :
  foldl f z (o) (rev (o) s) = foldr (fun x => f^~ x) z (o) s.
Proof.
rewrite boolp.funeqE => x; rewrite !fcompE 3!fmapE !bindA.
bind_ext => ?; by rewrite bindretf /= -foldl_rev.
Qed.

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

Lemma bind_kleisli (A B C : UU0) m (f : A -> M B) (g : B -> M C) :
  m >>= (f >=> g) = (m >>= f) >>= g.
Proof. by rewrite bindA; bind_ext => a; rewrite /kleisli !compE join_fmap. Qed.

Lemma ret_kleisli (A B : UU0) (k : A -> M B) : Ret >=> k = k.
Proof. by rewrite /kleisli -compA (natural RET) FIdf compA joinretM. Qed.

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

Module MonadFail.
Record mixin_of (M : monad) := Mixin {
  fail : forall A : UU0, M A ;
  (* exceptions are left-zeros of sequential composition *)
  _ : BindLaws.left_zero (@Bind M) fail (* fail A >>= f = fail B *)
}.
Record class_of (M : UU0 -> UU0) := Class {
  base : Monad.class_of M ; mixin : mixin_of (Monad.Pack base) }.
Structure type := Pack { acto : UU0 -> UU0 ; class : class_of acto }.
Definition monadType (M : type) := Monad.Pack (base (class M)).
Module Exports.
Definition Fail (M : type) : forall A, acto M A :=
  let: Pack _ (Class _ (Mixin x _)) := M in x.
Arguments Fail {M A} : simpl never.
Notation failMonad := type.
Coercion monadType : failMonad >-> monad.
Canonical monadType.
End Exports.
End MonadFail.
Export MonadFail.Exports.

Section fail_lemmas.
Variable (M : failMonad).
Lemma bindfailf : BindLaws.left_zero (@Bind M) (@Fail _).
Proof. by case : M => m [? []]. Qed.
End fail_lemmas.

Section guard_assert.
Variable M : failMonad.

Definition guard (b : bool) : M unit := locked (if b then skip else Fail).

Lemma guardPn (b : bool) : if_spec b skip Fail (~~ b) b (guard b).
Proof. by rewrite /guard; unlock; case: ifPn => ?; constructor. Qed.

Lemma guardT : guard true = skip. Proof. by rewrite /guard; unlock. Qed.

Lemma guardF : guard false = Fail. Proof. by rewrite /guard; unlock. Qed.

(* guard distributes over conjunction *)
Lemma guard_and a b : guard (a && b) = guard a >> guard b.
Proof.
move: a b => -[|] b /=; by [rewrite guardT bindskipf | rewrite guardF bindfailf].
Qed.

Definition assert {A : UU0} (p : pred A) (a : A) : M A :=
  locked (guard (p a) >> Ret a).

Lemma assertE {A : UU0} (p : pred A) (a : A) : assert p a = guard (p a) >> Ret a.
Proof. by rewrite /assert; unlock. Qed.

Lemma assertT {A : UU0} (a : A) : assert xpredT a = Ret a :> M _.
Proof. by rewrite assertE guardT bindskipf. Qed.

Lemma assertF {A : UU0} (a : A) : assert xpred0 a = Fail :> M _.
Proof. by rewrite assertE guardF bindfailf. Qed.

Lemma assertPn {A : UU0} (p : pred A) (a : A) :
  if_spec (p a) (Ret a) Fail (~~ (p a)) (p a) (assert p a).
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
Lemma guardsC (HM : BindLaws.right_zero (@Bind M) (@Fail _)) b B (m : M B) :
  guard b >> m = m >>= assert (fun=> b).
Proof.
case: guardPn => Hb.
  rewrite bindskipf.
  rewrite /assert; unlock; rewrite guardT.
  rewrite_ bindskipf.
  by rewrite bindmret.
rewrite /assert; unlock; rewrite guardF.
rewrite_ bindfailf.
by rewrite bindfailf HM.
Qed.

End guard_assert.
Arguments assert {M} {A}.
Arguments guard {M}.

Module MonadAlt.
Record mixin_of (M : monad) := Mixin {
  alt : forall T : UU0, M T -> M T -> M T
        where "a [~] b" := (alt a b) (* infix notation *) ;
  _ : forall T : UU0, associative (@alt T) ;
  (* composition distributes leftwards over choice *)
  _ : BindLaws.left_distributive (@Bind M) alt }.
(* in general, composition does not distribute rightwards over choice *)
(* NB: no bindDr to accommodate both angelic and demonic interpretations of nondeterminism *)
Record class_of (M : UU0 -> UU0) := Class {
  base : Monad.class_of M ; mixin : mixin_of (Monad.Pack base) }.
Structure type := Pack { acto : UU0 -> UU0 ; class : class_of acto }.
Definition monadType (M : type) := Monad.Pack (base (class M)).
Module Exports.
Definition Alt M : forall T, acto M T -> acto M T -> acto M T :=
  let: Pack _ (Class _ (Mixin x _ _)) := M in x.
Arguments Alt {M T} : simpl never.
Notation "x '[~]' y" := (Alt x y).
Notation altMonad := type.
Coercion monadType : altMonad >-> monad.
Canonical monadType.
End Exports.
End MonadAlt.
Export MonadAlt.Exports.

Section monadalt_lemmas.
Variable (M : altMonad).
Lemma alt_bindDl : BindLaws.left_distributive (@Bind M) (@Alt M).
Proof. by case: M => m [? []]. Qed.
Lemma altA : forall A, associative (@Alt M A).
Proof. by case: M => m [? []]. Qed.
End monadalt_lemmas.

Module MonadAltCI.
Record mixin_of (M : UU0 -> UU0) (op : forall A, M A -> M A -> M A) :=
  Mixin { _ : forall A : UU0, idempotent (op A) ;
          _ : forall A : UU0, commutative (op A) }.
Record class_of (M : UU0 -> UU0) := Class {
  base : MonadAlt.class_of M ;
  mixin : mixin_of (@Alt (MonadAlt.Pack base)) }.
Structure type := Pack { acto : UU0 -> UU0 ; class : class_of acto }.
Definition altMonadType (M : type) := MonadAlt.Pack (base (class M)).
Module Exports.
Notation altCIMonad := type.
Coercion altMonadType : altCIMonad >-> altMonad.
Canonical altMonadType.
End Exports.
End MonadAltCI.
Export MonadAltCI.Exports.

Section altci_lemmas.
Variable (M : altCIMonad).
Lemma altmm : forall A, idempotent (@Alt _ A : M A -> M A -> M A).
Proof. by case: M => m [? []]. Qed.
Lemma altC : forall A, commutative (@Alt _ A : M A -> M A -> M A).
Proof. by case: M => m [? []]. Qed.
Lemma altCA A : @left_commutative (M A) (M A) (fun x y => x [~] y).
Proof. move=> x y z. by rewrite altA altC altA altC (altC z). Qed.
Lemma altAC A : @right_commutative (M A) (M A) (fun x y => x [~] y).
Proof. move=> x y z; by rewrite altC altA (altC x). Qed.
Lemma altACA A : @interchange (M A) (fun x y => x [~] y) (fun x y => x [~] y).
Proof. move=> x y z t; rewrite !altA; congr (_ [~] _); by rewrite altAC. Qed.
End altci_lemmas.

Module MonadNondet.
Record mixin_of (M : failMonad) (a : forall A, M A -> M A -> M A) :=
  Mixin { _ : @BindLaws.left_id M (@Fail M) a ;
          _ : @BindLaws.right_id M (@Fail M) a }.
Record class_of (M : UU0 -> UU0) := Class {
  base : MonadFail.class_of M ;
  mixin_alt : MonadAlt.mixin_of (Monad.Pack (MonadFail.base base)) ;
  mixin_nondet : @mixin_of (MonadFail.Pack base) (MonadAlt.alt mixin_alt) }.
Structure type := Pack { acto : UU0 -> UU0 ; class : class_of acto }.
Definition failMonadType (M : type) := MonadFail.Pack (base (class M)).
Definition altMonadType (M : type) :=
  MonadAlt.Pack (MonadAlt.Class (mixin_alt (class M))).
Module Exports.
Notation nondetMonad := type.
Coercion failMonadType : nondetMonad >-> failMonad.
Canonical failMonadType.
Canonical altMonadType.
End Exports.
End MonadNondet.
Export MonadNondet.Exports.

Section nondet_lemmas.
Variable (M : nondetMonad).
Lemma altmfail : @BindLaws.right_id M (@Fail M) (@Alt _).
Proof. by case: M => m [[? ?] [? ? ?] [? ?]]. Qed.
Lemma altfailm : @BindLaws.left_id M (@Fail M) (@Alt _). (* NB: not used? *)
Proof. by case: M => m [[? ?] [? ? ?] [? ?]]. Qed.
End nondet_lemmas.

Module MonadCINondet.
Record class_of (m : UU0 -> UU0) := Class {
  base : MonadNondet.class_of m ;
  mixin : MonadAltCI.mixin_of
    (@Alt (MonadAlt.Pack (MonadAlt.Class (MonadNondet.mixin_alt base)))) }.
Structure type := Pack { acto : UU0 -> UU0 ; class : class_of acto }.
Definition nondetMonadType (M : type) := MonadNondet.Pack (base (class M)).
Definition altCIMonadType (M : type) :=
  MonadAltCI.Pack (MonadAltCI.Class (mixin (class M))).
Module Exports.
Notation nondetCIMonad := type.
Coercion nondetMonadType : nondetCIMonad >-> nondetMonad.
Canonical nondetMonadType.
Canonical altCIMonadType.
End Exports.
End MonadCINondet.
Export MonadCINondet.Exports.

Section nondet_big.
Variables (M : nondetMonad) (A : UU0).
Canonical alt_monoid :=
  Monoid.Law (@altA (MonadNondet.altMonadType M) A) (@altfailm _ _) (@altmfail _ _).

Lemma test_bigop n : \big[Alt/Fail]_(i < n) (Fail : M A) = Fail.
Proof.
elim: n => [|n IH]; first by rewrite big_ord0.
by rewrite big_ord_recr /= IH altmfail.
Qed.

End nondet_big.

Module MonadFailR0.
Record mixin_of (M : failMonad) := Mixin {
  _ : BindLaws.right_zero (@Bind M) (@Fail _) }.
Record class_of (M : UU0 -> UU0) := Class {
  base : MonadFail.class_of M ;
  mixin : mixin_of (MonadFail.Pack base) }.
Structure type := Pack { acto : UU0 -> UU0 ; class : class_of acto }.
Definition failR0MonadType (M : type) := MonadFail.Pack (base (class M)).
Module Exports.
Notation failR0Monad := type.
Coercion failR0MonadType : failR0Monad >-> failMonad.
Canonical failR0MonadType.
End Exports.
End MonadFailR0.
Export MonadFailR0.Exports.

Section failR0_lemmas.
Variable (M : failR0Monad).
Lemma bindmfail : BindLaws.right_zero (@Bind M) (@Fail _).
Proof. by case: M => m [? [? ?]]. Qed.
End failR0_lemmas.

Module MonadPrePlus.
Record mixin_of (M : nondetMonad) := Mixin {
  _ : BindLaws.right_distributive (@Bind M) (@Alt _) }.
Record class_of (M : UU0 -> UU0) := Class {
  base : MonadNondet.class_of M ;
  mixin_failR0 : MonadFailR0.mixin_of (MonadFail.Pack (MonadNondet.base base)) ;
  mixin : mixin_of (MonadNondet.Pack base) }.
Structure type := Pack { acto : UU0 -> UU0 ; class : class_of acto }.
Definition prePlusMonadType (M : type) := MonadNondet.Pack (base (class M)).
Definition failR0MonadType (M : type) := MonadFailR0.Pack (MonadFailR0.Class (mixin_failR0 (class M))).
Module Exports.
Notation prePlusMonad := type.
Coercion prePlusMonadType : prePlusMonad >-> nondetMonad.
Canonical prePlusMonadType.
Coercion failR0MonadType : prePlusMonad >-> failR0Monad.
Canonical failR0MonadType.
End Exports.
End MonadPrePlus.
Export MonadPrePlus.Exports.

Section pre_plus_lemmas.
Variable (M : prePlusMonad).
Lemma alt_bindDr : BindLaws.right_distributive (@Bind M) (@Alt _).
Proof. by case: M => m [? ? []]. Qed.
End pre_plus_lemmas.

Module MonadPlus.
Record class_of (M : UU0 -> UU0) := Class {
  base : MonadCINondet.class_of M ;
  mixin_failR0 : MonadFailR0.mixin_of (MonadCINondet.Pack base) ;
  mixin_preplus : MonadPrePlus.mixin_of (MonadCINondet.Pack base) }.
Structure type := Pack { acto : UU0 -> UU0 ; class : class_of acto }.
Definition plusMonadType (M : type) := MonadCINondet.Pack (base (class M)).
Definition preplus_of_plus (M : type) :=
  MonadPrePlus.Pack (@MonadPrePlus.Class _ (MonadCINondet.base (base (class M)))(*IMP*) (mixin_failR0 (class M)) (mixin_preplus (class M))).
Module Exports.
Notation plusMonad := type.
Coercion plusMonadType : plusMonad >-> nondetCIMonad.
Canonical plusMonadType.
Coercion preplus_of_plus : plusMonad >-> prePlusMonad.
Canonical preplus_of_plus.
End Exports.
End MonadPlus.
Export MonadPlus.Exports.

Module MonadExcept.
Record mixin_of (M : failMonad) := Mixin {
  catch : forall A, M A -> M A -> M A ;
  (* monoid *)
  _ : forall A, right_id Fail (@catch A) ;
  _ : forall A, left_id Fail (@catch A) ;
  _ : forall A, associative (@catch A) ;
  (* unexceptional bodies need no handler *)
  _ : forall A x, @left_zero (M A) (M A) (Ret x) (@catch A)
  (* NB: left-zero of sequential composition inherited from failMonad *) }.
Record class_of (M : UU0 -> UU0) := Class {
  base : MonadFail.class_of M ;
  mixin : mixin_of (MonadFail.Pack base) }.
Structure type := Pack { acto : UU0 -> UU0 ; class : class_of acto }.
Definition failMonadType M := MonadFail.Pack (base (class M)).
Definition monadType M := Monad.Pack (MonadFail.base (base (class M))).
Module Exports.
Definition Catch (M : type) : forall A, acto M A -> acto M A -> acto M A :=
  let: Pack _ (Class _ (Mixin x _ _ _ _)) := M in x.
Arguments Catch {M A} : simpl never.
Notation exceptMonad := type.
Coercion failMonadType : exceptMonad >-> failMonad.
Canonical failMonadType.
Canonical monadType.
End Exports.
End MonadExcept.
Export MonadExcept.Exports.

Section except_lemmas.
Variables (M : exceptMonad).
Lemma catchfailm : forall A, left_id Fail (@Catch M A).
Proof. by case: M => m [? []]. Qed.
Lemma catchmfail : forall A, right_id Fail (@Catch M A). (* NB: not used? *)
Proof. by case: M => m [? []]. Qed.
Lemma catchret : forall A x, left_zero (Ret x) (@Catch M A).
Proof. by case: M => m [? []]. Qed.
Lemma catchA : forall A, associative (@Catch M A). (* NB: not used? *)
Proof. by case: M => m [? []]. Qed.
End except_lemmas.

Module MonadContinuation.
(* NB: interface is wip *)
Record mixin_of (M : monad) := Mixin {
   callcc : forall A B : UU0, ((A -> M B) -> M A) -> M A;
   _ : forall (A B : UU0) (g : (A -> M B) -> M A) (k : B -> M B),
       callcc (fun f => g (fun x => f x >>= k)) = callcc g; (* see Sect. 7.2 of [Schrijvers, 19] *)
   _ : forall (A B : UU0) (m : M B), callcc (fun _ : B -> M A => m) = m ; (* see Sect. 3.3 of [Wadler, 94] *)
   _ : forall (A B C : UU0) (m : M A) x (k : A -> B -> M C),
       callcc (fun f : _ -> M _ => m >>= (fun a => f x >>= (fun b => k a b))) =
       callcc (fun f : _ -> M _ => m >> f x) ;
   _ : forall (A B : UU0) (m : M A) b,
       callcc (fun f : B -> M B => m >> f b) =
       callcc (fun _ : B -> M B => m >> Ret b) }.
Record class_of (M : UU0 -> UU0) := Class {
  base : Monad.class_of M ; mixin : mixin_of (Monad.Pack base) }.
Structure type := Pack { acto : UU0 -> UU0 ; class : class_of acto }.
Definition monadType (M : type) := Monad.Pack (base (class M)).
Module Exports.
Definition Callcc (M : type) : forall A B : UU0, ((A -> acto M B) -> acto M A) -> acto M A :=
  let: Pack _ (Class _ (Mixin x _ _ _ _)) := M in x.
Notation contMonad := type.
Coercion monadType : contMonad >-> monad.
Canonical monadType.
End Exports.
End MonadContinuation.
Export MonadContinuation.Exports.

Section continuation_lemmas.
Variables (M : contMonad).
Lemma callcc0 (A B : UU0) (g : (A -> M B) -> M A) (k : B -> M B) :
  Callcc (fun f => g (fun x => f x >>= k)) = Callcc g.
Proof. by case: M A B g k => m [? []]. Qed.
Lemma callcc1 (A B : UU0) p : Callcc (fun _ : B -> M A => p) = p.
Proof. by case: M A B p => m [? []]. Qed.
Lemma callcc2 (A B C : UU0) (m : M A) x (k : A -> B -> M C) :
  (Callcc (fun f : _ -> M _ => do a <- m; do b <- f x; k a b) =
   Callcc (fun f : _ -> M _ => m >> f x))%Do.
Proof. by case: M A B C m x k => m [? []]. Qed.
Lemma callcc3 (A B : UU0) (m : M A) b :
  Callcc (fun f : B -> M B => m >> f b) = Callcc (fun _ : B -> M B => m >> Ret b).
Proof. by case: M A B m b => m [? []]. Qed.
End continuation_lemmas.

Module MonadShiftReset.
(* NB: interface is wip *)
Record mixin_of (M : contMonad) U := Mixin {
  shift : forall A : UU0, ((A -> M U) -> M U) -> M A ;
  reset : M U -> M U ;
  _ : forall (A : UU0) (m : M A), shift (fun k => m >>= k) = m ; (* see Sect. 3.3 of [Wadler, 94] *)
  _ : forall (A B : UU0) (h : (A -> M B) -> M A),
    Callcc h = shift (fun k' => h (fun x => shift (fun k'' => k' x)) >>= k')  ; (* see Sect. 3.3 of [Wadler, 94] *)
  _ : forall (A : UU0) (c : A) (c': U) (k : A -> U -> _),
    (reset (do x <- Ret c; do y <- shift (fun _ => Ret c'); k x y) = Ret c >> Ret c')%Do ;
  _ : forall (c c' : U) (k : U -> U -> _),
    (reset (do x <- Ret c; do y <- shift (fun f => do v <- f c'; f v); Ret (k x y)) =
     reset (do x <- Ret c; do y <- shift (fun f => f c'); Ret (k x (k x y))))%Do ;
  _ : forall (c : U) k,
    (reset (do y <- shift (@^~ c); Ret (k y)) = Ret (k c))%Do
}.
Record class_of (M : UU0 -> UU0) B := Class {
  base : MonadContinuation.class_of M ;
  mixin : mixin_of (MonadContinuation.Pack base) B }.
Structure type B := Pack { acto : UU0 -> UU0 ; class : class_of acto B }.
Definition contMonadType B (M : type B) := MonadContinuation.Pack (base (class M)).
Module Exports.
Definition Shift B (M : type B) : forall A : UU0, ((A -> acto M B) -> acto M B) -> acto M A :=
  let: Pack _ (Class _ (Mixin x _ _ _ _ _ _)) := M in x.
Definition Reset B (M : type B) : acto M B -> acto M B :=
  let: Pack _ (Class _ (Mixin _ x _ _ _ _ _)) := M in x.
Notation shiftresetMonad := type.
Coercion contMonadType : shiftresetMonad >-> contMonad.
Canonical contMonadType.
End Exports.
End MonadShiftReset.
Export MonadShiftReset.Exports.

Section shiftreset_lemmas.
Variables (U : UU0) (M : shiftresetMonad U).
Lemma shiftreset0 (A : UU0) (m : M A) : Shift (fun k => m >>= k) = m.
Proof. by case: M A m => m [? []]. Qed.
Lemma shiftreset1 (A B : UU0) (h : (A -> M B) -> M A) :
  Callcc h = Shift (fun k' => h (fun x => Shift (fun k'' => k' x)) >>= k').
Proof. by case: M A B h => m [? []]. Qed.
Lemma shiftreset2 (A : UU0) c c' (k : A -> U -> _):
  Reset (do x <- Ret c; do y <- (Shift (fun _ => @RET M U c') : M U); k x y)%Do =
    (Ret c >> Ret c') :> M _ .
Proof. by case: M c c' k => m [? []]. Qed.
Lemma shiftreset3 c c' (k : U -> U -> _) :
  (Reset (do x <- Ret c; do y <- (Shift (fun f : U -> M U => do v <- f c'; f v) : M U); Ret (k x y)) =
  Reset (do x <- Ret c; do y <- (Shift (fun f : U -> M U => f c') : M U); Ret (k x (k x y))))%Do.
Proof. by case: M c c' k => m [? []]. Qed.
Lemma shiftreset4 c k:
  Reset ((Shift (@^~ c) : M U) >>= (fun y => Ret (k y))) = Ret (k c) :> M U.
Proof. by case: M c => m [? []]. Qed.
End shiftreset_lemmas.

(* NB: wip, no model *)
Module MonadJump.
(* Sect. 7.2 of [Tom Schrijvers & al., Monad Transformers and Modular
Algebraic Eﬀects: What Binds Them Together, Haskell 2019] *)
Record mixin_of (ref : UU0 -> UU0) (M : monad) := Mixin {
   jump : forall A B : UU0, ref A -> A -> M B;
   sub : forall A B : UU0, (ref A -> M B) -> (A -> M B) -> M B;
   _ : forall (A B : UU0) k x, sub (fun r => @jump A B r x) k = k x;
   _ : forall (A B : UU0) p k, @sub A B (fun _ => p) k = p;
   _ : forall (A B : UU0) p r', sub p (@jump A B r') = p r';
   _ : forall (A B : UU0) (p : ref A -> ref B -> M B) (k1 : A -> M B) k2,
       sub (fun r1 : ref A => sub (fun r2 => p r1 r2) (k2 r1)) k1 =
       sub (fun r2 : ref B => sub (fun r1 => p r1 r2) k1) (fun x => sub (k2^~x) k1); (*NB: differs from [Schrijvers et al. 19]*)
   _ : forall (A B : UU0) r x k, (@jump A B r x) >>= k = @jump A B r x;
   _ : forall (A B : UU0) p q k, @sub A B p q >>= k = @sub A B (p >=> k) (q >=> k)
}.
Record class_of ref (M : UU0 -> UU0) := Class {
  base : Monad.class_of M ; mixin : mixin_of ref (Monad.Pack base) }.
Structure type ref := Pack { acto : UU0 -> UU0 ; class : class_of ref acto }.
Definition monadType ref (M : type ref) := Monad.Pack (base (class M)).
Module Exports.
Definition Jump ref (M : type ref) : forall A B, ref A -> A -> acto M B :=
  let: Pack _ (Class _ (Mixin x _ _ _ _ _ _ _)) := M in x.
Arguments Jump {ref M A B} : simpl never.
Definition Sub ref (M : type ref)
    : forall A B, (ref A -> acto M B) -> (A -> acto M B) -> acto M B :=
  let: Pack _ (Class _ (Mixin _ x _ _ _ _ _ _)) := M in x.
Arguments Sub {ref M A B} : simpl never.
Notation jumpMonad := type.
Coercion monadType : jumpMonad >-> monad.
Canonical monadType.
End Exports.
End MonadJump.
Export MonadJump.Exports.

Module MonadState.
Record mixin_of (S : UU0) (M : monad) := Mixin {
  get : M S ;
  put : S -> M unit ;
  _ : forall s s', put s >> put s' = put s' ;
  _ : forall s, put s >> get = put s >> Ret s ;
  _ : get >>= put = skip ;
  _ : forall (A : UU0) (k : S -> S -> M A),
    get >>= (fun s => get >>= k s) = get >>= fun s => k s s }.
Record class_of (S : UU0) (m : UU0 -> UU0) := Class {
  base : Monad.class_of m ; mixin : mixin_of S (Monad.Pack base) }.
Structure type (S : UU0) := Pack { acto : UU0 -> UU0 ; class : class_of S acto }.
Definition monadType (S : UU0) (M : type S) := Monad.Pack (base (class M)).
Module Exports.
Definition Get (S : UU0) (M : type S) : acto M S :=
  let: Pack _ (Class _ (Mixin x _ _ _ _ _)) := M in x.
Arguments Get {S M} : simpl never.
Definition Put (S : UU0) (M : type S) : S -> acto M unit :=
  let: Pack _ (Class _ (Mixin _ x _ _ _ _)) := M in x.
Arguments Put {S M} : simpl never.
Notation stateMonad := type.
Coercion monadType : stateMonad >-> monad.
Canonical monadType.
End Exports.
End MonadState.
Export MonadState.Exports.

Section state_lemmas.
Variables (S : UU0) (M : stateMonad S).
Lemma putput s s' : Put s >> Put s' = Put s' :> M _.
Proof. by case: M => m [[[? ? ? ? []]]]. Qed.
Lemma putget s : Put s >> Get = Put s >> Ret s :> M _.
Proof. by case: M => m [[[? ? ? ? []]]]. Qed.
Lemma getputskip : Get >>= Put = skip :> M _.
Proof.  by case: M => m [[[? ? ? ? []]]]. Qed.
Lemma getget (A : UU0) (k : S -> S -> M A) :
 (Get >>= (fun s => Get >>= k s)) = (Get >>= fun s => k s s).
Proof. by case: M k => m [[[? ? ? ? []]]]. Qed.
End state_lemmas.

Module MonadStateRun.
Local Open Scope type_scope.
Record mixin_of (S : UU0) (N : monad) (M : stateMonad S) := Mixin {
  runStateT : forall A : UU0, M A -> S -> N (A * S) ;
  _ : forall (A : UU0) (a : A) (s : S), runStateT (Ret a) s = Ret (a, s) ;
  _ : forall (A B : UU0) (m : M A) (f : A -> M B) (s : S),
    runStateT (m >>= f) s = runStateT m s >>= fun x => runStateT (f x.1) x.2 ;
  _ : forall s : S, runStateT Get s = Ret (s, s) ;
  _ : forall s' s : S, runStateT (Put s') s = Ret (tt, s') }.
Record class_of (S : UU0) (N : monad) (m : UU0 -> UU0) := Class {
  base : MonadState.class_of S m ;
  mixin : @mixin_of S N (MonadState.Pack base) }.
Structure type (S : UU0) (N : monad) := Pack {
  acto : UU0 -> UU0 ; class : class_of S N acto }.
Definition stateMonadType (S : UU0) (N : monad) (M : type S N) : stateMonad S :=
  MonadState.Pack (base (class M)).
Module Exports.
Notation stateRunMonad := type.
Definition RunStateT (S : UU0) (N : monad) (M : stateRunMonad S N)
    : forall A : UU0, acto M A -> S -> N (A * S) :=
  let: Pack _ (Class _ (Mixin x _ _ _ _)) := M in x.
Arguments RunStateT {S N M A} : simpl never.
Coercion stateMonadType : stateRunMonad >-> stateMonad.
Canonical stateMonadType.
End Exports.
Local Close Scope type_scope.
End MonadStateRun.
Export MonadStateRun.Exports.

Section staterun_lemmas.
Local Open Scope type_scope.
Variables (S : UU0) (N : monad) (M : stateRunMonad S N).
Lemma RunStateTRet (A : UU0) (a : A) (s : S) :
  RunStateT (Ret a : M _) s = Ret (a, s).
Proof. by case: M => ? [? []]. Qed.
Lemma RunStateTBind (A B : UU0) (m : M A) (f : A -> M B) (s : S) :
  RunStateT (m >>= f) s = RunStateT m s >>= fun x => RunStateT (f x.1) x.2.
Proof. by case: M m f => ? [? []]. Qed.
Lemma RunStateTGet (s : S) : RunStateT (Get : M _) s = Ret (s, s).
Proof. by case: M s => ? [? []]. Qed.
Lemma RunStateTPut (s' s : S) : RunStateT (Put s' : M _) s = Ret (tt, s').
Proof. by case: M s => ? [? []]. Qed.
Local Close Scope type_scope.
End staterun_lemmas.

Module MonadExceptStateRun.
Section monadexceptstaterun.
Variable S : UU0.
Record mixin_of (N : exceptMonad) (M : stateRunMonad S N)
    (fail : forall A : UU0, M A)
    (catch : forall A : UU0, M A -> M A -> M A) := Mixin {
  _ : forall (A : UU0) (s : S), RunStateT (@fail A) s = @Fail N _ ;
  _ : forall (A : UU0) (s : S) (m1 m2 : M A),
      RunStateT (catch _ m1 m2) s = Catch (RunStateT m1 s) (RunStateT m2 s) }.
Record class_of (N : exceptMonad) (m : UU0 -> UU0) := Class {
  base : MonadExcept.class_of m ;
  mixin_state : MonadState.mixin_of S (Monad.Pack (MonadFail.base (MonadExcept.base base))) ;
  mixin_stateRun : MonadStateRun.mixin_of
    (Monad.Pack (MonadFail.base (MonadFail.class N)))
    (MonadState.Pack (MonadState.Class mixin_state)) ;
  mixin : @mixin_of N (MonadStateRun.Pack (MonadStateRun.Class mixin_stateRun))
    (@Fail (MonadFail.Pack (MonadExcept.base base)))
    (@Catch (MonadExcept.Pack base)) }.
Structure type (N : exceptMonad) := Pack {
  acto : UU0 -> UU0 ; class : class_of N acto }.
Definition exceptMonadType (N : exceptMonad) (M : type N) : exceptMonad :=
  MonadExcept.Pack (base (class M)).
End monadexceptstaterun.
Module Exports.
Notation exceptStateRunMonad := type.
Coercion exceptMonadType : exceptStateRunMonad >-> exceptMonad.
Canonical exceptMonadType.
Definition state_of_exceptStateRun (S : UU0) (N : exceptMonad) (M : type S N) : stateMonad S :=
  MonadState.Pack (MonadState.Class (mixin_state (class M))).
Canonical state_of_exceptStateRun.
Coercion state_of_exceptStateRun : exceptStateRunMonad >-> stateMonad.
Definition stateRun_of_exceptStateRun (S : UU0) (N : exceptMonad) (M : type S N) : stateRunMonad S N :=
  MonadStateRun.Pack (MonadStateRun.Class (mixin_stateRun (class M))).
Canonical stateRun_of_exceptStateRun.
Coercion stateRun_of_exceptStateRun : exceptStateRunMonad >-> stateRunMonad.
End Exports.
End MonadExceptStateRun.
Export MonadExceptStateRun.Exports.

Section exceptstaterun_lemmas.
Variables (S : UU0) (N : exceptMonad) (M : exceptStateRunMonad S N).
Lemma RunStateTFail (A : UU0) (s : S) :
  RunStateT (Fail : M _) s = Fail :> N (A * S)%type.
Proof. by case: M s => ? [? ? ? []]. Qed.
Lemma RunStateTCatch (A : UU0) (s : S) (m1 m2 : M A) :
  RunStateT (Catch m1 m2) s = Catch (RunStateT m1 s) (RunStateT m2 s).
Proof. by case: M s m1 m2 => ? [? ? ? []]. Qed.
End exceptstaterun_lemmas.

Module MonadReify.
Record mixin_of (S : UU0) (M : monad) := Mixin {
  reify : forall A : UU0, M A -> S -> option (A * S) ;
  _ : forall (A : UU0) (a : A) s, reify (Ret a) s = Some (a, s) ;
  _ : forall (A B : UU0) (m : M A) (f : A -> M B) s,
      reify (m >>= f) s = if reify m s is Some (a', s') then reify (f a') s' else None}.
Record class_of (S : UU0) (M : UU0 -> UU0) := Class {
  base : Monad.class_of M ;
  mixin : mixin_of S (Monad.Pack base) }.
Structure type (S : UU0) := Pack { acto : UU0 -> UU0 ; class : class_of S acto }.
Definition monadType (S : UU0) (M : type S) := Monad.Pack (base (class M)).
Module Exports.
Definition Reify (S : UU0) (M : type S) : forall A : UU0, acto M A -> S -> option (A * S) :=
  let: Pack _ (Class _ (Mixin x _ _)) := M in x.
Arguments Reify {S M A} : simpl never.
Notation reifyMonad := type.
Coercion monadType : reifyMonad >-> monad.
Canonical monadType.
End Exports.
End MonadReify.
Export MonadReify.Exports.

Section reify_lemmas.
Variables (S : UU0) (M : reifyMonad S).
Lemma reifyret : forall (A : UU0) (a : A) s, Reify (Ret a : M _) s = Some (a, s).
Proof. by case: M => m [? []]. Qed.
Lemma reifybind : forall (A B : UU0) (m : M A) (f : A -> M B) s,
  Reify (m >>= f) s = if Reify m s is Some (a', s') then Reify (f a') s' else None.
Proof. by case: M => m [? []]. Qed.
End reify_lemmas.

Module MonadStateReify.
Record mixin_of (S : UU0) (M : reifyMonad S) (get : M S) (put : S -> M unit) : UU0
  := Mixin {
  _ : forall s, Reify get s = Some (s, s) ;
  _ : forall s s', Reify (put s') s = Some (tt, s') }.
Record class_of (S : UU0) (M : UU0 -> UU0) := Class {
  base : MonadReify.class_of S M ;
  mixin_state : MonadState.mixin_of S (Monad.Pack (MonadReify.base base)) ;
  mixin_stateReify : @mixin_of S (MonadReify.Pack base)
    (@Get _ (MonadState.Pack (MonadState.Class mixin_state))) (@Put _ (MonadState.Pack (MonadState.Class mixin_state))) ;
}.
Structure type (S : UU0) := Pack { acto : UU0 -> UU0 ; class : class_of S acto }.
Definition reifyMonadType (S : UU0) (M : type S) := MonadReify.Pack (base (class M)).
Definition state_of_stateReify (S : UU0) (M : type S) :=
  MonadState.Pack (MonadState.Class (mixin_state (class M))).
Module Exports.
Notation stateReifyMonad := type.
Coercion reifyMonadType : stateReifyMonad >-> reifyMonad.
Canonical reifyMonadType.
Coercion state_of_stateReify : stateReifyMonad >-> stateMonad.
Canonical state_of_stateReify.
End Exports.
End MonadStateReify.
Export MonadStateReify.Exports.

Section statereify_lemmas.
Variables (S : UU0) (M : stateReifyMonad S).
Lemma reifyget : forall s, Reify (Get : M _) s = Some (s, s).
Proof. by case: M => m [? ? []]. Qed.
Lemma reifyput : forall s s', Reify (Put s' : M _) s = Some (tt, s').
Proof. by case: M => m [? ? []]. Qed.
End statereify_lemmas.

Module MonadFailReify.
Record mixin_of (S : UU0) (M : reifyMonad S) (fail : forall S' : UU0, M S') : UU0 := Mixin {
  _ : forall S' (s : S), Reify (fail S') s = None }.
Record class_of (S : UU0) (M : UU0 -> UU0) := Class {
  base : MonadReify.class_of S M ;
  mixin_fail : MonadFail.mixin_of (Monad.Pack (MonadReify.base base)) ;
  mixin_failreify : @mixin_of S (MonadReify.Pack base) (@Fail (MonadFail.Pack (MonadFail.Class mixin_fail)))
 }.
Structure type (S : UU0) := Pack { acto : UU0 -> UU0 ; class : class_of S acto }.
Definition failReifyMonadType (S : UU0) (M : type S) := MonadReify.Pack (base (class M)).
Definition fail_of_failReify (S : UU0) (M : type S) :=
  MonadFail.Pack (MonadFail.Class (mixin_fail (class M))).
Module Exports.
Notation failReifyMonad := type.
Coercion failReifyMonadType : failReifyMonad >-> reifyMonad.
Canonical failReifyMonadType.
Coercion fail_of_failReify : failReifyMonad >-> failMonad.
Canonical fail_of_failReify.
End Exports.
End MonadFailReify.
Export MonadFailReify.Exports.

Section failreify_lemmas.
Variables (S : UU0) (M : failReifyMonad S).
Lemma reifyfail : forall S' s, Reify (Fail : M S') s = None.
Proof. by case: M => m [? ? []]. Qed.
End failreify_lemmas.

Module MonadFailFailR0Reify.
Record class_of (S : UU0) (M : UU0 -> UU0) := Class {
  base : MonadFailReify.class_of S M ;
  mixin_failR0 : MonadFailR0.mixin_of (MonadFail.Pack (MonadFail.Class (MonadFailReify.mixin_fail base))) }.
Structure type (S : UU0) := Pack { acto : UU0 -> UU0 ; class : class_of S acto }.
Definition failFailR0ReifyMonadType (S : UU0) (M : type S) := MonadFailReify.Pack (base (class M)).
Definition failR0_of_failFailR0Reify (S : UU0) (M : type S) :=
  @MonadFailR0.Pack _ (MonadFailR0.Class (mixin_failR0 (class M))).
Module Exports.
Notation failFailR0ReifyMonad := type.
Coercion failFailR0ReifyMonadType : failFailR0ReifyMonad >-> failReifyMonad.
Canonical failFailR0ReifyMonadType.
Coercion failR0_of_failFailR0Reify : failFailR0ReifyMonad >-> failR0Monad.
Canonical failR0_of_failFailR0Reify.
End Exports.
End MonadFailFailR0Reify.
Export MonadFailFailR0Reify.Exports.

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
Export MonadFailStateReify.Exports.

Module MonadNondetState.
(*Record mixin_of (M : nondetMonad) := Mixin {
  (* backtrackable state *)
  _ : BindLaws.right_zero (@Bind M) (@Fail _) ;
  (* composition distributes rightwards over choice *)
  _ : BindLaws.right_distributive (@Bind M) (@Alt _) }.*)
Record class_of (S : UU0) (M : UU0 -> UU0) := Class {
  base : MonadPrePlus.class_of M ;
  mixin_state : MonadState.mixin_of S (MonadFail.monadType (MonadNondet.failMonadType (MonadPrePlus.Pack base)))
(*  mixin_nondetState : mixin_of (MonadNondet.Pack base)*)
}.
Structure type (S : UU0) := Pack { acto : UU0 -> UU0 ; class : class_of S acto }.
Definition prePlusMonadType (S : UU0) (M : type S) := MonadPrePlus.Pack (base (class M)).
Definition stateMonadType (S : UU0) (M : type S) :=
  MonadState.Pack (MonadState.Class (mixin_state (class M))).
Module Exports.
Notation nondetStateMonad := type.
Coercion prePlusMonadType : nondetStateMonad >-> prePlusMonad.
Canonical prePlusMonadType.
Canonical stateMonadType.
End Exports.
End MonadNondetState.
Export MonadNondetState.Exports.

(*Section nondetstate_lemmas.
Variables (S : UU0) (M : nondetStateMonad S).
Lemma bindmfail : BindLaws.right_zero (@Bind M) (@Fail _).
Proof. by case: M => m [? ? [? ?]]. Qed.
Lemma alt_bindDr : BindLaws.right_distributive (@Bind M) (@Alt _).
Proof. by case: M => m [? ? []]. Qed.
End nondetstate_lemmas.*)

(* NB: this is experimental, may disappear, see rather foreah in
monad_transformer because it is more general *)
Module MonadStateLoop.
Record mixin_of (S : UU0) (M : stateMonad S) := Mixin {
   foreach : nat -> nat -> (nat -> M unit) -> M unit ;
  _ : forall m body, foreach m m body = Ret tt ;
  _ : forall m n body, foreach (m.+1 + n) m body =
     (body (m + n)) >> foreach (m + n) m body :> M unit }.
Record class_of (S : UU0) (M : UU0 -> UU0) := Class {
  base : MonadState.class_of S M ;
  mixin : mixin_of (MonadState.Pack base)}.
Structure type (S : UU0) := Pack { acto : UU0 -> UU0 ; class : class_of S acto }.
Definition stateMonadType (S : UU0) (M : type S) : stateMonad S :=
  MonadState.Pack (base (class M)).
Module Exports.
Notation loopStateMonad := type.
Definition Foreach (S : UU0) (M : loopStateMonad S) : nat -> nat -> (nat -> acto M unit) -> acto M unit :=
  let: Pack _ (Class _ (Mixin x _ _)) := M in x.
Coercion stateMonadType : loopStateMonad >-> stateMonad.
Canonical stateMonadType.
End Exports.
End MonadStateLoop.
Export MonadStateLoop.Exports.

Section stateloop_lemmas.
Variables (S : UU0) (M : loopStateMonad S).
Lemma loop0 m (body : nat -> M unit) :
  Foreach m m body = Ret tt :> M _.
Proof. by case: M body => ? [? []]. Qed.
Lemma loop1 m n body :
  Foreach (m.+1 + n) m body =
  (body (m + n) : M _) >> Foreach (m + n) m body :> M unit.
Proof. by case: M body => ? [? []]. Qed.
End stateloop_lemmas.

Module MonadArray.
Record mixin_of (S : UU0) (I : eqType) (M : monad) := Mixin {
  get : I -> M S ;
  put : I -> S -> M unit ;
  _ : forall i s s', put i s >> put i s' = put i s' ;
  _ : forall i s (A : UU0) (k : S -> M A), put i s >> get i >>= k =
      put i s >> k s ;
  _ : forall i, get i >>= put i = skip ;
  _ : forall i (A : UU0) (k : S -> S -> M A),
    get i >>= (fun s => get i >>= k s) = get i >>= fun s => k s s ;
  _ : forall i j (A : UU0) (k : S -> S -> M A),
    get i >>= (fun u => get j >>= (fun v => k u v)) =
    get j >>= (fun v => get i >>= (fun u => k u v)) ;
  _ : forall i j u v, (i != j) \/ (u = v) ->
    put i u >> put j v = put j v >> put i u ;
  _ : forall i j u (A : UU0) (k : S -> M A), i != j ->
    put i u >> get j >>= k =
    get j >>= (fun v => put i u >> k v) }.
Record class_of (S : UU0) (I : eqType) (m : UU0 -> UU0) := Class {
  base : Monad.class_of m ; mixin : mixin_of S I (Monad.Pack base) }.
Structure type (S : UU0) (I : eqType) :=
  Pack { acto : UU0 -> UU0 ; class : class_of S I acto }.
Definition monadType (S : UU0) I (M : type S I) := Monad.Pack (base (class M)).
Module Exports.
Definition aGet (S : UU0) I (M : type S I) : I -> acto M S :=
  let: Pack _ (Class _ (Mixin x _ _ _ _ _ _ _ _)) := M in x.
Arguments aGet {S I M} : simpl never.
Definition aPut (S : UU0) I (M : type S I) : I -> S -> acto M unit :=
  let: Pack _ (Class _ (Mixin _ x _ _ _ _ _ _ _ )) := M in x.
Arguments aPut {S I M} : simpl never.
Notation arrayMonad := type.
Coercion monadType : arrayMonad >-> monad.
Canonical monadType.
End Exports.
End MonadArray.
Export MonadArray.Exports.

Section monadarray_lemmas.
Variables (S : UU0) (I : eqType) (M : arrayMonad S I).
Lemma aputput i s s' : aPut i s >> aPut i s' = aPut i s' :> M _.
Proof. by case: M => ? [? []]. Qed.
Lemma aputget i s (A : UU0) (k : S -> M A) : aPut i s >> aGet i >>= k =
    aPut i s >> k s :> M _.
Proof. by case: M k => ? [? []]. Qed.
Lemma agetputskip i : aGet i >>= aPut i = skip :> M _.
Proof. by case: M => ? [? []]. Qed.
Lemma agetget i (A : UU0) (k : S -> S -> M A) :
  aGet i >>= (fun s => aGet i >>= k s) = aGet i >>= fun s => k s s.
Proof. by case: M k => ? [? []]. Qed.
Lemma agetC i j (A : UU0) (k : S -> S -> M A) :
  aGet i >>= (fun u => aGet j >>= (fun v => k u v)) =
  aGet j >>= (fun v => aGet i >>= (fun u => k u v)).
Proof. by case: M k => ? [? []]. Qed.
Lemma aputC i j u v : i != j \/ u = v ->
  aPut i u >> aPut j v = aPut j v >> aPut i u :> M _.
Proof. by case: M i j u v => ? [? []]. Qed.
Lemma aputgetC i j u (A : UU0) (k : S -> M A) : i != j ->
  aPut i u >> aGet j >>= (fun v => k v) =
  aGet j >>= (fun v => aPut i u >> k v).
Proof. by case: M i j u A k => ? [? []]. Qed.
End monadarray_lemmas.

Module MonadTrace.
Record mixin_of (T : UU0) (M : UU0 -> UU0) := Mixin {
  mark : T -> M unit }.
Record class_of (T : UU0) (M : UU0 -> UU0) := Class {
  base : Monad.class_of M ; mixin : mixin_of T M }.
Structure type (T : UU0) := Pack { acto : UU0 -> UU0; class : class_of T acto }.
Definition monadType (T : UU0) (M : type T) := Monad.Pack (base (class M)).
Module Exports.
Definition Mark (T : UU0) (M : type T) : T -> acto M unit :=
  let: Pack _ (Class _ (Mixin x)) := M in x.
Arguments Mark {T M} : simpl never.
Notation traceMonad := type.
Coercion monadType : traceMonad >-> monad.
Canonical monadType.
End Exports.
End MonadTrace.
Export MonadTrace.Exports.

Module MonadTraceReify.
Record mixin_of (T : UU0) (M : reifyMonad (seq T)) (mark : T -> M unit) :=
  Mixin {_ : forall t l, Reify (mark t) l = Some (tt, rcons l t)}.
Record class_of (T : UU0) (M : UU0 -> UU0) := Class {
  base : MonadTrace.class_of T M ;
  mixin_run : MonadReify.mixin_of _ (Monad.Pack (MonadTrace.base base)) ;
  mixin_traceReify : @mixin_of _ (MonadReify.Pack (MonadReify.Class mixin_run))
    (@Mark _ (MonadTrace.Pack base)) }.
Structure type (T : UU0) := Pack { acto : UU0 -> UU0 ; class : class_of T acto }.
Definition traceMonadType (T : UU0) (M : type T) := MonadTrace.Pack (base (class M)).
Definition reifyMonadType (T : UU0) (M : type T) :=
  MonadReify.Pack (MonadReify.Class (mixin_run (class M))).
Module Exports.
Notation traceReifyMonad := type.
Coercion traceMonadType : traceReifyMonad >-> traceMonad.
Canonical traceMonadType.
Canonical reifyMonadType.
End Exports.
End MonadTraceReify.
Export MonadTraceReify.Exports.

Section tracereify_lemmas.
Variables (T : UU0) (M : traceReifyMonad T).
Lemma reifytmark : forall s t, Reify (Mark t : M _) s = Some (tt, rcons s t).
Proof. by case: M => m [? ? []]. Qed.
End tracereify_lemmas.

Module MonadStateTrace.
Record mixin_of (S T : UU0) (M : monad) := Mixin {
  st_get : M S ;
  st_put : S -> M unit ;
  st_mark : T -> M unit ;
  _ : forall s s', st_put s >> st_put s' = st_put s' ;
  _ : forall s, st_put s >> st_get = st_put s >> Ret s ;
  _ : st_get >>= st_put = skip ;
  _ : forall (A : UU0) (k : S -> S -> M A),
      st_get >>= (fun s => st_get >>= k s) = st_get >>= fun s => k s s ;
  _ : forall s e, st_put s >> st_mark e = st_mark e >> st_put s ;
  _ : forall e (k : _ -> M S), st_get >>= (fun v => st_mark e >> k v) =
                         st_mark e >> st_get >>= k
}.
Record class_of (S T : UU0) (M : UU0 -> UU0) := Class {
  base : Monad.class_of M ;
  mixin : mixin_of S T (Monad.Pack base) }.
Structure type (S T : UU0) := Pack { acto : UU0 -> UU0 ; class : class_of S T acto }.
Definition monadType (S T : UU0) (M : type S T) := Monad.Pack (base (class M)).
Module Exports.
Definition stGet (S T : UU0) (M : type S T) : acto M S :=
  let: Pack _ (Class _ (Mixin x _ _ _ _ _ _ _ _)) := M in x.
Arguments stGet {S T M} : simpl never.
Definition stPut S T (M : type S T) : S -> acto M unit :=
  let: Pack _ (Class _ (Mixin _ x _ _ _ _ _ _ _)) := M in x.
Arguments stPut {S T M} : simpl never.
Definition stMark S T (M : type S T) : T -> acto M unit :=
  let: Pack _ (Class _ (Mixin _ _ x _ _ _ _ _ _)) := M in x.
Arguments stMark {S T M} : simpl never.
Notation stateTraceMonad := type.
Coercion monadType : stateTraceMonad >-> monad.
Canonical monadType.
End Exports.
End MonadStateTrace.
Export MonadStateTrace.Exports.

Section statetrace_lemmas.
Variables (S T : UU0) (M : stateTraceMonad S T).
Lemma st_putput s s' : stPut s >> stPut s' = stPut s' :> M _.
Proof. by case: M => m [? []]. Qed.
Lemma st_putget s : stPut s >> stGet = stPut s >> Ret s :> M _.
Proof. by case: M => m [? []]. Qed.
Lemma st_getputskip : stGet >>= stPut = skip :> M _.
Proof. by case: M => m [? []]. Qed.
Lemma st_getget (A : UU0) (k : S -> S -> M A) :
  stGet >>= (fun s => stGet >>= k s) = stGet >>= fun s => k s s.
Proof. by case: M k => m [? []]. Qed.
Lemma st_putmark s e : stPut s >> stMark e = stMark e >> stPut s :> M _.
Proof. by case: M => m [? []]. Qed.
Lemma st_getmark e (k : S -> M S) :
  stGet >>= (fun v => stMark e >> k v) = stMark e >> stGet >>= k.
Proof. by case: M k => m [? []]. Qed.
End statetrace_lemmas.

Module MonadStateTraceReify.
Record mixin_of (S T : UU0) (M : reifyMonad (S * seq T)%type) (st_get : M S)
  (st_put : S -> M unit) (st_mark : T -> M unit) := Mixin {
  _ : forall s l, Reify st_get (s, l) = Some (s, (s, l)) ;
  _ : forall s l s', Reify (st_put s') (s, l) = Some (tt, (s', l)) ;
  _ : forall t s l, Reify (st_mark t) (s, l) = Some (tt, (s, rcons l t))
}.
Record class_of (S T : UU0) (M : UU0 -> UU0) := Class {
  base : MonadStateTrace.class_of S T M ;
  mixin_reify : MonadReify.mixin_of (S * seq T)%type
    (Monad.Pack (MonadStateTrace.base base)) ;
  mixin_stateTraceReify : @mixin_of _ _ (MonadReify.Pack (MonadReify.Class mixin_reify))
    (@stGet _ _ (MonadStateTrace.Pack base))
    (@stPut _ _ (MonadStateTrace.Pack base))
    (@stMark _ _ (MonadStateTrace.Pack base)) ;
}.
Structure type (S T : UU0) := Pack {
  acto : UU0 -> UU0 ; class : class_of S T acto }.
Definition stateTraceMonadType (S T : UU0) (M : type T S) :=
  MonadStateTrace.Pack (base (class M)).
Definition reifyMonadType (S T : UU0) (M : type S T) :=
  MonadReify.Pack (MonadReify.Class (mixin_reify (class M))).
Module Exports.
Notation stateTraceReifyMonad := type.
Coercion stateTraceMonadType (S T : UU0) (M : stateTraceReifyMonad S T) : stateTraceMonad S T
  := stateTraceMonadType M.
Canonical stateTraceMonadType.
Canonical reifyMonadType.
End Exports.
End MonadStateTraceReify.
Export MonadStateTraceReify.Exports.

Section statetracereify_lemmas.
Variables (S T : UU0) (M : stateTraceReifyMonad S T).
Lemma reifystget : forall s, Reify (stGet : M _) s = Some (s.1, s).
Proof. by case: M => m [? ? [? ? ?]] []. Qed.
Lemma reifystput : forall s s', Reify (stPut s' : M _) s = Some (tt, (s', s.2)).
Proof. by case: M => m [? ? [? ? ?]] []. Qed.
Lemma reifystmark : forall t s, Reify (stMark t : M _) s = Some (tt, (s.1, rcons s.2 t)).
Proof. by case: M => m [? ? [? ? ?]] t []. Qed.
End statetracereify_lemmas.

Module MonadProb.
Local Open Scope reals_ext_scope.
Record mixin_of (M : monad) := Mixin {
  choice : forall (p : prob) (T : Type), M T -> M T -> M T
           where "a <| p |> b" := (choice p a b) ;
  (* identity axioms *)
  _ : forall (T : Type) (a b : M T), a <| 0%:pr |> b = b ;
  _ : forall (T : Type) (a b : M T), a <| 1%:pr |> b = a ;
  (* skewed commutativity *)
  _ : forall (T : Type) p (a b : M T), a <| p |> b = b <| p.~%:pr |> a ;
  _ : forall (T : Type) p, idempotent (@choice p T) ;
  (* quasi associativity *)
  _ : forall (T : Type) (p q r s : prob) (a b c : M T),
    (p = r * s :> R /\ s.~ = p.~ * q.~)%R ->
    a <| p |> (b <| q |> c) = (a <| r |> b) <| s |> c ;
  (* composition distributes leftwards over [probabilistic] choice *)
  _ : forall p, BindLaws.left_distributive (@Bind M) (choice p) }.
Record class_of (M : Type -> Type) := Class {
  base : Monad.class_of M ; mixin : mixin_of (Monad.Pack base) }.
Structure type := Pack { acto : Type -> Type ; class : class_of acto }.
Definition monadType (M : type) := Monad.Pack (MonadProb.base (class M)).
Module Exports.
Definition Choice (M : type) : forall p T, acto M T -> acto M T -> acto M T :=
  let: Pack _ (Class _ (Mixin x _ _ _ _ _ _ )) := M in x.
Arguments Choice {M} : simpl never.
Notation "a <| p |> b" := (Choice p _ a b) : proba_monad_scope.
Notation probMonad := type.
Coercion monadType : probMonad >-> monad.
Canonical monadType.
End Exports.
End MonadProb.
Export MonadProb.Exports.

Section prob_lemmas.
Local Open Scope proba_monad_scope.
Local Open Scope reals_ext_scope.
Variable (M : probMonad).
Lemma choicemm : forall A p, idempotent (@Choice M p A).
Proof. by case: M => m [? []]. Qed.
Lemma choice0 : forall A (mx my : M A), mx <| 0%:pr |> my = my.
Proof. by case: M => m [? []]. Qed.
Lemma choice1 : forall A (mx my : M A), mx <| 1%:pr |> my = mx.
Proof. by case: M => m [? []]. Qed.
Lemma choiceA A : forall (p q r s : prob) (mx my mz : M A),
    (p = r * s :> R /\ s.~ = p.~ * q.~)%R ->
    mx <| p |> (my <| q |> mz) = (mx <| r |> my) <| s |> mz.
Proof. by case: M A => m [? []]. Qed.
Lemma choiceC : forall A (p : prob) (mx my : M A), mx <| p |> my = my <| p.~%:pr |> mx.
Proof. by case: M => m [? []]. Qed.
Lemma prob_bindDl p : BindLaws.left_distributive (@Bind M) (Choice p).
Proof. by case: M => m [? []]. Qed.
End prob_lemmas.
Arguments choiceA {M} {A} _ _ _ _ {mx} {my} {mz}.
Arguments choiceC {M} {A} _ {mx} {my}.

Module MonadProbDr.
Record mixin_of (M : probMonad) := Mixin {
  (* composition distributes rightwards over [probabilistic] choice *)
  (* WARNING: this should not be asserted as an axiom in conjunction with distributivity of <||> over [] *)
  prob_bindDr : forall p, BindLaws.right_distributive (@Bind M) (Choice p) (* NB: not used *)
} .
Record class_of (m : Type -> Type) := Class {
  base : MonadProb.class_of m ;
  mixin : mixin_of (MonadProb.Pack base) }.
Structure type := Pack { acto : Type -> Type; class : class_of acto }.
Definition probMonadType (M : type) := MonadProb.Pack (base (class M)).
Module Exports.
Notation probDrMonad := type.
Coercion probMonadType : probDrMonad >-> probMonad.
Canonical probMonadType.
End Exports.
End MonadProbDr.
Export MonadProbDr.Exports.

Module MonadAltProb.
Record mixin_of (M : altCIMonad) (f : prob -> forall T : Type, M T -> M T -> M T)
  := Mixin {_ : forall T p, right_distributive (f p T) (fun a b => a [~] b) }.
Record class_of (M : Type -> Type) := Class {
  base : MonadAltCI.class_of M ;
  mixin_prob : MonadProb.mixin_of
    (Monad.Pack (MonadAlt.base (MonadAltCI.base base))) ;
  mixin_altProb : @mixin_of (MonadAltCI.Pack base)
                            (@MonadProb.choice _ mixin_prob) }.
Structure type := Pack { acto : Type -> Type ; class : class_of acto }.
Definition altCIMonadType (M : type) := MonadAltCI.Pack (base (class M)).
Definition altMonadType (M : type) :=
  MonadAlt.Pack (MonadAltCI.base (base (class M))).
Definition probMonadType (M : type) :=
  MonadProb.Pack (MonadProb.Class (mixin_prob (class M))).
Module Exports.
Notation altProbMonad := type.
Coercion altCIMonadType : altProbMonad >-> altCIMonad.
Canonical altCIMonadType.
Canonical probMonadType.
Canonical altMonadType.
End Exports.
End MonadAltProb.
Export MonadAltProb.Exports.

Section altprob_lemmas.
Local Open Scope proba_monad_scope.
Variable (M : altProbMonad).
Lemma choiceDr : forall (A : Type) p,
  right_distributive (fun x y : M A => x <| p |> y) (fun x y => x [~] y).
Proof. by case: M => m [? ? []]. Qed.
End altprob_lemmas.

Module MonadExceptProb.
Record mixin_of (M : exceptMonad) (a : prob -> forall A : Type, M A -> M A -> M A) := Mixin {
  catchDl : forall (A : Type) w, left_distributive (@Catch M A) (fun x y => a w A x y)
    (* NB: not used? *)}.
Record class_of (M : Type -> Type) := Class {
  base : MonadExcept.class_of M ;
  mixin_prob : MonadProb.mixin_of (Monad.Pack (MonadFail.base (MonadExcept.base base))) ;
  mixin_exceptProb : @mixin_of (MonadExcept.Pack base)
    (@Choice (MonadProb.Pack (MonadProb.Class mixin_prob)))
}.
Structure type := Pack { acto : Type -> Type ; class : class_of acto }.
Definition exceptMonadType (M : type) := MonadExcept.Pack (base (class M)).
Definition probMonadType M :=
  MonadProb.Pack (MonadProb.Class (mixin_prob (class M))).
Module Exports.
Notation exceptProbMonad := type.
Coercion exceptMonadType : exceptProbMonad >-> exceptMonad.
Canonical exceptMonadType.
Canonical probMonadType.
End Exports.
End MonadExceptProb.
Export MonadExceptProb.Exports.

Module MonadFresh.
Record mixin_of (S : eqType) (M : Type -> Type) :=
  Mixin { fresh : M S }.
Record class_of S (M : Type -> Type) := Class {
  base : Monad.class_of M ;
  mixin : mixin_of S M }.
Structure type S := Pack { acto : Type -> Type ; class : class_of S acto }.
Definition monadType S (M : type S) := Monad.Pack (base (class M)).
Module Exports.
Definition Fresh S (M : type S) : acto M S :=
  let: Pack _ (Class _ (Mixin x)) := M in x.
Arguments Fresh {S M} : simpl never.
Notation freshMonad := type.
Coercion monadType : freshMonad >-> monad.
Canonical monadType.
End Exports.
End MonadFresh.
Export MonadFresh.Exports.

Module segment_closed.
Record t A := mk {
  p : pred (seq A) ;
  H : forall a b, p (a ++ b) -> p a /\ p b }.
End segment_closed.
Definition segment_closed_p A := @segment_closed.p A.
Coercion segment_closed_p : segment_closed.t >-> pred.

Module MonadFailFresh.
Record mixin_of (S : eqType) (M : failMonad) (fresh : M S) := Mixin {
  symbols := fun n => sequence (nseq n fresh);
  (* generated symbols are indeed fresh (specification of fresh) *)
  distinct : segment_closed.t S ;
  _ : bassert distinct \o symbols = symbols ;
  (* failure is a right zero of composition (backtracking interpretation) *)
  _ : BindLaws.right_zero (@Bind M) (@Fail _)
}.
Record class_of (S : eqType) (M : Type -> Type) := Class {
  base : MonadFail.class_of M ;
  mixin : MonadFresh.mixin_of S M ;
  ext : @mixin_of S (MonadFail.Pack base) (MonadFresh.fresh mixin)
}.
Structure type S : Type := Pack { acto : Type -> Type ; class : class_of S acto }.
Definition failMonadType S (M : type S) := MonadFail.Pack (base (class M)).
Definition freshMonadType S (M : type S) :=
  @MonadFresh.Pack _ (MonadFailFresh.acto M)
  (MonadFresh.Class (Monad.class (MonadFail.monadType (failMonadType M)))
                    (mixin (class M))).
Module Exports.
Definition Symbols S (M : type S) :=
  let: Pack _ (Class _ _ (Mixin x _ _ _)) := M return nat -> acto M (seq S) in x.
Arguments Symbols {S M} : simpl never.
Definition Distinct S (M : type S) :=
  let: Pack _ (Class _ _ (Mixin _ x _ _)) := M return segment_closed.t S in x.
Arguments Distinct {S} M : simpl never.
Notation failFreshMonad := type.
Coercion failMonadType : failFreshMonad >-> failMonad.
Canonical failMonadType.
Canonical freshMonadType.
End Exports.
End MonadFailFresh.
Export MonadFailFresh.Exports.

Section failfresh_lemmas.
Variables (S : eqType) (M : failFreshMonad S).
Lemma failfresh_bindmfail : BindLaws.right_zero (@Bind M) (@Fail _).
Proof. by case: M => m [? ? []]. Qed.
Lemma bassert_symbols : bassert (Distinct M) \o Symbols = Symbols :> (nat -> M _).
Proof. by case: M => m [? ? []]. Qed.
End failfresh_lemmas.
