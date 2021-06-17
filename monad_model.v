From mathcomp Require Import all_ssreflect.
From mathcomp Require Import finmap.
From mathcomp Require boolp.
From mathcomp Require Import classical_sets.
From infotheo Require convex classical_sets_ext.
Require Import monae_lib hierarchy monad_lib fail_lib state_lib trace_lib.
Require Import monad_transformer.

(******************************************************************************)
(*                       Models for various monads                            *)
(*                                                                            *)
(* Sample models for monads in hierarchy.v (see also other *_model.v files).  *)
(* As for naming, we tend to use the identifier acto for the actions on       *)
(* objects and actm for the actions on morphisms.                             *)
(*                                                                            *)
(* Models of monads (to be used to build models of interfaces):               *)
(* identity           == identity monad                                       *)
(* Module ListMonad   == defines the type ListMonad.t of list monads          *)
(* Module SetMonad    == defines the type SetMonad.t of set monads using      *)
(*                        using classical_sets                                *)
(* Module Except      == defines the type Except.t of exception monads        *)
(* option_monad       == option monad, i.e., Except.t unit                    *)
(* Module Output      == defines the type Output.t of output monads           *)
(* Module Environment == defines the type Environment.t of environment monads *)
(* Module State       == defines the type State.t of state monads             *)
(* Module Cont        == define the type Cont.t of continuation monads        *)
(*                                                                            *)
(* Sigma-operations (with algebraicity proofs):                               *)
(* Module ListOps        == empty and append operations                       *)
(* Module OutputOps      == output and flush operations                       *)
(* Module EnvironmentOps == ask and local operations                          *)
(* Module ExceptOps      == throw and handle operations                       *)
(* Module StateOps       == get and put operations                            *)
(* Module ContOps        == abort and (algebraic) callcc operations           *)
(*                                                                            *)
(* Models of interfaces:                                                      *)
(* Module ModelFail               == models of failMonad                      *)
(* Module ModelExcept             == model of exceptMonad                     *)
(* Module ModelState              == model of stateMonad                      *)
(* Module ModelAlt                == models of altMonad                       *)
(* Module ModelAltCI              == model of altCIMonad                      *)
(* Module ModelNondet             == models of nondetMonad                    *)
(* Module ModelStateTrace         == model of stateTraceMonad                 *)
(* Module ModelCont               == model of contMonad                       *)
(* Module ModelStateTraceReify    == model of stateTraceReifyMonad            *)
(* Module ModelBacktrackableState == from the ground up using fsets, i.e.,    *)
(*                                   redefinition of monad state-fail-alt-    *)
(*                                   nondet-nondetstate monad                 *)
(*                                                                            *)
(* Equality between monads from the hierarchy and their counterparts built    *)
(* using monad transformers and the identity monad:                           *)
(* - stateT_id_ModelState, exceptT_id_ModelExcept, contT_id_ModelCont         *)
(*                                                                            *)
(* Module ModelMonadStateRun       == model of stateRunMonad                  *)
(* Module ModelMonadExceptStateRun == model of exceptStateRunMonad            *)
(*                                                                            *)
(* references:                                                                *)
(* - Wadler, P. Monads and composable continuations. LISP and Symbolic        *)
(*   Computation 7, 39–55 (1994)                                              *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.

(* TODO *)
Section PR_to_classical_sets.
Local Open Scope classical_set_scope.

Lemma bigsetUA A B C (s : set A) (f : A -> set B) (g : B -> set C) :
  \bigcup_(i in \bigcup_(i in s) f i) g i = \bigcup_(x in s) \bigcup_(i in f x) g i.
Proof.
rewrite boolp.funeqE => c; rewrite boolp.propeqE.
split => [[b [a' aa' ?] ?]|[a' aa' [b ? ?]]];
  by [exists a' => //; exists b | exists b => //; exists a'].
Qed.

End PR_to_classical_sets.

(* TODO *)
Section PR_to_fset.
Local Open Scope fset_scope.
Variables (K V : choiceType) (f : K -> V).

Lemma imfset_set1 x : f @` [fset x] = [fset f x].
Proof.
apply/fsetP => y.
by apply/imfsetP/fset1P=> [[x' /fset1P-> //]| ->]; exists x; rewrite ?fset11.
Qed.

Variables (T : choiceType) (I : eqType) (r : seq I).
(* In order to avoid "&& true" popping up everywhere, *)
(*  we prepare a specialized version of bigfcupP *)
Lemma bigfcupP' x (F : I -> {fset T}) :
  reflect (exists2 i : I, (i \in r) & x \in F i)
          (x \in \bigcup_(i <- r | true) F i).
Proof.
apply: (iffP idP) => [|[i ri]]; last first.
  by apply: fsubsetP x; rewrite bigfcup_sup.
rewrite big_seq_cond; elim/big_rec: _ => [|i _ /andP[ri Pi] _ /fsetUP[|//]].
  by rewrite in_fset0.
by exists i; rewrite ?ri.
Qed.
End PR_to_fset.

Module ModelMonad.

Section identity.
Local Obligation Tactic := by [].
Definition identity_functor : FId ~> FId :=
  Natural.Pack (Natural.Mixin (@natural_id FId)).
Program Definition identity := @Monad_of_ret_bind _ identity_functor
  (fun A B (a : id A) (f : A -> id B) => f a) _ _ _.
End identity.

Module ListMonad.
Section listmonad.
Definition acto := fun A => seq A.
Local Notation M := acto.
Lemma map_id : @FunctorLaws.id seq (@map).
Proof. by move=> A; rewrite boolp.funeqE => x; rewrite map_id. Qed.
Lemma map_comp : @FunctorLaws.comp seq (@map).
Proof. by move=> A B C g h; rewrite boolp.funeqE => x; rewrite map_comp. Qed.
Definition functor := Functor.Pack (Functor.Mixin map_id map_comp).
Definition ret_component := fun A : Type => (@cons A)^~ [::].
Lemma ret_naturality : naturality FId functor ret_component.
Proof. by move=> A B h; rewrite boolp.funeqE. Qed.
Definition ret : FId ~> functor := Natural.Pack (Natural.Mixin ret_naturality).
Definition bind := fun A B (a : M A) (f : A -> M B) => flatten (map f a).
Lemma left_neutral : @BindLaws.left_neutral functor bind ret.
Proof. by move=> A B m f; rewrite /bind /ret /= cats0. Qed.
Lemma right_neutral : @BindLaws.right_neutral functor bind ret.
Proof. by move=> A m; rewrite /bind flatten_seq1. Qed.
Lemma associative : @BindLaws.associative functor bind.
Proof.
move=> A B C; elim => // h t; rewrite /bind => ih f g.
by rewrite /= map_cat flatten_cat /= ih.
Qed.
Definition t := Monad_of_ret_bind left_neutral right_neutral associative.
End listmonad.
End ListMonad.

Module SetMonad.
Section setmonad.
Local Open Scope classical_set_scope.
Lemma map_id : FunctorLaws.id (fun T1 T2 f A => f @` A).
Proof.
by move=> x; rewrite boolp.funeqE => y; rewrite image_id.
Qed.
Lemma map_comp : FunctorLaws.comp (fun T1 T2 f A => f @` A).
Proof.
by move=> A B C g h; rewrite boolp.funeqE => x /=; rewrite image_comp.
Qed.
Definition functor := Functor.Pack (Functor.Mixin map_id map_comp).
Lemma naturality_ret : naturality FId functor (@set1).
Proof.
move=> A B h; rewrite boolp.funeqE => a /=; rewrite boolp.funeqE => b /=.
rewrite boolp.propeqE; split.
  by case => a0; rewrite /set1 => ->{a0} <-{b}.
by rewrite /set1 => ->{b} /=; exists a.
Qed.
Definition ret : FId ~> functor := Natural.Pack (Natural.Mixin naturality_ret).
Lemma left_neutral :
  @BindLaws.left_neutral functor (fun A B => @bigsetU B A) ret.
Proof.  move=> ? ? ? ?; exact: bigcup_set1. Qed.
Lemma right_neutral :
  @BindLaws.right_neutral functor (fun A B => @bigsetU B A) ret.
Proof. by move=> ? ?; rewrite classical_sets_ext.bigcup_of_singleton image_id. Qed.
Lemma associative :
  @BindLaws.associative functor (fun A B => @bigsetU B A).
Proof. move=> ? ? ? ? ? ?; exact: bigsetUA. Qed.
Definition t := Monad_of_ret_bind left_neutral right_neutral associative.
End setmonad.
End SetMonad.

Module Except.
Section except.
Variable E : UU0.
Definition acto := fun A : UU0 => (E + A)%type.
Local Notation M := acto.
Definition map := fun (A B : UU0) (f : A -> B) (a : M A) =>
  match a with inl z => inl z | inr b => inr (f b) end.
Lemma map_id : FunctorLaws.id map.
Proof. by move=> *; rewrite boolp.funeqE; case. Qed.
Lemma map_comp : FunctorLaws.comp map.
Proof. by move=> *; rewrite boolp.funeqE; case. Qed.
Definition functor := Functor.Pack (Functor.Mixin map_id map_comp).
Definition ret_component := @inr E.
Lemma natural : naturality FId functor ret_component.
Proof. by move=> A B h; rewrite boolp.funeqE. Qed.
Definition ret : FId ~> functor := Natural.Pack (Natural.Mixin natural).
Definition bind := fun A B (a : M A) (f : A -> M B) =>
  match a with inl z => inl z | inr b => f b end.
Lemma left_neutral : @BindLaws.left_neutral functor bind ret.
Proof. by []. Qed.
Lemma right_neutral : @BindLaws.right_neutral functor bind ret.
Proof. by move=> ? []. Qed.
Lemma associative : @BindLaws.associative functor bind.
Proof. by move=> ? ? ? []. Qed.
Definition t := Monad_of_ret_bind left_neutral right_neutral associative.
End except.
End Except.

Definition option_monad := Except.t unit.

Module Output.
Section output.
Variable L : UU0.
Definition acto := fun X : UU0 => (X * seq L)%type.
Local Notation M := acto.
Definition map (A B : UU0) (f : A -> B) (m : M A) : M B :=
  let: (a, s) := m in (f a, s).
Lemma map_id : FunctorLaws.id map.
Proof. by move=> A; rewrite boolp.funeqE; case. Qed.
Lemma map_comp : FunctorLaws.comp map.
Proof. by move=> A B C g h; rewrite boolp.funeqE; case. Qed.
Definition functor := Functor.Pack (Functor.Mixin map_id map_comp).
Definition ret_component : FId ~~> M := fun A a => (a, [::]).
Lemma naturality_ret : naturality FId functor ret_component.
Proof. by move=> A B h; rewrite boolp.funeqE. Qed.
Definition ret : FId ~> functor := Natural.Pack (Natural.Mixin naturality_ret).
Definition bind := fun A B (m : M A) (f : A -> M B) =>
  let: (x, w) := m in let: (x', w') := f x in (x', w ++ w').
Lemma left_neutral : @BindLaws.left_neutral functor bind ret.
Proof. by move=> A B a f; rewrite /bind /=; case: f. Qed.
Lemma right_neutral : @BindLaws.right_neutral functor bind ret.
Proof. by move=> A m; rewrite /bind /=; case: m => x w; rewrite cats0. Qed.
Lemma associative : @BindLaws.associative functor bind.
Proof.
move=> A B C m f g; rewrite /bind; case: m => x w; case: f => x' w'.
by case: g => x'' w''; rewrite catA.
Qed.
Definition t := Monad_of_ret_bind left_neutral right_neutral associative.
End output.
End Output.

Module Environment.
Section environment.
Variable E : UU0.
Definition acto := fun A : UU0 => E -> A.
Local Notation M := acto.
Definition map (A B : UU0) (f : A -> B) (m : M A) : M B := fun e => f (m e).
Lemma map_id : FunctorLaws.id map. Proof. by []. Qed.
Lemma map_comp : FunctorLaws.comp map.
Proof. by move=> A B C g h; rewrite boolp.funeqE. Qed.
Definition functor := Functor.Pack (Functor.Mixin map_id map_comp).
Definition ret_component : FId ~~> M := fun A x => fun e => x.
(* computation that ignores the environment *)
Lemma naturality_ret : naturality FId functor ret_component.
Proof. by move=> A B h; rewrite boolp.funeqE. Qed.
Definition ret : FId ~> functor := Natural.Pack (Natural.Mixin naturality_ret).
Definition bind := fun A B (m : M A) (f : A -> M B) => fun e => f (m e) e.
(* binds m f applied the same environment to m and to the result of f *)
Lemma left_neutral : @BindLaws.left_neutral functor bind ret.
Proof. by []. Qed.
Lemma right_neutral : @BindLaws.right_neutral functor bind ret.
Proof. by []. Qed.
Lemma associative : @BindLaws.associative functor bind.
Proof. by []. Qed.
Definition t := Monad_of_ret_bind left_neutral right_neutral associative.
End environment.
End Environment.

Module State.
Section state.
Variable S : UU0. (* type of states *)
Definition acto := fun A : UU0 => S -> A * S.
Local Notation M := acto.
Definition map (A B : UU0) (f : A -> B) (m : M A) : M B :=
 fun (s : S) => let (x1, x2) := m s in (f x1, x2).
Lemma map_id : FunctorLaws.id map.
Proof.
move=> x; rewrite boolp.funeqE => y; rewrite boolp.funeqE => z /=.
by  rewrite /map; case: y.
Qed.
Lemma map_comp : FunctorLaws.comp map.
Proof.
move=> A B C g h; rewrite boolp.funeqE => m; rewrite boolp.funeqE => s.
by rewrite /map /=; case: m.
Qed.
Definition functor := Functor.Pack (Functor.Mixin map_id map_comp).
Definition ret_component : FId ~~> M := fun A a => fun s => (a, s).
Lemma naturality_ret : naturality FId functor ret_component.
Proof. by move=> A B h; rewrite boolp.funeqE => a /=; rewrite boolp.funeqE. Qed.
Definition ret : FId ~> functor := Natural.Pack (Natural.Mixin naturality_ret).
Definition bind := fun A B (m : M A) (f : A -> M B) => uncurry f \o m.
Lemma left_neutral : @BindLaws.left_neutral functor bind ret.
Proof. by move=> A B a f; rewrite boolp.funeqE. Qed.
Lemma right_neutral : @BindLaws.right_neutral functor bind ret.
Proof.
by move=> A f; rewrite boolp.funeqE => s; rewrite /bind /=; case: (f s).
Qed.
Lemma associative : @BindLaws.associative functor bind.
Proof.
move=> A B C a b c; rewrite /bind compA; congr (_ \o _).
by rewrite boolp.funeqE => -[].
Qed.
Definition t := Monad_of_ret_bind left_neutral right_neutral associative.
End state.
End State.

(* see Sect. 3 of of [Wadler, 94] for the model of the ret and the bind of the
continuation monad *)
Module Cont.
Section cont.
Variable r : UU0. (* the type of answers *)
Definition acto := fun A : UU0 => (A -> r) -> r.
Local Notation M := acto.
Definition actm (A B : UU0) (f : A -> B) (m : M A) : M B :=
  fun Br : B -> r => m (fun a : A => Br (f a)).
Lemma map_id : FunctorLaws.id actm.
Proof. by move=> A; rewrite boolp.funeqE => m; rewrite boolp.funeqE. Qed.
Lemma map_comp : FunctorLaws.comp actm.
Proof. by move=> *; rewrite boolp.funeqE => m; rewrite boolp.funeqE. Qed.
Definition functor := Functor.Pack (Functor.Mixin map_id map_comp).
Lemma naturality_ret : naturality FId functor (fun A a => fun k => k a).
Proof. by move=> A B f; rewrite boolp.funeqE => a /=; rewrite boolp.funeqE. Qed.
Definition ret : FId ~> functor := Natural.Pack (Natural.Mixin naturality_ret).
Definition bind := fun A B (ma : M A) (f : A -> M B) => fun k => ma (fun a => f a k).
Lemma left_neutral : @BindLaws.left_neutral functor bind ret.
Proof. by move=> A B a f; rewrite boolp.funeqE => Br. Qed.
Lemma right_neutral : @BindLaws.right_neutral functor bind ret.
Proof. by []. Qed.
Lemma associative : @BindLaws.associative functor bind.
Proof. by []. Qed.
Definition t : monad := Monad_of_ret_bind left_neutral right_neutral associative.
End cont.
End Cont.

End ModelMonad.

Module ListOps.

Module Empty.
Definition acto (X : Type) := unit.
Definition actm X Y (f : X -> Y) (t : acto X) : acto Y := tt.
Program Definition func := Functor.Pack (@Functor.Mixin _ actm _ _).
Next Obligation. by move=> A; rewrite boolp.funeqE; case. Qed.
Next Obligation. by move=> A B C f g; rewrite boolp.funeqE; case. Qed.
End Empty.

Module Append.
Definition acto (X : Type) := (X * X)%type.
Definition actm X Y (f : X -> Y) (t : acto X) : acto Y :=
  let: (x1, x2) := t in (f x1, f x2).
Program Definition func := Functor.Pack (@Functor.Mixin _ actm _ _).
Next Obligation. by move=> A; rewrite boolp.funeqE; case. Qed.
Next Obligation. by move=> A B C f g; rewrite boolp.funeqE; case. Qed.
End Append.

Local Notation M := ModelMonad.ListMonad.t.

Definition empty A : unit -> M A := fun _ => @nil A.
Lemma naturality_empty : naturality (Empty.func \O M) M empty.
Proof. by move=> A B h; rewrite boolp.funeqE. Qed.
Definition empty_op : Empty.func.-operation M := Natural.Pack (Natural.Mixin naturality_empty).
Lemma algebraic_empty : algebraicity empty_op.
Proof. by []. Qed.

Definition append A : (M A * M A)%type -> M A :=
  fun x => let: (s1, s2) := x in (s1 ++ s2).
Lemma naturality_append : naturality (Append.func \O M) M append.
Proof.
move=> A B h; rewrite boolp.funeqE; case => s1 s2 /=.
rewrite /Actm /= /Monad_of_ret_bind.Map /=.
rewrite /ModelMonad.ListMonad.bind /= /ModelMonad.ListMonad.ret /=.
by rewrite map_cat flatten_cat.
Qed.
Definition append_op : Append.func.-operation M := Natural.Pack (Natural.Mixin naturality_append).
Lemma algebraic_append : algebraicity append_op.
Proof.
move=> A B f [t1 t2] /=.
rewrite !bindE /= /ModelMonad.ListMonad.bind /= /Actm /=.
rewrite /Monad_of_ret_bind.Map /=.
rewrite /ModelMonad.ListMonad.bind /= /ModelMonad.ListMonad.ret /=.
by rewrite -flatten_cat -map_cat /= -flatten_cat -map_cat.
Qed.

End ListOps.

Module OutputOps.

Module Output. Section output. Variable L : UU0.
Definition acto (X : UU0) := (seq L * X)%type.
Definition actm (X Y : UU0) (f : X -> Y) (t : acto X) : acto Y :=
  let: (w, x) := t in (w, f x).
Program Definition func := Functor.Pack (@Functor.Mixin _ actm _ _).
Next Obligation. by move=> A; rewrite boolp.funeqE; case. Qed.
Next Obligation. by move=> A B C f g; rewrite boolp.funeqE; case. Qed.
End output. End Output.

Module Flush.
Definition acto (X : Type) := X.
Definition actm X Y (f : X -> Y) (t : acto X) : acto Y := f t.
Program Definition func := Functor.Pack (@Functor.Mixin _ actm _ _).
Next Obligation. by []. Qed.
Next Obligation. by []. Qed.
End Flush.

Section outputops.
Variable L : UU0.
Local Notation M := (ModelMonad.Output.t L).

Definition output (A : UU0) : (seq L * M A) -> M A :=
  fun m => let: (x, w') := m.2 in (x, m.1 ++ w'). (*NB: w'++m.1 in the esop paper*)
Lemma naturality_output : naturality (Output.func L \O M) M output.
Proof.
move=> A B h; rewrite boolp.funeqE; case => w [x w'] /=.
by rewrite /output /= cats0 /Actm /= /Monad_of_ret_bind.Map /= cats0.
Qed.
Definition output_op : (Output.func L).-operation M :=
  Natural.Pack (Natural.Mixin naturality_output).
Lemma algebraic_output : algebraicity output_op.
Proof.
move=> A B f [w [x w']].
rewrite bindE /= /output /= bindE /= !cats0.
by case: f => x' w''; rewrite catA.
Qed.

Definition flush A : M A -> M A := fun m => let: (x, _) := m in (x, [::]).
(* performing a computation in a modified environment *)
Lemma naturality_flush : naturality (Flush.func \O M) M flush.
Proof. by move=> A B h; rewrite boolp.funeqE; case. Qed.
Definition flush_op : Flush.func.-operation M := Natural.Pack (Natural.Mixin naturality_flush).
(* NB: flush is not algebraic *)
Lemma algebraic_flush : algebraicity flush_op.
Proof.
move=> A B f [x w].
rewrite /flush_op /=.
rewrite /flush /=.
rewrite /Actm /=.
rewrite bindE /=.
rewrite /OutputOps.Flush.actm.
rewrite bindE /=.
rewrite cats0.
case: f => x' w'.
Abort.

End outputops.

End OutputOps.

(* wip *)
Module ModelOutput.
Section modeloutput.
Variable L : UU0.
Local Notation M := (ModelMonad.Output.t L).
(* usual output operation *)
Definition output : seq L -> M unit := fun w => OutputOps.output_op _ _ (w, Ret tt).
Lemma outputE : output = fun w => (tt, w).
Proof.
rewrite boolp.funeqE => w.
by rewrite /output /OutputOps.output_op /= /OutputOps.output /= cats0.
Qed.
(* TODO: complete with an interface for the output monad and instantiate *)
End modeloutput.
End ModelOutput.

Module EnvironmentOps.

Module Ask. Section ask. Variable E : UU0.
Definition acto (X : UU0) := E -> X.
Definition actm (X Y : UU0) (f : X -> Y) (t : acto X) : acto Y := f \o t.
Program Definition func := Functor.Pack (@Functor.Mixin _ actm _ _).
Next Obligation. by []. Qed.
Next Obligation. by []. Qed.
End ask. End Ask.

Module Local. Section local. Variable E : UU0.
Definition acto (X : UU0) := ((E -> E) * X)%type.
Definition actm (X Y : UU0) (f : X -> Y) (t : acto X) : acto Y :=
  let: (e, x) := t in (e, f x).
Program Definition func := Functor.Pack (@Functor.Mixin _ actm _ _).
Next Obligation. by move=> A; rewrite boolp.funeqE; case. Qed.
Next Obligation. by move=> A B C g h; rewrite boolp.funeqE; case. Qed.
End local. End Local.

Section environmentops.
Variable E : UU0.
Local Notation M := (ModelMonad.Environment.t E).

Definition ask A : (E -> M A) -> M A := fun f s => f s s. (* reading the environment *)
Lemma naturality_ask : naturality (Ask.func E \O M) M ask.
Proof. by []. Qed.
Definition ask_op : (Ask.func E).-operation M :=
  Natural.Pack (Natural.Mixin naturality_ask).
Lemma algebraic_ask : algebraicity ask_op.
Proof. by []. Qed.

Definition local A : (E -> E) * M A -> M A := fun x s => let: (e, t) := x in t (e s).
(* performing a computation in a modified environment *)
Lemma naturality_local : naturality (Local.func E \O M) M local.
Proof. by move=> A B h; rewrite boolp.funeqE; case. Qed.
Definition local_op : (Local.func E).-operation M :=
  Natural.Pack (Natural.Mixin naturality_local).
(* NB: local is not algebraic *)
Lemma algebraic_local : algebraicity local_op.
Proof.
move=> A B f t.
rewrite /local_op /=.
rewrite /local /=.
rewrite boolp.funeqE => e /=.
rewrite bindE /=.
rewrite /ModelMonad.Environment.bind /=.
rewrite /Actm /=.
rewrite /Monad_of_ret_bind.Map /=.
rewrite /ModelMonad.Environment.bind /=.
rewrite /ModelMonad.Environment.ret /=.
rewrite /EnvironmentOps.Local.actm /=.
case: t => /= ee m.
rewrite bindE /=.
rewrite /ModelMonad.Environment.bind /=.
rewrite /Actm /=.
rewrite /Monad_of_ret_bind.Map /=.
rewrite /ModelMonad.Environment.bind /=.
rewrite /ModelMonad.Environment.ret /=.
Abort.

End environmentops.
End EnvironmentOps.

(* wip *)
Module ModelEnvironment.
Section modelenvironment.
Variable E : UU0.
Local Notation M := (ModelMonad.Environment.t E).
(* usual get operation *)
Definition ask : M E := EnvironmentOps.ask_op _ _ Ret.
Lemma askE : ask = fun e => e. Proof. by []. Qed.
(* TODO: complete with an interface for the environment monad and instantiate, see Jaskelioff's PhD *)
End modelenvironment.
End ModelEnvironment.

Module ExceptOps.

Module Throw. Section throw. Variable Z : UU0.
Definition acto (X : UU0) := Z.
Definition actm (X Y : UU0) (f : X -> Y) (t : acto X) : acto Y := t.
Program Definition func := Functor.Pack (@Functor.Mixin _ actm _ _).
Next Obligation. by []. Qed.
Next Obligation. by []. Qed.
End throw. End Throw.

Module Handle. Section handle. Variable Z : UU0.
Definition acto (X : UU0) := (X * (Z -> X))%type.
Definition actm (X Y : UU0) (f : X -> Y) (t : acto X) : acto Y :=
  let: (x, h) := t in (f x, fun z => f (h z)).
Program Definition func := Functor.Pack (@Functor.Mixin _ actm _ _).
Next Obligation. by move=> A; rewrite boolp.funeqE; case. Qed.
Next Obligation. by move=> A B C g h; rewrite boolp.funeqE; case. Qed.
End handle. End Handle.

Section exceptops.
Variable Z : UU0.
Local Notation M := (ModelMonad.Except.t Z).

Definition throw (A : UU0) : Z -> M A := fun z => inl z.
Lemma naturality_throw : naturality (Throw.func Z \O M) M throw.
Proof. by []. Qed.
Definition throw_op : (Throw.func Z).-operation M :=
  Natural.Pack (Natural.Mixin naturality_throw).
Lemma algebraic_throw : algebraicity throw_op.
Proof. by []. Qed.
Definition throw_aop : (Throw.func Z).-aoperation (ModelMonad.Except.t Z) :=
  AOperation.Pack (AOperation.Class (AOperation.Mixin algebraic_throw)).

Definition handle A (m : M A) (h : Z -> M A) : M A :=
  match m with inl z => h z | inr x => inr x end.
Lemma naturality_handle :
  naturality (Handle.func Z \O M) M (fun A => uncurry (@handle A)).
Proof. by move=> A B h; rewrite boolp.funeqE; case; case. Qed.
Definition handle_op : (Handle.func Z).-operation M :=
  Natural.Pack (Natural.Mixin naturality_handle).
(* NB: handle is not algebraic *)
Lemma algebraic_handle : algebraicity handle_op.
Proof.
move=> A B f t.
rewrite /handle_op /=.
rewrite /handle /=.
rewrite /uncurry /prod_curry.
case: t => -[z//|a] g /=.
rewrite bindE /=.
case: (f a) => // z.
rewrite bindE /=.
rewrite /ModelMonad.Except.bind /=.
rewrite /Actm /=.
rewrite /Monad_of_ret_bind.Map /=.
rewrite /ModelMonad.Except.bind /=.
case: (g z) => [z0|a0].
Abort.

End exceptops.
End ExceptOps.

Arguments ExceptOps.throw_op {Z}.
Arguments ExceptOps.handle_op {Z}.

Module StateOps.

(* NB: see also Module Ask *)
Module Get. Section get. Variable S : UU0.
Definition acto (X : UU0) := S -> X.
Definition actm (X Y : UU0) (f : X -> Y) (t : acto X) : acto Y := f \o t.
Program Definition func := Functor.Pack (@Functor.Mixin _ actm _ _).
Next Obligation. by move=> A; rewrite boolp.funeqE. Qed.
Next Obligation. by move=> A B C g h; rewrite boolp.funeqE. Qed.
End get. End Get.

Module Put. Section put. Variable S : UU0.
Definition acto (X : UU0) := (S * X)%type.
Definition actm (X Y : UU0) (f : X -> Y) (sx : acto X) : acto Y := (sx.1, f sx.2).
Program Definition func := Functor.Pack (@Functor.Mixin _ actm _ _).
Next Obligation. by move=> A; rewrite boolp.funeqE; case. Qed.
Next Obligation. by move=> A B C g h; rewrite boolp.funeqE. Qed.
End put. End Put.

Section stateops.
Variable S : UU0.
Local Notation M := (ModelMonad.State.t S).

Definition get A (k : S -> M A) : M A := fun s => k s s.
Lemma naturality_get : naturality (Get.func S \O M) M get.
Proof.
move=> A B h; rewrite boolp.funeqE => /= m /=.
by rewrite boolp.funeqE => s; rewrite FCompE.
Qed.
Definition get_op : (Get.func S).-operation M :=
  Natural.Pack (Natural.Mixin naturality_get).
Lemma algebraic_get : algebraicity get_op.
Proof. by []. Qed.
Definition get_aop : (Get.func S).-aoperation (ModelMonad.State.t S) :=
  AOperation.Pack (AOperation.Class (AOperation.Mixin algebraic_get)).

Definition put A (s : S) (m : M A) : M A := fun _ => m s.
Lemma naturality_put :
  naturality (Put.func S \O M) M (fun A => uncurry (put (A:=A))).
Proof.
move=> A B h.
by rewrite boolp.funeqE => /=; case => s m /=; rewrite boolp.funeqE.
Qed.
Definition put_op : (Put.func S).-operation M :=
  Natural.Pack (Natural.Mixin naturality_put).
Lemma algebraic_put : algebraicity put_op.
Proof. by move=> ? ? ? []. Qed.
Definition put_aop : (Put.func S).-aoperation (ModelMonad.State.t S) :=
  AOperation.Pack (AOperation.Class (AOperation.Mixin algebraic_put)).

End stateops.
End StateOps.

Arguments StateOps.get_op {S}.
Arguments StateOps.put_op {S}.

Module ContOps.

Module Abort. Section abort. Variable r : UU0.
Definition acto (X : UU0) := r.
Definition actm (A B : UU0) (f : A -> B) (x : acto A) : acto B := x.
Program Definition func := Functor.Pack (@Functor.Mixin _ actm _ _ ).
Next Obligation. by []. Qed.
Next Obligation. by []. Qed.
End abort. End Abort.

Module Acallcc. Section acallcc. Variable r : UU0.
Definition acto := fun A : UU0 => (A -> r) -> A.
Definition actm (X Y : UU0) (f : X -> Y) (t : acto X) : acto Y :=
  fun (g : Y -> r) => f (t (fun x => g (f x))).
Program Definition func := Functor.Pack (@Functor.Mixin _ actm _ _ ).
Next Obligation. by []. Qed.
Next Obligation. by []. Qed.
End acallcc. End Acallcc.

Section contops.
Variable r : UU0.

Local Notation M := (ModelMonad.Cont.t r).

Definition abort (A : UU0) : r -> M A := fun r _ => r.
Lemma naturality_abort : naturality (Abort.func r \O M) M abort.
Proof. by []. Qed.
Definition abort_op : (Abort.func r).-operation M :=
  Natural.Pack (Natural.Mixin naturality_abort).
Lemma algebraicity_abort : algebraicity abort_op.
Proof. by []. Qed.
Definition abort_aop : (Abort.func r).-aoperation (ModelMonad.Cont.t r) :=
  AOperation.Pack (AOperation.Class (AOperation.Mixin algebraicity_abort)).

(* alebgraic call/cc *)
Definition acallcc A (f : (M A -> r) -> M A) : M A :=
  fun k => f (fun m => m k) k.
Lemma naturality_acallcc : naturality (Acallcc.func r \O M) M acallcc.
Proof. by []. Qed.
Definition acallcc_op : (Acallcc.func r).-operation M :=
  Natural.Pack (Natural.Mixin naturality_acallcc).
Lemma algebraicity_callcc : algebraicity acallcc_op.
Proof. by []. Qed.
Definition callcc_aop : (Acallcc.func r).-aoperation (ModelMonad.Cont.t r) :=
  AOperation.Pack (AOperation.Class (AOperation.Mixin algebraicity_callcc)).

End contops.
End ContOps.

Module ModelFail.

Section option.
Local Obligation Tactic := by [].
Program Definition option_class := @MonadFail.Class _ _
  (@MonadFail.Mixin ModelMonad.option_monad (fun A => @ExceptOps.throw unit A tt) _).
Definition option := MonadFail.Pack option_class.
End option.

Section list.
Local Obligation Tactic := by [].
Program Definition list_class := @MonadFail.Class _ _
  (@MonadFail.Mixin ModelMonad.ListMonad.t (fun _ => @ListOps.empty _ tt) _).
Definition monae_list := MonadFail.Pack list_class.
End list.

Section set.
Local Obligation Tactic := idtac.
Program Definition set_class := @MonadFail.Class _ _
  (@MonadFail.Mixin ModelMonad.SetMonad.t (@set0) _).
Next Obligation.
move=> A B f /=; rewrite boolp.funeqE => b; rewrite boolp.propeqE.
by split=> // -[a []].
Qed.
Definition monae_set := MonadFail.Pack set_class.
End set.

End ModelFail.

Module ModelExcept.
Section except.
Local Notation M := ModelMonad.option_monad.
Definition handle : forall A, M A -> M A -> M A :=
  fun A m1 m2 => @ExceptOps.handle_op unit _ (m1, (fun _ => m2)).
Lemma handleE : handle = (fun A m m' => if m is inr x then m else m').
Proof. by apply fun_ext_dep => A; rewrite boolp.funeqE; case. Qed.
Program Definition except_class := @MonadExcept.Class _
  ModelFail.option_class (@MonadExcept.Mixin _ handle _ _ _ _).
Next Obligation. by case => //; case. Qed.
Next Obligation. by case. Qed.
Next Obligation. by case. Qed.
Next Obligation. by case. Qed.
Definition t := MonadExcept.Pack except_class.
End except.
End ModelExcept.

Module ModelState.
Section modelstate.
Variable S : UU0.
Local Notation M := (ModelMonad.State.t S).
Definition get : M S := StateOps.get_op _ Ret.
Lemma getE : get = fun s => (s, s). Proof. by []. Qed.
Definition put : S -> M unit := fun s => StateOps.put_op _ (s, Ret tt).
Lemma putE : put = fun s' _ => (tt, s').
Proof. by []. Qed.
Program Definition state : stateMonad S := MonadState.Pack (MonadState.Class
  (@MonadState.Mixin _ _ get put _ _ _ _)).
End modelstate.
End ModelState.

Module ModelAlt.

Section list.
Local Obligation Tactic := idtac.
Program Definition list_class := @MonadAlt.Class _ _
  (@MonadAlt.Mixin ModelMonad.ListMonad.t (fun A => curry (@ListOps.append A)) catA _).
Next Obligation.
move=> A B /= s1 s2 k.
rewrite !bindE /Join /= /Monad_of_ret_bind.join /= /ModelMonad.ListMonad.bind /=.
rewrite (_ : (ModelMonad.ListMonad.t # k) (s1 ++ s2) =
  ((ModelMonad.ListMonad.t # k) s1) ++
  ((ModelMonad.ListMonad.t # k) s2)); last first.
  rewrite !(@Monad_of_ret_bind.MapE ModelMonad.ListMonad.functor) /=.
  by rewrite /ModelMonad.ListMonad.bind map_cat flatten_cat.
by rewrite /ModelMonad.ListMonad.bind map_cat flatten_cat.
Qed.
Definition list := MonadAlt.Pack list_class.
End list.

(* NB: was at the top of the file *)
Lemma setUDl : @BindLaws.left_distributive ModelMonad.SetMonad.functor (fun I A => @bigsetU A I) (@setU).
Proof.
move=> A B /= p q r; rewrite boolp.funeqE => b; rewrite boolp.propeqE; split.
move=> -[a [?|?] ?]; by [left; exists a | right; exists a].
by rewrite /setU => -[[a ? ?]|[a ? ?]]; exists a => //; [left|right].
Qed.

Section set.
Local Obligation Tactic := idtac.
Program Definition set_class := @MonadAlt.Class _ _
  (@MonadAlt.Mixin ModelMonad.SetMonad.t (@setU) _ _).
Next Obligation. by move=> ?; exact: setUA. Qed.
Next Obligation.
rewrite /BindLaws.left_distributive /= => A B m1 m2 k.
rewrite !bindE /Join /= /Monad_of_ret_bind.join /=.
rewrite !(@Monad_of_ret_bind.MapE ModelMonad.SetMonad.functor) /=.
by rewrite setUDl // setUDl.
Qed.
Definition set := MonadAlt.Pack set_class.
End set.

End ModelAlt.

Module ModelAltCI.

Section set.
Local Obligation Tactic := idtac.
Program Definition set_class := @MonadAltCI.Class _
  ModelAlt.set_class (@MonadAltCI.Mixin _ (@setU) _ _).
Next Obligation. by move=> ?; exact: setUid. Qed.
Next Obligation. by move=> ?; exact: setUC. Qed.
Definition set := MonadAltCI.Pack set_class.
End set.

End ModelAltCI.

Module ModelNondet.

Section list.
Local Obligation Tactic := idtac.
Program Definition list_class := @MonadNondet.Class _
  ModelFail.list_class (MonadAlt.mixin ModelAlt.list_class) _.
Next Obligation.
apply: MonadNondet.Mixin => //= A l.
by rewrite /curry /= /Fail /= /ListOps.empty cats0.
Qed.
Definition list := MonadNondet.Pack list_class.
End list.

Section set.
Local Obligation Tactic := idtac.
Program Definition set_class := @MonadNondet.Class _
  ModelFail.set_class (MonadAlt.mixin ModelAlt.set_class) _.
Next Obligation.
by apply: MonadNondet.Mixin => //= A p; rewrite boolp.funeqE => a;
  rewrite boolp.propeqE; rewrite /Fail /= /set0 /setU; split=> [[] // |pa];
  [right|left].
Qed.
Definition set := MonadNondet.Pack list_class.
End set.

End ModelNondet.

Module ModelStateTrace.

Section st.
Variables (S T : UU0).
Local Obligation Tactic := idtac.
Program Definition mk : stateTraceMonad S T :=
let m := Monad.class (@ModelMonad.State.t (S * list T)) in
let stm := @MonadStateTrace.Class S T _ m
(@MonadStateTrace.Mixin _ _ (Monad.Pack m)
 (fun s => (s.1, s)) (* st_get *)
 (fun s' s => (tt, (s', s.2))) (* st_put *)
 (fun t s => (tt, (s.1, rcons s.2 t))) (* st_mark *)
 _ _ _ _ _ _) in
@MonadStateTrace.Pack S T _ stm.
Next Obligation. by []. Qed.
Next Obligation. by []. Qed.
Next Obligation. move=> *; by rewrite boolp.funeqE; case. Qed.
Next Obligation. by []. Qed.
Next Obligation. by []. Qed.
Next Obligation. by []. Qed.
End st.
End ModelStateTrace.

(* see Sect 3.1 of [Wadler, 94] for the model of callcc *)
Definition usual_callcc r (M := fun C => (C -> r) -> r) A B (f : (A -> M B) -> M A) : M A :=
  fun k : A -> r => f (fun a _ => k a) k.

Module ModelCont.
Section modelcont.
Variable r : UU0.
Local Notation M := (ModelMonad.Cont.t r).
Definition callcc (A B : UU0) (f : (A -> M B) -> M A) : M A :=
  ContOps.acallcc_op _ _ (fun k => f (fun x _ => k (Ret x))).
Lemma callccE (A B : UU0) (f : (A -> M B) -> M A) : callcc f = usual_callcc f.
Proof. by []. Qed.
Program Definition t : contMonad := MonadContinuation.Pack (MonadContinuation.Class
  (@MonadContinuation.Mixin (ModelMonad.Cont.t r) callcc _ _ _ _)).
End modelcont.
End ModelCont.

(* we looked at examples from https://qiita.com/suharahiromichi *)
Section continuation_examples.
Fixpoint fib (n : nat) : nat :=
  match n with
    | 0 => 1
    | 1 => 1
    | (m.+1 as sm).+1 => fib sm + fib m
  end.
Fixpoint fib_cps {M : monad} (n : nat) : M nat :=
  match n with
    | 0 => Ret 1
    | 1 => Ret 1
    | (m.+1 as sm).+1 =>
      fib_cps sm >>=
      fun a => fib_cps m >>=
      fun b => Ret (a + b)
  end.

Lemma fib_cpsE (M : monad) n :
  fib_cps n.+2 = (fib_cps n.+1 >>= fun a => fib_cps n >>= fun b => Ret (a + b)) :> M _.
Proof. by []. Qed.
Let nat_ind2 (P : nat -> Prop) (P0 : P O) (P1 : P 1) :
  (forall m, P m -> P m.+1 -> P m.+2) -> forall m, P m.
Proof.
move=> H n; suff : P n /\ P n.+1 by case.
elim: n => // n [] H1 H2; split => //; exact: H.
Qed.
Goal forall (M : monad) n, fib_cps n = Ret (fib n) :> M nat.
Proof.
move=> M; apply nat_ind2 => // n ih1 ih2.
by rewrite fib_cpsE ih2 bindretf ih1 bindretf.
Qed.

Definition oaddn (M : monad) (acc : nat) (x : option nat) : M nat :=
  if x is Some x then Ret (x + acc) else Ret acc.
Definition sum_just M (xs : seq (option nat)) := foldM (oaddn M) 0 xs.

Definition oaddn_break (M : monad) (break : nat -> M nat) (acc : nat) (x : option nat) : M nat :=
  if x is Some x then Ret (x + acc) else break acc.
Let M : contMonad := ModelCont.t nat.
Definition sum_break (xs : seq (option nat)) : M nat :=
  Callcc (fun break : nat -> M nat => foldM (oaddn_break break) 0 xs).

(*
Compute (sum_break [:: Some 2; Some 6; None; Some 4]).
*)

(* example from Sect. 3.1 of [Wadler, 94] *)
Goal Ret 1 +m (Callcc (fun f => Ret 10 +m (f 100))) = Ret (1 + 100) :> M _.
Proof. by rewrite /addM bindretf boolp.funeqE. Abort.

(* https://xavierleroy.org/mpri/2-4/transformations.pdf *)

Fixpoint list_iter (M : monad) A (f : A -> M unit) (s : seq A) : M unit :=
  if s is h :: t then f h >> list_iter f t else Ret tt.

(*
Compute (@list_iter ModelMonad.identity nat (fun a => Ret tt) [:: O; 1; 2]).
*)

Definition list_find (M : contMonad) (A : UU0) (p : pred A) (s : seq A) : M _ :=
  Callcc (fun k => list_iter (fun x => if p x then (*Throw*) k (Some x) else Ret tt) s >> Ret None).

(* returns None if no such element exists *)
(*
Compute (@list_find (@ModelCont.t bool) nat [pred x | odd x] [:: 2; 4; 6]).
*)
(* returns the first element such that *)
(*
Compute (@list_find (@ModelCont.t bool) nat [pred x | odd x] [:: 2; 4; 3; 6]).
*)

End continuation_examples.

(* see Sect. 3.2 of [Wadler, 94] for the model of shift and reset *)
Module ModelShiftReset.
Definition shift r :
    forall A : UU0, ((A -> ModelCont.t r r) -> ModelCont.t r r) -> ModelCont.t r A :=
 fun A h => fun c => h (fun v c' => c' (c v)) ssrfun.id.

Definition reset r : ModelCont.t r r -> ModelCont.t r r :=
  fun m  => fun c => c (m ssrfun.id).

Program Definition t r : shiftresetMonad r :=
  let M : contMonad := ModelCont.t r in
  @MonadShiftReset.Pack _ _ (@MonadShiftReset.Class _ r (MonadContinuation.class M)
 (@MonadShiftReset.Mixin _ _
 (@shift r)
 (@reset r) _ _ _ _ _)).
End ModelShiftReset.

Section shiftreset_examples.
(* see Sect. 3.2 of [Wadler, 94] *)
Let M : monad := ModelShiftReset.t nat.
Goal Ret 1 +m (Reset (Ret 10 +m (Shift (fun f : _ -> M nat => f (100) >>= f) : M _)) : M _) =
     Ret (1 + (10 + (10 + 100))).
Proof. by rewrite /addM bindretf boolp.funeqE. Abort.
Goal Ret 1 +m (Reset (Ret 10 +m (Shift (fun f : _ -> M nat => Ret 100 : M _) : M _)) : M _) =
     Ret (1 + 100).
Proof. by rewrite /addM bindretf boolp.funeqE. Abort.
Goal Ret 1 +m (Reset (Ret 10 +m (Shift (fun f : _ -> M nat => f 100 +m f 1000) : M _)) : M _) =
     Ret (1 + ((10 + 100) + (10 + 1000))).
Proof. by rewrite /addM bindretf boolp.funeqE. Abort.

Let N : monad := ModelShiftReset.t (seq nat).
Fixpoint perverse (l : seq nat) : N (seq nat) :=
  if l is h :: t then
    Shift (fun f : _ -> N _ => Ret h >>= (fun x => perverse t >>= f >>= (fun y => @RET N _ (x :: y))))
  else Ret [::].
Goal Reset (perverse [:: 1; 2; 3]) = Ret [:: 3; 2; 1] :> ModelShiftReset.t _ (seq nat).
by [].
Abort.

Definition stranger :=
  let g b := Reset ((Shift (fun f : _ -> ModelShiftReset.t _ _ => f b) >>=
                           (fun x => if x then Ret 2 else Ret 3)) : ModelShiftReset.t _ _) in
  g true +m g false.
Goal stranger = Ret 5. by []. Abort.

Goal Reset (Ret 2 +m Shift (fun k : _ -> M _ => k 3 +m Ret 1 : M _) : M _) = Ret 6 :> M _.
Proof. by rewrite /addM bindretf boolp.funeqE. Abort.
Goal Reset (Ret 2 *m Shift (fun k : _ -> M _ => k 4 +m Ret 1 : M _)
                  *m Shift (fun k : _ -> M _ => k 3 +m Ret 1 : M _) : M _ ) = Ret 26 :> M _.
Proof. by rewrite /mulM bindretf boolp.funeqE. Abort.

End shiftreset_examples.

(* wip *)
Module ModelStateLoop.
Section modelstateloop.
Variable S : UU0.
Local Notation M := (@ModelMonad.State.t S).
Fixpoint mforeach (it min : nat) (body : nat -> M unit) : M unit :=
  if it <= min then Ret tt
  else if it is it'.+1 then
      (body it') >>= (fun _ => mforeach it' min body)
      else Ret tt.
Program Definition mk : loopStateMonad S :=
let m := @ModelState.state S in
let slm := @MonadStateLoop.Class S _ (MonadState.class m)
  (@MonadStateLoop.Mixin _ m mforeach _ _ ) in
MonadStateLoop.Pack slm.
Next Obligation. by case: m => //= n; rewrite ltnS leqnn. Qed.
Next Obligation. by case: ifPn => //; rewrite ltnNge leq_addr. Qed.
End modelstateloop.
End ModelStateLoop.

Module ModelReify.

Definition mk {S T : UU0} : reifyMonad (S * seq T)%type.
set m := @ModelMonad.State.t (S * seq T)%type.
refine (@MonadReify.Pack _ _ (@MonadReify.Class _ _ (Monad.class m)
  (@MonadReify.Mixin _ m
  (fun A m (s : S * seq T) => Some (m s)) (* reify *) _ _))).
by [].
move=> A B m0 f s.
rewrite !bindE /=.
rewrite /ModelMonad.State.bind /=.
rewrite /Actm /=.
rewrite /Monad_of_ret_bind.Map /=.
rewrite /ModelMonad.State.bind /=.
rewrite /ModelMonad.State.ret /=.
by destruct (m0 s).
Defined.

End ModelReify.

Module ModelStateTraceReify.

Definition mk {S T} :
  stateTraceReifyMonad S T.
refine (let stm := @ModelStateTrace.mk S T in
        let reify := @ModelReify.mk S T in
@MonadStateTraceReify.Pack S T (fun A => S * seq T -> A * (S * seq T))
  (@MonadStateTraceReify.Class S T (fun A => S * seq T -> A * (S * seq T))
    (MonadStateTrace.class stm)
    (MonadReify.mixin (MonadReify.class reify))
    (@MonadStateTraceReify.Mixin _ _ reify _ _ _ _ _ _))).
by [].
by [].
by [].
Defined.

End ModelStateTraceReify.

Module ModelBacktrackableState.
Local Open Scope fset_scope.

Section monad.
Variable S : Type.
Local Obligation Tactic := try by [].

Definition acto : Type -> Type :=
  fun A => S -> {fset (convex.choice_of_Type A * convex.choice_of_Type S)}.

Let ret_component := fun A (a : A) s =>
  [fset (a : convex.choice_of_Type A, s : convex.choice_of_Type S)].

Let bind := fun A B (m : acto A)
  (f : A -> S -> {fset (convex.choice_of_Type B * convex.choice_of_Type S)}) =>
  fun s => \bigcup_(i <- (fun x : [choiceType of convex.choice_of_Type A *
                                           convex.choice_of_Type S] => f x.1 x.2) @` (m s))
                 i.

Definition map A B (f : A -> B) (m : acto A) : acto B :=
  bind m (@ret_component _ \o f).

Lemma map_id : FunctorLaws.id map.
Proof.
move=> A; rewrite /map boolp.funeqE => m.
rewrite /bind boolp.funeqE => s.
rewrite compfid big_imfset /=; last first.
  by move=> [a0 s0] [a1 s1] /= _ _ /fset1_inj.
rewrite /ret_component; apply/fsetP => /= -[a0 s0].
apply/idP/idP.
  case/(@bigfcupP _ _ (m s)) => /= -[a1 s1].
  rewrite andbT => H1 /=.
  by move/fset1P => ->.
move=> H0.
apply/(@bigfcupP _ _ (m s)).
exists (a0, s0) => //.
by rewrite andbT.
by apply/fset1P.
Qed.

Lemma map_comp : FunctorLaws.comp map.
move=> A B C g h.
rewrite /map /bind boolp.funeqE => m.
rewrite boolp.funeqE => s /=.
apply/fsetP => /= -[c0 s0].
apply/idP/idP.
  case/bigfcupP => /= x.
  rewrite andbT => /imfsetP /= -[[a1 s1] H1] ->{x} /=.
  rewrite /ret_component => /fset1P [->{c0} ->{s0}].
  apply/bigfcupP => /=.
  eexists; last exact/fset1P.
  rewrite andbT.
  apply/imfsetP => /=.
  exists ((h a1), s1).
  apply/bigfcupP => /=.
  eexists; last exact/fset1P.
  rewrite andbT.
  apply/imfsetP => //=.
  eexists.
  exact: H1.
  by [].
  by [].
case/bigfcupP => /= x.
rewrite andbT.
case/imfsetP => /= -[b1 s1].
move/bigfcupP => /= -[bs].
rewrite andbT.
move/imfsetP => /= [[a2 s2]] H2 ->{bs} /= /fset1P -[->{b1} ->{s1}] ->{x}.
move/fset1P => [->{c0} ->{s0}].
apply/bigfcupP => /=.
eexists; last exact/fset1P.
rewrite andbT.
by apply/imfsetP; exists (a2, s2).
Qed.

Definition func := Functor.Pack (Functor.Mixin map_id map_comp).

Lemma naturality_ret : naturality FId func ret_component.
Proof.
move=> A B h; rewrite /ret_component boolp.funeqE => a; rewrite boolp.funeqE => s.
by rewrite /func /Actm /map /bind /= imfset_set1 /= big_seq_fset1.
Qed.

Definition ret : FId ~> func := Natural.Pack (Natural.Mixin naturality_ret).

Program Definition t := @Monad_of_ret_bind _ ret bind _ _ _.
Next Obligation.
move=> A B /= m f; rewrite boolp.funeqE => s.
by rewrite /bind /ret imfset_set1 /= big_seq_fset1.
Qed.
Next Obligation.
move=> A B /=; rewrite boolp.funeqE => s.
apply/fsetP => /= x; apply/bigfcupP'; case: ifPn => xBs.
  set x' := (x : [choiceType of convex.choice_of_Type A * convex.choice_of_Type S]).
  exists [fset x']; last by rewrite inE.
    apply/imfsetP; exists x' => //=.
  by case: x'.
case => /= SA /imfsetP[] /= sa saBs ->{SA} /fset1P => Hx.
move: xBs; rewrite Hx; apply/negP; rewrite negbK; by case: sa saBs Hx.
Qed.
Next Obligation.
move=> A B C /= m f g; rewrite boolp.funeqE => s.
have @g' : convex.choice_of_Type B -> convex.choice_of_Type S -> {fset convex.choice_of_Type C * convex.choice_of_Type S}.
  move=> b' s'; exact: (g b' s').
apply/fsetP => /= x; apply/bigfcupP'/bigfcupP'; case => /= CS  /imfsetP[/=].
- move=> bs /bigfcupP'[/= BS]  /imfsetP[/= sa] sams ->{BS} bsfsa ->{CS} xgbs.
  exists (\bigcup_(i <- [fset g' x0.1 x0.2 | x0 in f sa.1 sa.2]) i).
    by apply/imfsetP => /=; exists sa.
  apply/bigfcupP'; exists (g bs.1 bs.2) => //; by apply/imfsetP => /=; exists bs.
- move=> sa sams ->{CS} /bigfcupP'[/= CS]  /imfsetP[/= bs] bsfsa ->{CS} xgbs.
  exists (g bs.1 bs.2) => //; apply/imfsetP => /=; exists bs => //.
  apply/bigfcupP' => /=; exists (f sa.1 sa.2) => //; by apply/imfsetP => /=; exists sa.
Qed.
Lemma BindE (A B : Type) m (f : A -> t B) :
  m >>= f = fun s => \bigcup_(i <- (fun x : [choiceType of convex.choice_of_Type A * convex.choice_of_Type S] => f x.1 x.2) @` (m s)) i.
Proof.
rewrite boolp.funeqE => s.
rewrite /Bind /Join /= /Monad_of_ret_bind.join /=.
rewrite /bind.
set lhs := [fset _ _ | _ in _].
set rhs := [fset _ _ | _ in _].
rewrite (_ : lhs = rhs) //; apply/fsetP => x; rewrite {}/lhs {}/rhs.
apply/idP/imfsetP => /=.
- case/imfsetP => -[a1 a2] /=.
  rewrite /Actm /=.
  rewrite /Monad_of_ret_bind.Map /=.
  case/bigfcupP' => /= b.
  by case/imfsetP => -[b1 b2] /= Hb ->{b} /fset1P[-> -> ->{x a1 a2}]; exists (b1, b2).
- case=> -[a1 s1] Ha /= ->{x}.
  apply/imfsetP => /=.
  rewrite /Actm /= /Monad_of_ret_bind.Map /=.
  eexists.
  + apply/bigfcupP' => /=.
    eexists.
      apply/imfsetP => /=.
      by exists (a1, s1).
    apply/fset1P; reflexivity.
  + by [].
Qed.

End monad.

Section state.
Variable S : Type.
Local Obligation Tactic := idtac.

Program Definition _state : stateMonad S :=
  @MonadState.Pack S (acto S)
  (@MonadState.Class S (acto S) (Monad.class (t S)) (@MonadState.Mixin S (t S)
((fun s => [fset (s : convex.choice_of_Type S , s : convex.choice_of_Type S)]) : (t S S)) (* get *)
((fun s => (fun _ => [fset (tt : convex.choice_of_Type unit, s : convex.choice_of_Type S)])) : S -> (t S unit)) (* put *)
_ _ _ _)).
Next Obligation.
move=> s s'; rewrite boolp.funeqE => s''.
rewrite BindE; apply/fsetP => /= x; apply/bigfcupP'/fset1P.
- by case => /= x0 /imfsetP[/= x1] /fset1P _ -> /fset1P.
- move=> -> /=.
  exists [fset ((tt, s') : [choiceType of convex.choice_of_Type unit * convex.choice_of_Type S])] => /=; last first.
    exact/fset1P.
  apply/imfsetP => /=; exists (tt, s) => //; exact/fset1P.
Qed.
Next Obligation.
move=> s; rewrite boolp.funeqE => s'.
rewrite 2!BindE /=; apply/fsetP => /= x; apply/bigfcupP'/bigfcupP'.
- case => /= x0 /imfsetP[/= x1] /fset1P -> -> /fset1P ->.
  exists [fset ((s, s) : [choiceType of convex.choice_of_Type S * convex.choice_of_Type S])]; last first.
    exact/fset1P.
  apply/imfsetP => /=; exists (tt, s) => //; exact/fset1P.
- case => /= x0 /imfsetP[/= x1] /fset1P -> -> /fset1P ->.
  exists [fset ((s ,s) : [choiceType of convex.choice_of_Type S * convex.choice_of_Type S])]; last first.
    exact/fset1P.
  apply/imfsetP => /=; exists (tt, s) => //; exact/fset1P.
Qed.
Next Obligation.
rewrite boolp.funeqE => s.
rewrite BindE /skip /= /Ret; apply/fsetP => /= x; apply/bigfcupP'/idP.
- case => /= x0 /imfsetP[/= x1] /fset1P -> -> /fset1P ->; exact/fset1P.
- move/fset1P => ->; exists [fset ((tt, s) : [choiceType of convex.choice_of_Type unit * convex.choice_of_Type S])]; last first.
    exact/fset1P.
  apply/imfsetP; exists (s, s) => //; by rewrite inE.
Qed.
Next Obligation.
move=> A k; rewrite boolp.funeqE => s.
rewrite 2!BindE; apply/fsetP => x; apply/bigfcupP'/bigfcupP'.
- case => /= x0 /imfsetP[/= x1] /fset1P -> ->.
  rewrite BindE => /bigfcupP'[/= x2] /imfsetP[/= x3] /fset1P -> -> xkss.
  exists (k s s s) => //; apply/imfsetP; exists (s, s) => //; by rewrite inE.
- case => /= x0 /imfsetP[/= x1] /fset1P -> -> /= xksss.
  have @k' : convex.choice_of_Type S -> convex.choice_of_Type S -> (convex.choice_of_Type S -> {fset convex.choice_of_Type A * convex.choice_of_Type S}).
    move=> a b s'; exact: (k a b s').
  exists (\bigcup_(i <- [fset k' (s, s).1 x2.1 x2.2 | x2 in [fset (((s, s).2, (s, s).2) : [choiceType of convex.choice_of_Type S * convex.choice_of_Type S])]]) i).
    apply/imfsetP ; exists (s, s); by [rewrite inE | rewrite BindE].
  apply/bigfcupP'; exists (k s s s) => //;   apply/imfsetP; exists (s, s) => //=; exact/fset1P.
Qed.

End state.

Section fail.
Variable S : choiceType.
Program Definition _fail : failMonad := @MonadFail.Pack _
  (@MonadFail.Class _ (Monad.class (t S))
    (@MonadFail.Mixin _ (fun (A : Type) (_ : S) => fset0) _)).
Next Obligation.
move=> A B g; rewrite boolp.funeqE => s; apply/fsetP => x; rewrite inE BindE; apply/negbTE.
apply/bigfcupP'; case => /= x0 /imfsetP[/= sa].
by rewrite (@in_fset0 [choiceType of convex.choice_of_Type A * convex.choice_of_Type S]).
Qed.

End fail.

Section alt.

Variable S : choiceType.
Local Obligation Tactic := try by [].
Program Definition _alt : altMonad := @MonadAlt.Pack _
  (@MonadAlt.Class _ (@Monad.class (t S))
    (@MonadAlt.Mixin (t S)
      (fun (A : Type) (a b : S -> {fset [choiceType of convex.choice_of_Type A * convex.choice_of_Type S]}) (s : S) => a s `|` b s) _ _)).
Next Obligation. by move=> A a b c; rewrite boolp.funeqE => s; rewrite fsetUA. Qed.
Next Obligation.
move=> A B /= m1 m2 k; rewrite boolp.funeqE => s; rewrite !BindE /=.
apply/fsetP => /= bs; apply/bigfcupP'/fsetUP.
- case => /= BS /imfsetP[/= sa] /fsetUP[sam1s ->{BS} Hbs|sam2s ->{BS} Hbs].
  + left; apply/bigfcupP' => /=; exists (k sa.1 sa.2) => //; apply/imfsetP; by exists sa.
  + right; apply/bigfcupP' => /=; exists (k sa.1 sa.2) => //; apply/imfsetP; by exists sa.
- case => /bigfcupP'[/= BS /imfsetP[/= sa sams ->{BS} bsksa]].
  by exists (k sa.1 sa.2) => //; apply/imfsetP; exists sa => //; rewrite inE sams.
  by exists (k sa.1 sa.2) => //; apply/imfsetP; exists sa => //; rewrite inE sams orbT.
Qed.

End alt.

Section nondet.

Variable S : choiceType.
Local Obligation Tactic := try by [].
Program Definition nondetbase : nondetMonad :=
  @MonadNondet.Pack _ (@MonadNondet.Class _ (@MonadFail.class (_fail S))
    (@MonadAlt.mixin (_alt S) _) (@MonadNondet.Mixin _ _ _ _)).
Next Obligation. move=> A /= m; rewrite boolp.funeqE => s; by rewrite fset0U. Qed.
Next Obligation. move=> A /= m; rewrite boolp.funeqE => s; by rewrite fsetU0. Qed.
End nondet.

Section failR0monad.
Variable S : choiceType.
Local Obligation Tactic := try by [].
Program Definition failR0base : failR0Monad :=
  @MonadFailR0.Pack _ (@MonadFailR0.Class _ (MonadNondet.base (MonadNondet.class (nondetbase S))) (@MonadFailR0.Mixin _ _)).
Next Obligation.
move=> A B /= g; rewrite !BindE /=; rewrite boolp.funeqE => s; apply/fsetP => /= sa.
apply/idP/idP/bigfcupP'.
case => /= SA /imfsetP[/= bs bsgs ->{SA}].
by rewrite (@in_fset0 [choiceType of convex.choice_of_Type A * convex.choice_of_Type S]).
Qed.
End failR0monad.

Section preplusmonad.

Variable S : choiceType.
Local Obligation Tactic := try by [].
Program Definition preplusbase : prePlusMonad :=
  @MonadPrePlus.Pack _ (@MonadPrePlus.Class _ (@MonadNondet.class (nondetbase S)) (MonadFailR0.mixin (@MonadFailR0.class (failR0base S))) (@MonadPrePlus.Mixin _ _)).
Next Obligation.
move=> A B /= m k1 k2; rewrite boolp.funeqE => s; rewrite !BindE /=; apply/fsetP => /= bs.
apply/bigfcupP'/idP.
- case => /= BS /imfsetP[/= sa sams ->{BS}] /fsetUP[bsk1|bsk2].
  + apply/fsetUP; left; apply/bigfcupP'; exists (k1 sa.1 sa.2) => //.
    apply/imfsetP; by exists sa.
  + apply/fsetUP; right; apply/bigfcupP'; exists (k2 sa.1 sa.2) => //.
    apply/imfsetP; by exists sa.
- move/fsetUP => [|] /bigfcupP'[/= BS] /imfsetP[/= sa sams ->{BS}] bsk.
  exists (k1 sa.1 sa.2 `|` k2 sa.1 sa.2).
    apply/imfsetP; by exists sa.
  by apply/fsetUP; left.
  exists (k1 sa.1 sa.2 `|` k2 sa.1 sa.2).
    apply/imfsetP; by exists sa.
  by apply/fsetUP; right.
Qed.

End preplusmonad.

Section nondetstate.

Variable S : choiceType.
Definition nondetstate : nondetStateMonad S :=
  @MonadNondetState.Pack _ _
    (@MonadNondetState.Class _ _ (MonadPrePlus.class (preplusbase S))
      (MonadState.mixin (MonadState.class (_state S)))).

End nondetstate.

End ModelBacktrackableState.

(* result of a discussion with Maxime and Enrico on 2019-09-12 *)
Section eq_rect_ret.
Variable X : UU0.
Let U  : UU1 := functor.
Let Q : U -> UU0 := Functor.acto^~ X.

Lemma eq_rect_ret (p p' : U) (K : Q p' = Q p) (x : Q p') (h : p = p') :
  x = eq_rect p Q (eq_rect _ (fun X : UU0 => id X) x _ K) p' h.
Proof.
rewrite /eq_rect; destruct h; rewrite (_ : K = erefl) //; exact/proof_irr.
Qed.

Lemma eq_rect_state_ret S (p := ModelMonad.State.functor S : U)
  (p' := MS_functor S ModelMonad.identity : U)
  (x : Q p') (h : p = p') : x = eq_rect p Q x p' h.
Proof.
have K : Q p' = Q p by [].
rewrite {2}(_ : x = eq_rect _ (fun x : UU0 => x) x _ K) //; first exact: eq_rect_ret.
rewrite /eq_rect (_ : K = erefl) //; exact/proof_irr.
Qed.

Lemma eq_rect_error_ret (E : UU0) (p : U := ModelMonad.Except.functor E)
  (p' : U := MX_functor E ModelMonad.identity)
  (x : Q p') (h : p = p') : x = eq_rect p Q x p' h.
Proof.
have K : Q p' = Q p by [].
rewrite {2}(_ : x = eq_rect _ (fun x : UU0 => x) x _ K) //; first exact: eq_rect_ret.
rewrite /eq_rect (_ : K = erefl) //; exact/proof_irr.
Qed.

Lemma eq_rect_cont_ret r (p : U := ModelMonad.Cont.functor r)
  (p' : U := MC_functor r ModelMonad.identity)
  (x : Q p') (h : p = p') : x = eq_rect p Q x p' h.
Proof.
have K : Q p' = Q p by [].
rewrite {2}(_ : x = eq_rect _ (fun x : UU0 => x) x _ K) //; first exact: eq_rect_ret.
rewrite /eq_rect (_ : K = erefl) //; exact/proof_irr.
Qed.

End eq_rect_ret.

Section eq_rect_bind.
Let U : Type := functor.
Let Q : U -> Type := fun F => forall A B, Functor.acto F A -> (A -> Functor.acto F B) -> Functor.acto F B.

Lemma eq_rect_bind (p p' : U) (K : Q p' = Q p) (x : Q p') (h : p = p') :
  x = eq_rect p Q (eq_rect _ id x _ K) p' h.
Proof.
rewrite /eq_rect; destruct h; rewrite (_ : K = erefl) //; exact/proof_irr.
Qed.

Lemma eq_rect_bind_state S (p : U := ModelMonad.State.functor S)
  (p' : U := MS_functor S ModelMonad.identity)
  (x : Q p') (h : p = p') : x = eq_rect p Q x p' h.
Proof.
have K : Q p' = Q p by [].
rewrite {2}(_ : x = eq_rect _ id x _ K); first exact: eq_rect_bind.
rewrite /eq_rect (_ : K = erefl) //; exact/proof_irr.
Qed.

Lemma eq_rect_bind_error E (p : U := ModelMonad.Except.functor E)
  (p' : U := MX_functor E ModelMonad.identity)
  (x : Q p') (h : p = p') : x = eq_rect p Q x p' h.
Proof.
have K : Q p' = Q p by [].
rewrite {2}(_ : x = eq_rect _ id x _ K) //; first exact: eq_rect_bind.
rewrite /eq_rect (_ : K = erefl) //; exact/proof_irr.
Qed.

Lemma eq_rect_bind_cont S (p : U := ModelMonad.Cont.functor S)
  (p' : U := MC_functor S ModelMonad.identity)
  (x : Q p') (h : p = p') : x = eq_rect p Q x p' h.
Proof.
have K : Q p' = Q p by [].
rewrite {2}(_ : x = eq_rect _ id x _ K) //; first exact: eq_rect_bind.
rewrite /eq_rect (_ : K = erefl) //; exact/proof_irr.
Qed.

End eq_rect_bind.

Section instantiations_with_the_identity_monad.

Lemma stateT_id_ModelState S :
  stateT S ModelMonad.identity = ModelMonad.State.t S.
Proof.
rewrite /= /stateTmonadM /ModelMonad.State.t.
have FG : MS_functor S ModelMonad.identity = ModelMonad.State.functor S.
  apply: functor_ext => /=; apply fun_ext_dep => A; apply fun_ext_dep => B.
  rewrite boolp.funeqE => f; rewrite boolp.funeqE => m; rewrite boolp.funeqE => s.
  by rewrite /MS_map /Actm /= /ModelMonad.State.map; destruct (m s).
apply (@monad_of_ret_bind_ext _ _ _ _ _ _ FG) => /=.
  apply/natural_ext => A a /=; exact: eq_rect_state_ret _ (esym FG).
set x := @bindS _ _; exact: (@eq_rect_bind_state S x (esym FG)).
Qed.

Lemma exceptT_id_ModelExcept (Z : UU0) :
  exceptT Z ModelMonad.identity = ModelMonad.Except.t Z.
Proof.
rewrite /= /exceptTmonadM /ModelMonad.Except.t.
have FG : MX_functor Z ModelMonad.identity = ModelMonad.Except.functor Z.
  apply: functor_ext => /=; apply fun_ext_dep => A; apply fun_ext_dep => B.
  rewrite boolp.funeqE => f; rewrite boolp.funeqE => m.
  by rewrite /MX_map /Actm /= /ModelMonad.Except.map; destruct m.
apply (@monad_of_ret_bind_ext _ _ _ _ _ _ FG) => /=.
  apply/natural_ext => A a /=; exact: (eq_rect_error_ret _ (esym FG)).
set x := @bindX _ _; exact: (@eq_rect_bind_error Z x (esym FG)).
Qed.

Lemma contT_id_ModelCont r :
  contT r ModelMonad.identity = ModelMonad.Cont.t r.
Proof.
rewrite /= /contTmonadM /ModelMonad.Cont.t.
have FG : MC_functor r ModelMonad.identity = ModelMonad.Cont.functor r.
  apply: functor_ext => /=; apply fun_ext_dep => A; apply fun_ext_dep => B.
  by rewrite boolp.funeqE => f; rewrite boolp.funeqE => m.
apply (@monad_of_ret_bind_ext _ _ _ _ _ _ FG) => /=.
  apply/natural_ext => A a /=; exact: (@eq_rect_cont_ret A r _ (esym FG)).
set x := @bindC _ _; exact: (@eq_rect_bind_cont r x (esym FG)).
Qed.

End instantiations_with_the_identity_monad.

Section monad_transformer_calcul.

Let contTi := @contT^~ ModelMonad.identity.
Let callcci := ModelCont.callcc.

Definition break_if_none (m : monad) (break : _) (acc : nat) (x : option nat) : m nat :=
  if x is Some x then Ret (x + acc) else break acc.

Definition sum_until_none (xs : seq (option nat)) : contTi nat nat :=
  callcci (fun break : nat -> contTi nat nat => foldM (break_if_none break) 0 xs).

Goal sum_until_none [:: Some 2; Some 6; None; Some 4] = @^~ 8.
by cbv.
Abort.

Definition calcul : contTi nat nat :=
  (contTi _ # (fun x => 8 + x))
  (callcci (fun k : _ -> contTi nat _ => (k 5) >>= (fun y => Ret (y + 4)))).

Goal calcul = @^~ 13.
by cbv.
Abort.

End monad_transformer_calcul.

Section examples_of_algebraic_lifting.

Section state_exceptT.
Let M S : monad := ModelState.state S.

Definition aLGet {Z S} : (StateOps.Get.func S).-aoperation (exceptT Z (M S)) :=
  alifting (StateOps.get_aop S) (Lift (exceptT Z) (M S)).

Definition aLPut {Z S} : (StateOps.Put.func S).-operation (exceptT Z (M S)) :=
  alifting (StateOps.put_aop S) (Lift (exceptT Z) (M S)).

Goal forall Z (S : UU0) X (k : S -> exceptT Z (M S) X), aLGet _ k = StateOps.get_op _ k.
by [].
Abort.

Goal forall Z S, aLGet _ Ret = Lift (exceptT Z) (M S) _ (@ModelState.get S).
by [].
Abort.

End state_exceptT.

Section continuation_stateT.
Variable (r S : UU0).
Let M : monad := ModelCont.t r.
Let stS : monadT := stateT S.

Definition aLCallcc : (ContOps.Acallcc.func r).-aoperation (stS M) :=
  alifting (ContOps.callcc_aop r) (Lift stS M).

Goal forall A (f : (stS M A -> r) -> stS M A),
  aLCallcc _ f = (fun s k => f (fun m => uncurry m (s, k)) s k) :> stS M A.
move=> A f.
by rewrite /aLCallcc /= /stS /= /stateT /= /stateTmonadM /=; unlock.
Abort.

Definition usual_callccS (A B : UU0) (f : (A -> stS M B) -> stS M A) : stS M A :=
  fun s k => f (fun x _ _ => k (x, s)) s k.

Lemma callccS_E A B f : @aLCallcc _
    (fun k : stS M A -> r =>
       f (fun x => (fun (_ : S) (_ : B * S -> r) => k (@RET (stS M) A x)) : stS M B)) =
  usual_callccS f.
Proof.
by rewrite /aLCallcc /= /stS /= /stateT /= /stateTmonadM /=; unlock.
Qed.

End continuation_stateT.

End examples_of_algebraic_lifting.

Module ModelMonadStateRun.
Section modelmonadstaterun.
Variable S : UU0.
Let N : monad := ModelExcept.t.
Definition M : stateMonad S := stateMonad_of_stateT(*stateT*) S N.

Local Obligation Tactic := idtac.
Program Definition t : stateRunMonad S N :=
  @MonadStateRun.Pack S N (MS S N) (@MonadStateRun.Class S N _
    (MonadState.Class (@MonadState.Mixin S _ (@Get _ M) (@Put _ M) _ _ _ _))
    (@MonadStateRun.Mixin S N _
      (fun A : UU0 => id) (*runStateT*)
      _ _ _ _)).
Next Obligation. move=> s s'; exact: (putput (stateMonad_of_stateT S N)). Qed.
Next Obligation. move=> s; exact: (putget (stateMonad_of_stateT S N)). Qed.
Next Obligation. exact: (getputskip (stateMonad_of_stateT S N)). Qed.
Next Obligation. exact: (@getget _ (stateMonad_of_stateT S N)). Qed.
Next Obligation. by []. Qed.
Next Obligation.
move=> A M m f s /=; rewrite /t_obligation_5.
rewrite /Bind /bindS /= /ModelMonad.Except.bind /= /Actm /=.
rewrite /Monad_of_ret_bind.Map /= /ModelMonad.Except.bind /=.
by case: (m s) => // -[].
Qed.
Next Obligation. by []. Qed.
Next Obligation. by []. Qed.

End modelmonadstaterun.
End ModelMonadStateRun.

Module ModelMonadExceptStateRun.
Section modelmonadexceptstaterun.
Variable S : UU0.
Let N : exceptMonad := ModelExcept.t.
Definition M : stateRunMonad S N := ModelMonadStateRun.t S.

Local Obligation Tactic := idtac.
Program Definition t : exceptStateRunMonad S N :=
  @MonadExceptStateRun.Pack S N (MS S N)
    (@MonadExceptStateRun.Class S N (MS S N)
       (@MonadExcept.Class (MS S N) _ _)
       (MonadState.mixin (MonadState.class (ModelMonadStateRun.t S)))
       (MonadStateRun.mixin (MonadStateRun.class M))
       (MonadExceptStateRun.Mixin _ _)).
Next Obligation.
pose X : forall A : UU0, M A := fun A => liftS (@Fail N _).
by refine (@MonadFail.Class _ _ (@MonadFail.Mixin _ X _)).
Defined.
Next Obligation.
set f := fun A : UU0 => mapStateT2 (@Catch N (A * S)%type).
refine (@MonadExcept.Mixin (MonadFail.Pack t_obligation_1) f _ _ _ _).
by move=> A x; rewrite /f /mapStateT2 boolp.funeqE => s; rewrite catchmfail.
by move=> A x; rewrite /f /mapStateT2 boolp.funeqE => s; rewrite catchfailm.
by move=> A; rewrite /f /mapStateT2 => a b c; rewrite boolp.funeqE => s; rewrite catchA.
by move=> A x y; rewrite /f /mapStateT2 boolp.funeqE => s; rewrite catchret.
Defined.
Next Obligation. by []. Defined.
Next Obligation. by []. Defined.
Next Obligation. by []. Defined.
Next Obligation. by []. Defined.

End modelmonadexceptstaterun.
End ModelMonadExceptStateRun.
