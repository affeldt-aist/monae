From mathcomp Require Import all_ssreflect.
From mathcomp Require Import finmap.
From mathcomp Require Import classical_sets.
Require Import imonae_lib ihierarchy imonad_lib ifail_lib istate_lib itrace_lib.
Require Import imonad_transformer.

(******************************************************************************)
(*                       Models for various monads                            *)
(*                                                                            *)
(* Sample models for the monads in monad.v, fail_monad.v, state_monad.v,      *)
(* trace_monad.v.                                                             *)
(*                                                                            *)
(* identity                                                                   *)
(* ListMonad.t                                                                *)
(* Except.t (exception or error monad)                                        *)
(*   option_monad                                                             *)
(* Output.t                                                                   *)
(* Environment.t                                                              *)
(* State.t                                                                    *)
(* Cont.t                                                                     *)
(*                                                                            *)
(* Sigma-operations:                                                          *)
(* ListOps                                                                    *)
(* OutputOps                                                                  *)
(* EnvironmentOps                                                             *)
(* ExceptOps                                                                  *)
(* StateOps                                                                   *)
(* ContOps                                                                    *)
(*                                                                            *)
(* ModelFail                                                                  *)
(* ModelExcept                                                                *)
(* ModelState                                                                 *)
(* ModelAlt                                                                   *)
(* ModelAltCI                                                                 *)
(* ModelNondet                                                                *)
(* ModelStateTrace                                                            *)
(* ModelCont                                                                  *)
(* ModelStateTraceRun                                                         *)
(*                                                                            *)
(* Equality between monads from the hierarchy and their counterparts built    *)
(* using monad transformers and the identity monad:                           *)
(* - state_monad_stateT, error_monad_errorT, cont_monad_contT                 *)
(*                                                                            *)
(* references:                                                                *)
(* - Wadler, P. Monads and composable continuations. LISP and Symbolic        *)
(*   Computation 7, 39–55 (1994)                                              *)
(******************************************************************************)

Import Univ.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.

Section PR.
Local Open Scope fset_scope.
Section ImfsetTh.
Variables (key : unit) (K V : choiceType).
Variable (f : K -> V).
Lemma imfset_set1 x : f @` [fset x] = [fset f x].
Proof.
apply/fsetP => y.
by apply/imfsetP/fset1P=> [[x' /fset1P-> //]| ->]; exists x; rewrite ?fset11.
Qed.
End ImfsetTh.
Section BigOps.
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
End BigOps.
End PR.

Module ModelMonad.

Section identity.
Local Obligation Tactic := by [].
Definition identity_functor : FId ~> FId := Natural.Pack (Natural.Mixin (@natural_id FId)).
Program Definition identity := @Monad_of_ret_bind _ identity_functor
  (fun A B (a : id A) (f : A -> id B) => f a) _ _ _.
End identity.

Module ListMonad.
Section listmonad.
Definition acto := fun A => seq A.
Local Notation M := acto.
Lemma map_id : @FunctorLaws.id seq (@map).
Proof. by move=> A; apply fun_ext => x; rewrite map_id. Qed.
Lemma map_comp : @FunctorLaws.comp seq (@map).
Proof. by move=> A B C g h; apply fun_ext => x; rewrite map_comp. Qed.
Definition functor := Functor.Pack (Functor.Mixin map_id map_comp).
Definition ret_component := fun A : Type => (@cons A)^~ [::].
Lemma ret_naturality : naturality FId functor ret_component.
Proof. by move=> A B h; apply fun_ext. Qed.
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

Module Except.
Section except.
Variable E : UU0.
Definition acto := fun A : UU0 => (E + A)%type.
Local Notation M := acto.
Definition map := fun (A B : UU0) (f : A -> B) (a : M A) =>
  match a with inl z => inl z | inr b => inr (f b) end.
Lemma map_id : FunctorLaws.id map.
Proof. by move=> *; apply fun_ext; case. Qed.
Lemma map_comp : FunctorLaws.comp map.
Proof. by move=> *; apply fun_ext; case. Qed.
Definition functor := Functor.Pack (Functor.Mixin map_id map_comp).
Definition ret_component := @inr E.
Lemma natural : naturality FId functor ret_component.
Proof. by move=> A B h; apply fun_ext. Qed.
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
Proof. by move=> A; apply fun_ext; case. Qed.
Lemma map_comp : FunctorLaws.comp map.
Proof. by move=> A B C g h; apply fun_ext; case. Qed.
Definition functor := Functor.Pack (Functor.Mixin map_id map_comp).
Definition ret_component : FId ~~> M := fun A a => (a, [::]).
Lemma naturality_ret : naturality FId functor ret_component.
Proof. by move=> A B h; apply fun_ext. Qed.
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
Proof. by move=> A B C g h; apply fun_ext. Qed.
Definition functor := Functor.Pack (Functor.Mixin map_id map_comp).
Definition ret_component : FId ~~> M := fun A x => fun e => x.
(* computation that ignores the environment *)
Lemma naturality_ret : naturality FId functor ret_component.
Proof. by move=> A B h; apply fun_ext. Qed.
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
Variable S : UU0.
Definition acto := fun A : UU0 => S -> A * S.
Local Notation M := acto.
Definition map (A B : UU0) (f : A -> B) (m : M A) : M B :=
 fun (s : S) => let (x1, x2) := m s in (f x1, x2).
Lemma map_id : FunctorLaws.id map.
Proof.
move=> x; apply fun_ext => y; apply fun_ext => z /=.
by  rewrite /map; case: y.
Qed.
Lemma map_comp : FunctorLaws.comp map.
Proof.
move=> A B C g h; apply fun_ext => m; apply fun_ext => s.
by rewrite /map /=; case: m.
Qed.
Definition functor := Functor.Pack (Functor.Mixin map_id map_comp).
Definition ret_component : FId ~~> M := fun A a => fun s => (a, s).
Lemma naturality_ret : naturality FId functor ret_component.
Proof. by move=> A B h; apply fun_ext => a /=; apply fun_ext. Qed.
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
Proof. by move=> A; apply fun_ext => m; apply fun_ext. Qed.
Lemma map_comp : FunctorLaws.comp actm.
Proof. by move=> *; apply fun_ext => m; apply fun_ext. Qed.
Definition functor := Functor.Pack (Functor.Mixin map_id map_comp).
Lemma naturality_ret : naturality FId functor (fun A a => fun k => k a).
Proof. by move=> A B f; apply fun_ext => a /=; apply fun_ext. Qed.
Definition ret : FId ~> functor := Natural.Pack (Natural.Mixin naturality_ret).
Definition bind := fun A B (ma : M A) (f : A -> M B) => fun k => ma (fun a => f a k).
Lemma left_neutral : @BindLaws.left_neutral functor bind ret.
Proof. by move=> A B a f; apply fun_ext => Br. Qed.
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
Next Obligation. by move=> A; apply fun_ext; case. Qed.
Next Obligation. by move=> A B C f g; apply fun_ext; case. Qed.
End Empty.

Module Append.
Definition acto (X : Type) := (X * X)%type.
Definition actm X Y (f : X -> Y) (t : acto X) : acto Y :=
  let: (x1, x2) := t in (f x1, f x2).
Program Definition func := Functor.Pack (@Functor.Mixin _ actm _ _).
Next Obligation. by move=> A; apply fun_ext; case. Qed.
Next Obligation. by move=> A B C f g; apply fun_ext; case. Qed.
End Append.

Local Notation M := ModelMonad.ListMonad.t.

Definition empty A : unit -> M A := fun _ => @nil A.
Lemma naturality_empty : naturality (Empty.func \O M) M empty.
Proof. by move=> A B h; apply fun_ext. Qed.
Definition empty_op : Empty.func.-operation M := Natural.Pack (Natural.Mixin naturality_empty).
Lemma algebraic_empty : algebraicity empty_op.
Proof. by []. Qed.

Definition append A : (M A * M A)%type -> M A :=
  fun x => let: (s1, s2) := x in (s1 ++ s2).
Lemma naturality_append : naturality (Append.func \O M) M append.
Proof.
move=> A B h; apply fun_ext; case => s1 s2 /=.
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
Next Obligation. by move=> A; apply fun_ext; case. Qed.
Next Obligation. by move=> A B C f g; apply fun_ext; case. Qed.
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
move=> A B h; apply fun_ext; case => w [x w'] /=.
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
Proof. by move=> A B h; apply fun_ext; case. Qed.
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
apply fun_ext => w.
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
Next Obligation. by move=> A; apply fun_ext; case. Qed.
Next Obligation. by move=> A B C g h; apply fun_ext; case. Qed.
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
Proof. by move=> A B h; apply fun_ext; case. Qed.
Definition local_op : (Local.func E).-operation M :=
  Natural.Pack (Natural.Mixin naturality_local).
(* NB: local is not algebraic *)
Lemma algebraic_local : algebraicity local_op.
Proof.
move=> A B f t.
rewrite /local_op /=.
rewrite /local /=.
apply fun_ext => e /=.
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
Next Obligation. by move=> A; apply fun_ext; case. Qed.
Next Obligation. by move=> A B C g h; apply fun_ext; case. Qed.
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
Proof. by move=> A B h; apply fun_ext; case; case. Qed.
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
Next Obligation. by move=> A; apply fun_ext. Qed.
Next Obligation. by move=> A B C g h; apply fun_ext. Qed.
End get. End Get.

Module Put. Section put. Variable S : UU0.
Definition acto (X : UU0) := (S * X)%type.
Definition actm (X Y : UU0) (f : X -> Y) (sx : acto X) : acto Y := (sx.1, f sx.2).
Program Definition func := Functor.Pack (@Functor.Mixin _ actm _ _).
Next Obligation. by move=> A; apply fun_ext; case. Qed.
Next Obligation. by move=> A B C g h; apply fun_ext. Qed.
End put. End Put.

Section stateops.
Variable S : UU0.
Local Notation M := (ModelMonad.State.t S).

Definition get A (k : S -> M A) : M A := fun s => k s s.
Lemma naturality_get : naturality (Get.func S \O M) M get.
Proof.
move=> A B h; apply fun_ext => /= m /=.
by apply fun_ext => s; rewrite FCompE.
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
by apply fun_ext => /=; case => s m /=; apply fun_ext.
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

End ModelAlt.

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

End ModelNondet.

Module ModelStateTrace.

Section st.
Variables (S T : UU0).
Local Obligation Tactic := idtac.
Program Definition mk : stateTraceMonad S T :=
let m := Monad.class (@ModelMonad.State.t (S * list T)%type) in
let stm := @MonadStateTrace.Class S T _ m
(@MonadStateTrace.Mixin _ _ (Monad.Pack m)
 (fun s => (s.1, s)) (* st_get *)
 (fun s' s => (tt, (s', s.2))) (* st_put *)
 (fun t s => (tt, (s.1, rcons s.2 t))) (* st_mark *)
 _ _ _ _ _ _) in
@MonadStateTrace.Pack S T _ stm.
Next Obligation. by []. Qed.
Next Obligation. by []. Qed.
Next Obligation. move=> *; by apply fun_ext; case. Qed.
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
Proof. by rewrite /addM bindretf; apply fun_ext. Abort.

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

Module ModelRun.

Definition mk {S T : UU0} : runMonad (S * seq T)%type.
set m := @ModelMonad.State.t (S * seq T)%type.
refine (@MonadRun.Pack _ _ (@MonadRun.Class _ _ (Monad.class m)
  (@MonadRun.Mixin _ m
  (fun A m (s : S * seq T) => Some (m s)) (* run *) _ _))).
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

End ModelRun.

Module ModelStateTraceRun.

Definition mk {S T} :
  stateTraceRunMonad S T.
refine (let stm := @ModelStateTrace.mk S T in
        let run := @ModelRun.mk S T in
@MonadStateTraceRun.Pack S T (fun A => S * seq T -> A * (S * seq T))
  (@MonadStateTraceRun.Class S T (fun A => S * seq T -> A * (S * seq T))
    (MonadStateTrace.class stm)
    (MonadRun.mixin (MonadRun.class run))
    (@MonadStateTraceRun.Mixin _ _ run _ _ _ _ _ _))).
by [].
by [].
by [].
Defined.

End ModelStateTraceRun.


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

Lemma state_monad_stateT S :
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

Lemma error_monad_errorT (Z : UU0) :
  errorT Z ModelMonad.identity = ModelMonad.Except.t Z.
Proof.
rewrite /= /errorTmonadM /ModelMonad.Except.t.
have FG : MX_functor Z ModelMonad.identity = ModelMonad.Except.functor Z.
  apply: functor_ext => /=; apply fun_ext_dep => A; apply fun_ext_dep => B.
  rewrite boolp.funeqE => f; rewrite boolp.funeqE => m.
  by rewrite /MX_map /Actm /= /ModelMonad.Except.map; destruct m.
apply (@monad_of_ret_bind_ext _ _ _ _ _ _ FG) => /=.
  apply/natural_ext => A a /=; exact: (eq_rect_error_ret _ (esym FG)).
set x := @bindX _ _; exact: (@eq_rect_bind_error Z x (esym FG)).
Qed.

Lemma cont_monad_contT r :
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

Section state_errorT.
Let M S : monad := ModelState.state S.

Definition aLGet {Z S} : (StateOps.Get.func S).-aoperation (errorT Z (M S)) :=
  alifting (StateOps.get_aop S) (Lift (errorT Z) (M S)).

Definition aLPut {Z S} : (StateOps.Put.func S).-operation (errorT Z (M S)) :=
  alifting (StateOps.put_aop S) (Lift (errorT Z) (M S)).

Goal forall Z (S : UU0) X (k : S -> errorT Z (M S) X), aLGet _ k = StateOps.get_op _ k.
by [].
Abort.

Goal forall Z S, aLGet _ Ret = Lift (errorT Z) (M S) _ (@ModelState.get S).
by [].
Abort.

End state_errorT.

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
