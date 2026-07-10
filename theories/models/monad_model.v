(* monae: Monadic equational reasoning in Rocq                                *)
(* Copyright (C) 2025 monae authors, license: LGPL-2.1-or-later               *)
Require Import JMeq.
From Stdlib Require Import Recdef Wf_nat.
From mathcomp Require Import all_ssreflect ssralg ssrint.
From Stdlib Require Import Recdef Wf_nat.
From mathcomp Require Import all_ssreflect ssralg ssrint.
From mathcomp Require Import finmap.
From mathcomp Require boolp.
From mathcomp Require Import classical_sets.
From infotheo Require convex classical_sets_ext.
Require Import preamble.
From HB Require Import structures.
Require Import hierarchy monad_lib fail_lib state_lib trace_lib.
Require Import monad_transformer.

(**md**************************************************************************)
(* # Models for various monads                                                *)
(*                                                                            *)
(* Sample models for monads in hierarchy.v (see also other *_model.v files).  *)
(* As for naming, we tend to use the identifier acto for the actions on       *)
(* objects and actm for the actions on morphisms.                             *)
(*                                                                            *)
(* Instances of monads (Modules):                                             *)
(* ```                                                                        *)
(* IdentityMonad      == identity monad idfun                                 *)
(* ListMonad          == list monad seq                                       *)
(* SetMonad           == set monads using classical_sets                      *)
(* ExceptMonad        == exception monad E + A                                *)
(* option_monad       == alias for ExceptMonad.acto unit                      *)
(* WriterFunctor      == writer functor X * S                                 *)
(* OutputMonad        == output monad X * seq L                               *)
(* ReaderMonad        == reader/environment monad E -> A                      *)
(* StateMonad         == state monad S -> A * S                               *)
(* ContMonad          == continuation monad (A -> r) -> r                     *)
(* ```                                                                        *)
(*                                                                            *)
(* Sigma-operations (with algebraicity proofs):                               *)
(* ```                                                                        *)
(* empty_op                == empty operation                                 *)
(* append_op               == append operation                                *)
(* flush_op                == flush operation                                 *)
(* output_op               == output operation                                *)
(* ask_op                  == ask operation                                   *)
(* local_op                == local operation                                 *)
(* throw_op                == throw operation                                 *)
(* handle_op               == handle operation                                *)
(* get_op                  == get operation                                   *)
(* put_op                  == put operation                                   *)
(* abort_op                == abort operation                                 *)
(* acallcc_op              == algebraic callcc operation                      *)
(* ```                                                                        *)
(*                                                                            *)
(* Models of interfaces:                                                      *)
(* ```                                                                        *)
(* Module Fail             == failMonad for option_monad, ListMonad.acto, set *)
(* Module Except           == exceptMonad for ExcetMonad.acto unit            *)
(* Module State            == stateMonad for StateMonad.acto S                *)
(* Module Alt              == altMonad for ListMonad.acto, set                *)
(* Module AltCI            == altCIMonad for ListMonad.acto, set              *)
(* Module Nondet           == nondetMonad for ListMonad.acto, set             *)
(* Module ModelStateTrace  == stateTraceMonad for StateMonad.acto (S * seq T) *)
(* Module ModelCont        == contMonad for ContMonad.acto r                  *)
(* Module ModelShiftReset  == shiftResetMonad for ContMonad.acto r            *)
(* Module ModelReify       == reifyModel for StateMonad.acto (S * seq T)      *)
(* Module ModelStateTraceReify == stateTraceReify monad for                   *)
(*                                StateMonad.acto (S * seq T)                 *)
(* Module ModelBacktrackableState == from the ground up using fsets, i.e.,    *)
(*                                   redefinition of monads state-fail-alt-   *)
(*                                   nondet-failR0-preplusmonad-nondetstate   *)
(*                                   for S -> {fset (A * S)}                  *)
(* Module ModelArray       == array monad                                     *)
(* Module ModelPlusArray   == plus array monad                                *)
(* Module ModelMonadStateRun       == stateRunMonad for MS                    *)
(* Module ModelMonadExceptStateRun == exceptStateRunMonad                     *)
(* ```                                                                        *)
(*                                                                            *)
(* ```                                                                        *)
(* Module ModelTypedStoreRun == model for typed store (and crun)              *)
(* ```                                                                        *)
(*                                                                            *)
(* ```                                                                        *)
(* Module TrivialPlusArray == another, degenerate model of MonadPlusArray     *)
(* ```                                                                        *)
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

(* TODO: move *)
Section assoc.
Variables (I : eqType) (S : UU0).
Definition insert i s (a : I -> S) j := if i == j then s else a j.
Lemma insert_insert i s' s a :
  insert i s' (insert i s a) = insert i s' a.
Proof.
by apply boolp.funext => j; rewrite /insert; case: ifPn => // /negbTE ->.
Qed.
Lemma insert_same i a s : insert i s a i = s.
Proof. by rewrite /insert eqxx. Qed.
Lemma insert_same2 i a : insert i (a i) a = a.
Proof.
by apply boolp.funext => j; rewrite /insert; case: ifPn => // /eqP ->.
Qed.
Lemma insertC j i v u a : i != j ->
  insert j v (insert i u a) = insert i u (insert j v a).
Proof.
move=> h; apply boolp.funext => k; rewrite /insert; case: ifPn => // /eqP <-{k}.
by rewrite (negbTE h).
Qed.
Lemma insertC2 j i v a : insert j v (insert i v a) = insert i v (insert j v a).
Proof.
apply boolp.funext => k; rewrite /insert; case: ifPn => // /eqP <-{k}.
by rewrite if_same.
Qed.

End assoc.

Module IdentityMonad.
Section identitymonad.
Let bind := fun A B (a : A) (f : A -> B) => f a.
Let left_neutral : BindLaws.left_neutral bind (NId idfun).
Proof. by []. Qed.
Let right_neutral : BindLaws.right_neutral bind (NId idfun).
Proof. by []. Qed.
Let associative : BindLaws.associative bind. Proof. by []. Qed.
Let acto := ( @idfun UU0 ).
HB.instance Definition _ := isMonad_ret_bind.Build acto left_neutral right_neutral associative.
End identitymonad.
End IdentityMonad. 
HB.export IdentityMonad.

Module ListMonad.
Section listmonad.
Definition acto := fun A : UU0 => seq A.
Local Notation M := acto.
Let ret : idfun ~~> M := fun (A : UU0) x =>  (@cons A) x [::].
Let bind := fun A B (m : M A) (f : A -> M B) => flatten (map f m).
Let left_neutral : BindLaws.left_neutral bind ret.
Proof. by move=> A B m f; rewrite /bind /ret /= cats0. Qed.
Let right_neutral : BindLaws.right_neutral bind ret.
Proof. by move=> A m; rewrite /bind flatten_seq1. Qed.
Let associative : BindLaws.associative bind.
Proof.
move=> A B C; elim => // h t; rewrite /bind => ih f g.
by rewrite /= map_cat flatten_cat /= ih.
Qed.
HB.instance Definition _ :=
  isMonad_ret_bind.Build M left_neutral right_neutral associative.
End listmonad.
End ListMonad.
HB.export ListMonad.

Lemma list_bindE (A B : UU0) (M := ListMonad.acto) (m : M A) (f : A -> M B) :
  m >>= f = flatten (map f m).
Proof. by []. Qed.

Module SetMonad.
Section setmonad.
Local Open Scope classical_set_scope.
Definition acto := set.
Local Notation M := acto.
Let ret : idfun ~~> M := @set1.
Let bind := fun A B => @bigcup B A.
Let left_neutral : BindLaws.left_neutral bind ret.
Proof. move=> ? ? ? ?; exact: bigcup_set1. Qed.
Let right_neutral : BindLaws.right_neutral bind ret.
Proof.
by move=> ? ?; rewrite /bind bigcup_imset1 image_id.
Qed.
Let associative : BindLaws.associative bind.
Proof. move=> ? ? ? ? ? ?; exact: bigcup_bigcup. Qed.
HB.instance Definition _ :=
  isMonad_ret_bind.Build set left_neutral right_neutral associative.
End setmonad.
End SetMonad.
HB.export SetMonad.

Lemma set_bindE (A B : UU0) (M := [the monad of set]) (m : M A) (f : A -> M B) :
  m >>= f = bigcup m f.
Proof. by []. Qed.

Module ExceptMonad.
Section exceptmonad.
Variable E : UU0.
Definition acto := fun A : UU0 => (E + A)%type.
Local Notation M := acto.
Let ret : idfun ~~> M := @inr E.
Let bind := fun A B (m : M A) (f : A -> M B) =>
  match m with inl z => inl z | inr b => f b end.
Let left_neutral : BindLaws.left_neutral bind ret.
Proof. by []. Qed.
Let right_neutral : BindLaws.right_neutral bind ret.
Proof. by move=> ? []. Qed.
Let associative : BindLaws.associative bind.
Proof. by move=> ? ? ? []. Qed.
HB.instance Definition _ :=
  isMonad_ret_bind.Build M left_neutral right_neutral associative.
End exceptmonad.
End ExceptMonad.
HB.export ExceptMonad.

Lemma except_bindE (E A B : UU0) (M := ExceptMonad.acto E)
    (m : M A) (f : A -> M B) :
  m >>= f = match m with inl z => inl z | inr b => f b end.
Proof. by []. Qed.

Definition option_monad := ExceptMonad.acto unit.
HB.instance Definition _ := Monad.on option_monad.

Module WriterFunctor.
Section writer.
Variable S : UU0.

Definition acto := fun A : UU0 => (A * S)%type.
Let actm (X Y : UU0) : (X -> Y) -> acto X -> acto Y :=
  fun f : X -> Y => fun xs : X * S => match xs with (x, s) => (f x, s) end.

Let writer_id : FunctorLaws.id actm.
Proof. by move => B; apply: boolp.funext => -[]. Qed.

Let writer_o : FunctorLaws.comp actm.
Proof. by move=> X Y Z g h; apply: boolp.funext => -[]. Qed.

HB.instance Definition _:= isFunctor.Build acto writer_id writer_o.

End writer.
End WriterFunctor.
HB.export WriterFunctor.

Module OutputMonad.
Section output.
Variable L : UU0.
Definition acto := fun X : UU0 => (X * seq L)%type.
Local Notation M := acto.
Let ret : idfun ~~> M := fun A a => (a, [::]).
Let bind := fun (A B : UU0) (m : M A) (f : A -> M B) =>
  let: (x, w) := m in let: (x', w') := f x in (x', w ++ w').
Let left_neutral : BindLaws.left_neutral bind ret.
Proof. by move=> A B a f; rewrite /bind /=; case: f. Qed.
Let right_neutral : BindLaws.right_neutral bind ret.
Proof. by move=> A m; rewrite /bind /=; case: m => x w; rewrite cats0. Qed.
Let associative : BindLaws.associative bind.
Proof.
move=> A B C m f g; rewrite /bind; case: m => x w; case: f => x' w'.
by case: g => x'' w''; rewrite catA.
Qed.
HB.instance Definition _ :=
  isMonad_ret_bind.Build M left_neutral right_neutral associative.
End output.
End OutputMonad.
HB.export OutputMonad.

Lemma output_bindE (L A B : UU0) (M := OutputMonad.acto L)
   (m : M A) (f : A -> M B) :
  m >>= f = let: (x, w) := m in let: (x', w') := f x in (x', w ++ w').
Proof. by []. Qed.

Module ReaderMonad.
Section reader.
Variable E : UU0.
Definition acto := fun A : UU0 => E -> A.
Local Notation M := acto.
Definition ret : idfun ~~> M := fun A x => fun e => x.
(* computation that ignores the environment *)
Let bind := fun (A B : UU0) (m : M A) (f : A -> M B) => fun e => f (m e) e.
(* binds m f applied the same environment to m and to the result of f *)
Let left_neutral : BindLaws.left_neutral bind ret.
Proof. by []. Qed.
Let right_neutral : BindLaws.right_neutral bind ret.
Proof. by []. Qed.
Let associative : BindLaws.associative bind.
Proof. by []. Qed.
HB.instance Definition _ :=
  isMonad_ret_bind.Build M left_neutral right_neutral associative.
End reader.
End ReaderMonad.
HB.export ReaderMonad.

Lemma reader_bindE (E A B : UU0) (M := ReaderMonad.acto E)
    (m : M A) (f : A -> M B) :
  m >>= f = fun e => f (m e) e.
Proof. by []. Qed.

Module StateMonad.
Section state.
Variable S : UU0. (* type of states *)
Definition acto := fun A : UU0 => S -> A * S.
Local Notation M := acto.
Let ret : idfun ~~> M := fun A a => fun s => (a, s).
Let bind := fun (A B : UU0) (m : M A) (f : A -> M B) => uncurry f \o m.
Let left_neutral : BindLaws.left_neutral bind ret.
Proof. by move=> A B a f; apply boolp.funext. Qed.
Let right_neutral : BindLaws.right_neutral bind ret.
Proof.
by move=> A f; apply boolp.funext => s; rewrite /bind compE/=; case: (f s).
Qed.
Let associative : BindLaws.associative bind.
Proof.
move=> A B C a b c; rewrite /bind compA; congr (_ \o _).
by apply boolp.funext => -[].
Qed.
HB.instance Definition _ :=
  isMonad_ret_bind.Build M left_neutral right_neutral associative.
End state.
End StateMonad.
HB.export StateMonad.

Lemma state_bindE (S A B : UU0) (M := StateMonad.acto S)
  (m : M A) (f : A -> M B) : m >>= f = uncurry f \o m.
Proof. by []. Qed.

(* see Sect. 3 of of [Wadler, 94] for the model of the ret and the bind of the
continuation monad *)
Module ContMonad.
Section cont.
Variable r : UU0. (* the type of answers *)
Definition acto := fun A : UU0 => (A -> r) -> r.
Local Notation M := acto.
Let ret : idfun ~~> M := fun A a => fun k => k a.
Let bind := fun (A B : UU0) (m : M A) (f : A -> M B) => fun k => m (fun a => f a k).
Let left_neutral : BindLaws.left_neutral bind ret.
Proof. by move=> A B a f; apply boolp.funext => Br. Qed.
Let right_neutral : BindLaws.right_neutral bind ret.
Proof. by []. Qed.
Let associative : BindLaws.associative bind.
Proof. by []. Qed.
HB.instance Definition _ :=
  isMonad_ret_bind.Build M left_neutral right_neutral associative.
End cont.
End ContMonad.
HB.export ContMonad.

Lemma cont_bindE (r A B : UU0) (M := ContMonad.acto r) (m : M A) (f : A -> M B) :
  m >>= f = fun k => m (fun a => f a k).
Proof. by []. Qed.

Module Empty.
Section empty.
Definition acto (X : UU0) : UU0 := unit.
Let actm (X Y : UU0) (f : X -> Y) (t : acto X) : acto Y := tt.
Let func_id : FunctorLaws.id actm.
Proof. by move=> A; apply boolp.funext => -[]. Qed.
Let func_comp : FunctorLaws.comp actm.
Proof. by move=> A B C f g; apply boolp.funext => -[]. Qed.
HB.instance Definition _ := isFunctor.Build acto func_id func_comp.
End empty.
End Empty.
HB.export monae.theories.models.monad_model.Empty.

Section appendop.
Local Notation M := [the monad of ListMonad.acto].

Definition empty : Empty.acto \o M ~~> M := fun A _ => @nil A.

Let naturality_empty : naturality (Empty.acto \o M) M empty.
Proof. by move=> A B h; exact: boolp.funext. Qed.

HB.instance Definition _ :=
  isNatural.Build (Empty.acto \o M) M empty naturality_empty.

Definition empty_op : Empty.acto.-operation M := [the _ ~> _ of empty].

Lemma algebraic_empty : algebraicity empty_op.
Proof. by []. Qed.

Definition append : squaring \o M ~~> M :=
  fun A x => let: (s1, s2) := x in (s1 ++ s2).

Let naturality_append : naturality (squaring \o M) M append.
Proof.
move=> A B h; apply boolp.funext => -[s1 s2] /=.
rewrite [LHS]fmapE [LHS]list_bindE.
rewrite [in LHS]map_cat.
by rewrite [in LHS]flatten_cat.
Qed.

HB.instance Definition _ :=
  isNatural.Build (squaring \o M) M append naturality_append.

Definition append_op : squaring.-operation M := [the _ ~> _ of append].

Lemma algebraic_append : algebraicity append_op.
Proof.
move=> A B f [t1 t2] /=.
by rewrite 3!list_bindE -flatten_cat -map_cat.
Qed.

End appendop.

Module Output.
Section output.
Variable L : UU0.
Definition acto (X : UU0) := (seq L * X)%type.
Let actm (X Y : UU0) (f : X -> Y) (t : acto X) : acto Y :=
  let: (w, x) := t in (w, f x).
Let func_id : FunctorLaws.id actm.
Proof. by move=> A; apply boolp.funext; case. Qed.
Let func_comp : FunctorLaws.comp actm.
Proof. by move=> A B C f g; apply boolp.funext; case. Qed.
HB.instance Definition _ := isFunctor.Build acto func_id func_comp.
End output.
End Output.
HB.export Output.

Module Flush.
Section flush.
Definition acto (X : UU0) := X.
Let actm (X Y : UU0) (f : X -> Y) (t : acto X) : acto Y := f t.
Let func_id : FunctorLaws.id actm. Proof. by []. Qed.
Let func_comp : FunctorLaws.comp actm. Proof. by []. Qed.
HB.instance Definition _ := isFunctor.Build acto func_id func_comp.
End flush.
End Flush.
HB.export Flush.

Section outputops.
Variable L : UU0.
Local Notation M := (OutputMonad.acto L).

Definition output : Output.acto L \o M ~~> M :=
  fun A m => let: (x, w') := m.2 in (x, m.1 ++ w'). (*NB: w'++m.1 in the esop paper*)

Let naturality_output :
  naturality (Output.acto L \o M) M output.
Proof.
move=> A B h.
apply boolp.funext => -[w [x w']].
by rewrite /output !compE/= catA.
Qed.

HB.instance Definition _ := isNatural.Build
  (Output.acto L \o M) M output naturality_output.

Definition output_op : (Output.acto L).-operation M := [the _ ~> _ of output].

Lemma algebraic_output : algebraicity output_op.
Proof.
move=> A B f [w [x w']].
rewrite output_bindE/=.
rewrite /output /=.
rewrite output_bindE.
by case: f => x' w''; rewrite catA.
Qed.

Definition flush : (Flush.acto \o M) ~~> M :=
  fun A m => let: (x, _) := m in (x, [::]).

(* performing a computation in a modified environment *)
Let naturality_flush : naturality (Flush.acto \o M) M flush.
Proof. by move=> A B h; apply: boolp.funext => -[]. Qed.

HB.instance Definition _ := isNatural.Build
  (Flush.acto \o M) M flush naturality_flush.

(* NB: flush is not algebraic *)
Definition flush_op : Flush.acto.-operation M :=
  [the _ ~> _ of flush].

Lemma algebraic_flush : algebraicity flush_op.
Proof.
move=> A B f [x w].
rewrite output_bindE.
rewrite /flush_op /=.
rewrite /flush /=.
rewrite /actm /=.
rewrite output_bindE.
case: f => x' w'.
Abort.

End outputops.

(* wip *)
Module Output'.
Section output.
Variable L : UU0.
Local Notation M := (OutputMonad.acto L).
(* usual output operation *)
Definition output : seq L -> M unit := fun w => output_op _ _ (w, Ret tt).
Lemma outputE : output = fun w => (tt, w).
Proof.
apply boolp.funext => w.
by rewrite /output /= /monad_model.output /= cats0.
Qed.
(* TODO: complete with an interface for the output monad and instantiate *)
End output.
End Output'.

Module Ask.
Section ask.
Variable E : UU0.
Definition acto (X : UU0) := E -> X.
Let actm (X Y : UU0) (f : X -> Y) (t : acto X) : acto Y := f \o t.
Let func_id : FunctorLaws.id actm. Proof. by []. Qed.
Let func_comp : FunctorLaws.comp actm. Proof. by []. Qed.
HB.instance Definition _ := isFunctor.Build acto func_id func_comp.
End ask.
End Ask.
HB.export Ask.

Module Local.
Section local.
Variable E : UU0.
Definition acto (X : UU0) := ((E -> E) * X)%type.
Let actm (X Y : UU0) (f : X -> Y) (t : acto X) : acto Y :=
  let: (e, x) := t in (e, f x).
Let func_id : FunctorLaws.id actm.
Proof. by move=> A; apply boolp.funext => -[]. Qed.
Let func_comp : FunctorLaws.comp actm.
Proof. by move=> A B C g h; apply boolp.funext => -[]. Qed.
HB.instance Definition _ := isFunctor.Build acto func_id func_comp.
End local.
End Local.
HB.export Local.

Section environmentops.
Variable E : UU0.
Local Notation M := (ReaderMonad.acto E).

Definition ask : (Ask.acto E \o M)(*E -> M A?*) ~~> M :=
  fun A f s => f s s. (* reading the environment *)

Let naturality_ask : naturality (Ask.acto E \o M) M ask.
Proof. by []. Qed.

HB.instance Definition _ := isNatural.Build
  (Ask.acto E \o M) M ask naturality_ask.

Definition ask_op : (Ask.acto E).-operation M :=
  [the _ ~> _ of ask].

Lemma algebraic_ask : algebraicity ask_op.
Proof. by []. Qed.

Definition local : (Local.acto E \o M)(*(E -> E) * M A*) ~~> M :=
  fun A x s => let: (e, t) := x in t (e s).
(* performing a computation in a modified environment *)

Let naturality_local : naturality (Local.acto E \o M) M local.
Proof. by move=> A B h; apply boolp.funext => -[]. Qed.

HB.instance Definition _ := isNatural.Build
  (Local.acto E \o M) M local naturality_local.

Definition local_op : (Local.acto E).-operation M :=
  [the _ ~> _ of local].

(* NB: local is not algebraic *)
Lemma algebraic_local : algebraicity local_op.
Proof.
move=> A B f t.
rewrite reader_bindE.
rewrite /local_op /=.
rewrite /local /=.
rewrite /actm /=.
case: t => /= ee m.
rewrite reader_bindE.
apply boolp.funext=> x /=.
Abort.

End environmentops.

(* wip *)
Module Environment.
Section environment.
Variable E : UU0.
Local Notation M := (ReaderMonad.acto E).
(* usual get operation *)
Definition ask : M E := ask_op _ _ Ret.
Lemma askE : ask = fun e => e. Proof. by []. Qed.
(* TODO: complete with an interface for the environment monad and instantiate, see Jaskelioff's PhD *)
End environment.
End Environment.

Module Throw.
Section throw.
Variable Z : UU0.
Definition acto (X : UU0) := Z.
Let actm (X Y : UU0) (f : X -> Y) (t : acto X) : acto Y := t.
Let func_id : FunctorLaws.id actm. Proof. by []. Qed.
Let func_comp : FunctorLaws.comp actm. Proof. by []. Qed.
HB.instance Definition _ := isFunctor.Build acto func_id func_comp.
End throw.
End Throw.
HB.export Throw.

Module Handle.
Section handle.
Variable Z : UU0.
Definition acto (X : UU0) := (X * (Z -> X))%type.
Let actm (X Y : UU0) (f : X -> Y) (t : acto X) : acto Y :=
  let: (x, h) := t in (f x, fun z => f (h z)).
Let func_id : FunctorLaws.id actm.
Proof. by move=> A; apply boolp.funext => -[]. Qed.
Let func_comp : FunctorLaws.comp actm.
Proof. by move=> A B C g h; apply boolp.funext => -[]. Qed.
HB.instance Definition _ := isFunctor.Build acto func_id func_comp.
End handle.
End Handle.
HB.export Handle.

Section exceptops.
Variable Z : UU0.
Local Notation M := (ExceptMonad.acto Z).

Definition throw : (Throw.acto Z \o M) ~~> M :=
  fun (A : UU0) z => inl z.

Let naturality_throw : naturality (Throw.acto Z \o M) M throw.
Proof. by []. Qed.

HB.instance Definition _ := isNatural.Build
  (Throw.acto Z \o M) M throw naturality_throw.

Definition throw_op : (Throw.acto Z).-operation M :=
  [the _ ~> _ of throw].

Lemma algebraic_throw : algebraicity throw_op.
Proof. by []. Qed.

HB.instance Definition _ := isAOperation.Build _ M throw algebraic_throw.

Definition throw_aop : (Throw.acto Z).-aoperation M :=
  [the aoperation _ _ of throw].

Definition handle' A (m : M A) (h : Z -> M A) : M A :=
  match m with inl z => h z | inr x => inr x end.

Definition handle : Handle.acto Z \o M ~~> M :=
  fun A => uncurry (@handle' A).

Let naturality_handle : naturality (Handle.acto Z \o M) M handle.

Proof. by move=> A B h; apply boolp.funext => -[[]]. Qed.

HB.instance Definition _ := isNatural.Build
  (Handle.acto Z \o M) M handle naturality_handle.

Definition handle_op : (Handle.acto Z).-operation M :=
  [the _ ~> _ of handle].

(* NB: handle is not algebraic *)
Lemma algebraic_handle : algebraicity handle_op.
Proof.
move=> A B f t.
rewrite except_bindE.
rewrite /handle_op /=.
rewrite /handle /=.
rewrite /uncurry /=.
case: t => -[z//|a] g /=.
rewrite except_bindE.
case: (f a) => // z.
rewrite /handle'.
rewrite except_bindE.
case: (g z) => [z0|a0].
Abort.

End exceptops.

Arguments throw_op {Z}.
Arguments handle_op {Z}.

(* NB: see also Module Ask *)
Module StateOpsGet.
Section get.
Variable S : UU0.
Definition acto (X : UU0) := S -> X.
Let actm (X Y : UU0) (f : X -> Y) (t : acto X) : acto Y := f \o t.
Let func_id : FunctorLaws.id actm.
Proof. by move=> A; apply boolp.funext. Qed.
Let func_comp : FunctorLaws.comp actm.
Proof. by move=> A B C g h; apply boolp.funext. Qed.
HB.instance Definition _ := isFunctor.Build acto func_id func_comp.
End get.
End StateOpsGet.
HB.export StateOpsGet.

Module StateOpsPut.
Section put.
Variable S : UU0.
Definition acto (X : UU0) := (S * X)%type.
Let actm (X Y : UU0) (f : X -> Y) (sx : acto X) : acto Y := (sx.1, f sx.2).
Let func_id : FunctorLaws.id actm.
Proof. by move=> A; apply boolp.funext => -[]. Qed.
Let func_comp : FunctorLaws.comp actm.
Proof. by move=> A B C g h; apply boolp.funext. Qed.
HB.instance Definition _ := isFunctor.Build acto func_id func_comp.
End put.
End StateOpsPut.
HB.export StateOpsPut.

Section stateops.
Variable S : UU0.
Local Notation M := (StateMonad.acto S).

Let get : StateOpsGet.acto S \o M ~~> M := fun A k s => k s s.

Let naturality_get : naturality (StateOpsGet.acto S \o M) M get.
Proof.
move=> A B h; apply boolp.funext => /= m; apply boolp.funext => s.
by rewrite FCompE.
Qed.

HB.instance Definition _ := isNatural.Build _ M get naturality_get.

Definition get_op : (StateOpsGet.acto S).-operation M :=
  [the _ ~> _ of get].

Lemma algebraic_get : algebraicity get_op.
Proof. by []. Qed.

HB.instance Definition _ := isAOperation.Build
  (StateOpsGet.acto S) M get algebraic_get.

Definition get_aop : (StateOpsGet.acto S).-aoperation M :=
  [the aoperation _ _ of get].

Let put' A (s : S) (m : M A) : M A := fun _ => m s.

Let put : StateOpsPut.acto S \o M ~~> M :=
  fun A => uncurry (put' (A := A)).

Let naturality_put : naturality (StateOpsPut.acto S \o M) M put.
Proof.
by move=> A B h; apply boolp.funext => /= -[s m /=]; apply boolp.funext.
Qed.

HB.instance Definition _ :=
  isNatural.Build _ M put naturality_put.

Definition put_op : (StateOpsPut.acto S).-operation M :=
  [the _ ~> _ of put].

Lemma algebraic_put : algebraicity put_op.
Proof. by move=> ? ? ? []. Qed.

HB.instance Definition _ := isAOperation.Build
  (StateOpsPut.acto S) M put algebraic_put.

Definition put_aop : (StateOpsPut.acto S).-aoperation M :=
  [the aoperation _ _ of put].

End stateops.

Arguments get_op {S}.
Arguments put_op {S}.

Module ContOpsAbort.
Section abort.
Variable r : UU0.
Definition acto (X : UU0) := r.
Let actm (A B : UU0) (f : A -> B) (x : acto A) : acto B := x.
Let func_id : FunctorLaws.id actm. Proof. by []. Qed.
Let func_comp : FunctorLaws.comp actm. Proof. by []. Qed.
HB.instance Definition _ := isFunctor.Build acto func_id func_comp.
End abort.
End ContOpsAbort.
HB.export ContOpsAbort.

Module ContOpsAcallcc.
Section acallcc.
Variable r : UU0.
Definition acto := fun A : UU0 => (A -> r) -> A.
Let actm (X Y : UU0) (f : X -> Y) (t : acto X) : acto Y :=
  fun (g : Y -> r) => f (t (fun x => g (f x))).
Let func_id : FunctorLaws.id actm. Proof. by []. Qed.
Let func_comp : FunctorLaws.comp actm. Proof. by []. Qed.
HB.instance Definition _ := isFunctor.Build acto func_id func_comp.
End acallcc.
End ContOpsAcallcc.
HB.export ContOpsAcallcc.

Section contops.
Variable r : UU0.
Local Notation M := (ContMonad.acto r).

Definition abort : ContOpsAbort.acto r \o M ~~> M :=
  fun (A : UU0) r _ => r.

Lemma naturality_abort : naturality (ContOpsAbort.acto r \o M) M abort.
Proof. by []. Qed.

HB.instance Definition _ := isNatural.Build _ M abort naturality_abort.

Definition abort_op : (ContOpsAbort.acto r).-operation M :=
  [the _ ~> _ of abort].

Let algebraicity_abort : algebraicity abort_op.
Proof. by []. Qed.

HB.instance Definition _ := isAOperation.Build (ContOpsAbort.acto r) M
  abort algebraicity_abort.

Definition abort_aop : (ContOpsAbort.acto r).-aoperation M :=
  [the aoperation _ _ of abort].

(* alebgraic call/cc *)
Definition acallcc : (ContOpsAcallcc.acto r \o M)(*(f : (M A -> r) -> M A)*) ~~> M :=
  fun A f k => f (fun m => m k) k.

Let naturality_acallcc : naturality (ContOpsAcallcc.acto r \o M) M acallcc.
Proof. by []. Qed.

HB.instance Definition _ :=
  isNatural.Build _ M acallcc naturality_acallcc.

Definition acallcc_op : (ContOpsAcallcc.acto r).-operation M :=
  [the _ ~> _ of acallcc].

Let algebraicity_callcc : algebraicity acallcc_op.
Proof. by []. Qed.

HB.instance Definition _ := isAOperation.Build (ContOpsAcallcc.acto r) M
  acallcc algebraicity_callcc.

Definition callcc_aop : (ContOpsAcallcc.acto r).-aoperation M :=
  [the aoperation _ _ of acallcc].

End contops.

Module Fail.
Section fail.
Definition option_fail : forall A, option_monad A := fun A => @throw unit A tt.
Let option_bindfailf : BindLaws.left_zero (@bind _) option_fail.
Proof. by []. Qed.
HB.instance Definition _ := Monad.on option_monad.
HB.instance Definition _ := @isMonadFail.Build option_monad
  option_fail option_bindfailf.

Definition list_fail : forall A, ListMonad.acto A := fun A => @empty _ tt.
Let list_bindfailf : BindLaws.left_zero (@bind _) list_fail.
Proof. by []. Qed.
HB.instance Definition _ := @isMonadFail.Build ListMonad.acto list_fail list_bindfailf.

Definition set_fail : forall A, set A := @set0.
Let set_bindfailf : BindLaws.left_zero (@bind _) set_fail.
Proof.
move=> A B f /=; apply boolp.funext => b; rewrite boolp.propeqE.
by split=> // -[a []].
Qed.
HB.instance Definition _ := isMonadFail.Build set set_bindfailf.
End fail.
End Fail.
HB.export Fail.

Module Except.
Section except.
Let M : failMonad := option_monad.
Definition handle : forall A, M A -> M A -> M A :=
  fun A m1 m2 => @handle_op unit _ (m1, (fun _ => m2)).
Lemma handleE : handle = (fun A m m' => if m is inr x then m else m').
Proof. by apply funext_dep => A; apply boolp.funext => -[]. Qed.
Let catchmfail : forall A, right_id fail (@handle A).
Proof. by move=> A; case => //; case. Qed.
Let catchfailm : forall A, left_id fail (@handle A).
Proof. by move=> A; case. Qed.
Let catchA : forall A, ssrfun.associative (@handle A).
Proof. by move=> A; case. Qed.
Let catchret : forall A x, @left_zero (M A) (M A) (Ret x) (@handle A).
Proof. by move=> A x; case. Qed.
HB.instance Definition _ := isMonadExcept.Build option_monad
  catchmfail catchfailm catchA catchret.
End except.
End Except.
HB.export Except.

Module State.
Section state.
Variable S : UU0.
Local Notation M := (StateMonad.acto S).
Let get : M S := get_op _ Ret.
Lemma getE : get = fun s => (s, s). Proof. by []. Qed.
Let put : S -> M unit := fun s => put_op _ (s, Ret tt).
Lemma putE : put = fun s' _ => (tt, s').
Proof. by []. Qed.
Let putput : forall s s', put s >> put s' = put s'.
Proof. by []. Qed.
Let putget : forall s, put s >> get = put s >> Ret s.
Proof. by []. Qed.
Let getput : get >>= put = skip.
Proof. by []. Qed.
Let getget : forall (A : UU0) (k : S -> S -> M A), get >>= (fun s => get >>= k s) = get >>= fun s => k s s.
Proof. by []. Qed.
HB.instance Definition _ := isMonadState.Build S (StateMonad.acto S)
  putput putget getput getget.
End state.
End State.
HB.export State.

Module Alt.

Section list.
Let M := ListMonad.acto.
Definition list_alt : forall T, M T -> M T -> M T := fun A => curry (@append A).
Let altA (T : UU0) : ssrfun.associative (@list_alt T).
Proof. by move=> a b c; rewrite /list_alt /= /curry /= catA. Qed.
Let alt_bindDl : BindLaws.left_distributive (@bind [the monad of ListMonad.acto]) list_alt.
Proof.
move=> A B /= s1 s2 k.
by rewrite list_bindE map_cat flatten_cat.
Qed.
HB.instance Definition _ := isMonadAlt.Build ListMonad.acto altA alt_bindDl.
End list.

(* NB: was at the top of the file *)
Lemma setUDl : @BindLaws.left_distributive _ (fun I A => @bigcup A I) (@setU).
Proof.
move=> A B /= p q r; apply boolp.funext => b; rewrite boolp.propeqE; split.
move=> -[a [?|?] ?]; by [left; exists a | right; exists a].
by rewrite /setU => -[[a ? ?]|[a ? ?]]; exists a => //; [left|right].
Qed.

Section set.
Let M := [the monad of set].
Let altA : forall T : UU0, ssrfun.associative (@setU T).
Proof. by move=> ?; exact: setUA. Qed.
Let alt_bindDl : BindLaws.left_distributive (@bind [the monad of set]) (@setU).
Proof.
rewrite /BindLaws.left_distributive /= => A B m1 m2 k.
by rewrite set_bindE setUDl.
Qed.
HB.instance Definition _ := isMonadAlt.Build set altA alt_bindDl.
End set.

End Alt.
HB.export Alt.

Module AltCI.

Section set.
Let M := [the altMonad of set].
Let altmm (A : UU0) : idempotent_op (@alt M A).
Proof. by move=> ?; exact: setUid. Qed.
Let altC (A : UU0) : commutative (@alt M A).
Proof. by move=> ?; exact: setUC. Qed.
HB.instance Definition _ := @isMonadAltCI.Build set altmm altC.
End set.

End AltCI.
HB.export AltCI.

Module Nondet.

Section list.
Let M : failMonad := [the failMonad of ListMonad.acto].
Let N : altMonad := [the altMonad of ListMonad.acto].
Let altfailm : @BindLaws.left_id _ (@fail M) (@alt N).
Proof. by []. Qed.
Let altmfail : @BindLaws.right_id _ (@fail M) (@alt N).
Proof.
move=> A l /=.
by rewrite /alt /= /list_alt /= /curry /= /fail /= /list_fail /= cats0.
Qed.
HB.instance Definition _ := isMonadNondet.Build ListMonad.acto altfailm altmfail.
End list.

Section set.
Local Notation M := [the failMonad of set].
Local Notation N := [the altMonad of set].
Let altfailm : @BindLaws.left_id _ (@fail M) (@alt N).
Proof.
move=> T m.
by rewrite /fail /= /set_fail /alt /= set0U.
Qed.
Let altmfail : @BindLaws.right_id _ (@fail M) (@alt N).
Proof.
move=> A l /=.
by rewrite /fail /= /alt /= /set_fail setU0.
Qed.
HB.instance Definition _ := isMonadNondet.Build set altfailm altmfail.
End set.

End Nondet.
HB.export Nondet.

Module PrePlus.

Section failr0.
Let M : failMonad := [the failMonad of set].
Let bindmfail : BindLaws.right_zero (@bind [the monad of set]) (@fail _).
Proof. by move=> T1 T2 A; rewrite /bind/= bigcup0. Qed.
HB.instance Definition _ := isMonadFailR0.Build set bindmfail.
End failr0.

Section set.
Let M : nondetMonad := [the nondetMonad of set].
Let alt_bindDr : BindLaws.right_distributive (@bind [the monad of set]) (@alt [the altMonad of set]).
Proof. by move=> T1 T2 A k1 k2; rewrite /bind/= bigcupU. Qed.
HB.instance Definition _ := isMonadPrePlus.Build set alt_bindDr.
End set.
End PrePlus.
HB.export PrePlus.

Module ModelStateTrace.

Section st.
Variables (S T : UU0).
Let M := [the monad of StateMonad.acto (S * seq T)%type].
Let st_get : M S := fun s => (s.1, s).
Let st_put : S -> M unit := (fun s' s => (tt, (s', s.2))).
Let st_mark : T -> M unit := (fun t s => (tt, (s.1, rcons s.2 t))).
Let st_putput : forall s s', st_put s >> st_put s' = st_put s'.
Proof. by []. Qed.
Let st_putget : forall s, st_put s >> st_get = st_put s >> Ret s.
Proof. by []. Qed.
Let st_getput : st_get >>= st_put = skip.
Proof. by move=> *; apply boolp.funext => -[]. Qed.
Let st_getget : forall (A : UU0) (k : S -> S -> M A),
      st_get >>= (fun s => st_get >>= k s) = st_get >>= fun s => k s s.
Proof. by []. Qed.
Let st_putmark : forall s e, st_put s >> st_mark e = st_mark e >> st_put s.
Proof. by []. Qed.
Let st_getmark : forall e (k : _ -> M S), st_get >>= (fun v => st_mark e >> k v) =
                         st_mark e >> st_get >>= k.
Proof. by []. Qed.
HB.instance Definition _ := @isMonadStateTrace.Build S T (StateMonad.acto (S * seq T)%type)
  st_get st_put st_mark st_putput st_putget st_getput st_getget st_putmark st_getmark.
End st.
End ModelStateTrace.
HB.export ModelStateTrace.

(* see Sect 3.1 of [Wadler, 94] for the model of callcc *)
Definition usual_callcc r (M := fun C => (C -> r) -> r) A B (f : (A -> M B) -> M A) : M A :=
  fun k : A -> r => f (fun a _ => k a) k.

Module ModelCont.
Section modelcont.
Variable r : UU0.
Local Notation M := [the monad of (ContMonad.acto r)].
Let callcc (A B : UU0) (f : (A -> M B) -> M A) : M A :=
  acallcc_op _ _ (fun k => f (fun x _ => k (Ret x))).
Lemma callccE (A B : UU0) (f : (A -> M B) -> M A) : callcc f = usual_callcc f.
Proof. by []. Qed.
Let callcc0 : forall (A B : UU0) (g : (A -> M B) -> M A) (k : B -> M B),
     @callcc _ _ (fun f => g (fun x => f x >>= k)) = @callcc _ _ g.
Proof. by []. Qed.
Let callcc1 : forall (A B : UU0) (m : M B), @callcc _ _ (fun _ : B -> M A => m) = m.
Proof. by []. Qed.
Let callcc2 : forall (A B C : UU0) (m : M A) x (k : A -> B -> M C),
     @callcc _ _ (fun f : _ -> M _ => m >>= (fun a => f x >>= (fun b => k a b))) =
     @callcc _ _ (fun f : _ -> M _ => m >> f x).
Proof. by []. Qed.
Let callcc3 : forall (A B : UU0) (m : M A) b,
     @callcc _ _ (fun f : B -> M B => m >> f b) =
     @callcc _ _ (fun _ : B -> M B => m >> Ret b).
Proof. by []. Qed.
HB.instance Definition _ := isMonadContinuation.Build (ContMonad.acto r)
  callcc0 callcc1 callcc2 callcc3.
End modelcont.
End ModelCont.
HB.export ModelCont.

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
Let M : contMonad := [the contMonad of ContMonad.acto nat].
Definition sum_break (xs : seq (option nat)) : M nat :=
  callcc (fun break : nat -> M nat => foldM (oaddn_break break) 0 xs).

Compute (sum_break [:: Some 2; Some 6; None; Some 4]).

(* example from Sect. 3.1 of [Wadler, 94] *)
Goal Ret 1 +m (callcc (fun f => Ret 10 +m (f 100))) = Ret (1 + 100) :> M _.
Proof. by rewrite /addM bindretf; apply boolp.funext. Abort.

(* https://xavierleroy.org/mpri/2-4/transformations.pdf *)

Fixpoint list_iter (M : monad) A (f : A -> M unit) (s : seq A) : M unit :=
  if s is h :: t then f h >> list_iter f t else Ret tt.

Compute (@list_iter [the monad of idfun] nat (fun a => Ret tt) [:: O; 1; 2]).

Definition list_find (M : contMonad) (A : UU0) (p : pred A) (s : seq A) : M _ :=
  callcc (fun k => list_iter (fun x => if p x then (*Throw*) k (Some x) else Ret tt) s >> Ret None).

(* returns None if no such element exists *)

Compute (@list_find [the contMonad of ContMonad.acto bool] nat [pred x | odd x] [:: 2; 4; 6]).

(* returns the first element such that *)

Compute (@list_find [the contMonad of (ContMonad.acto bool)] nat [pred x | odd x] [:: 2; 4; 3; 6]).

End continuation_examples.

(* see Sect. 3.2 of [Wadler, 94] for the model of shift and reset *)
Module ModelShiftReset.
Section modelshiftreset.
Variable r : UU0.
Let M := [the contMonad of ContMonad.acto r].
Definition shift :
    forall A : UU0, ((A -> M r) -> M r) -> M A :=
 fun A h => fun c => h (fun v c' => c' (c v)) ssrfun.id.

Definition reset : M r -> M r :=
  fun m  => fun c => c (m ssrfun.id).

Let shiftreset0 : forall (A : UU0) (m : M A), @shift _ (fun k => m >>= k) = m.
Proof. by []. Qed.
Let shiftreset1 : forall (A B : UU0) (h : (A -> M B) -> M A),
    callcc h = @shift _ (fun k' => h (fun x => @shift _ (fun k'' => k' x)) >>= k').
Proof. by []. Qed.
Let shiftreset2 : forall (A : UU0) (c : A) (c': r) (k : A -> r -> _),
    (reset (do x <- Ret c; do y <- @shift _ (fun _ => Ret c'); k x y) = Ret c >> Ret c')%Do.
Proof. by []. Qed.
Let shiftreset3 : forall (c c' : r) (k : r -> r -> _),
    (reset (do x <- Ret c; do y <- @shift _ (fun f => do v <- f c'; f v); Ret (k x y)) =
     reset (do x <- Ret c; do y <- @shift _ (fun f => f c'); Ret (k x (k x y))))%Do.
Proof. by []. Qed.
Let shiftreset4 : forall (c : r) k,
    (reset (do y <- @shift _ (@^~ c); Ret (k y)) = Ret (k c))%Do.
Proof. by []. Qed.

HB.instance Definition _ := isMonadShiftReset.Build r (ContMonad.acto r)
  shiftreset0 shiftreset1 shiftreset2 shiftreset3 shiftreset4.
End modelshiftreset.
End ModelShiftReset.
HB.export ModelShiftReset.

Section shiftreset_examples.
(* see Sect. 3.2 of [Wadler, 94] *)
Let M : shiftresetMonad nat := [the shiftresetMonad nat of ContMonad.acto nat].
Goal Ret 1 +m (reset (Ret 10 +m (shift (fun f : _ -> M nat => f (100) >>= f) : M _)) : M _) =
     Ret (1 + (10 + (10 + 100))).
Proof. by rewrite /addM bindretf; apply boolp.funext. Abort.
Goal Ret 1 +m (reset (Ret 10 +m (shift (fun f : _ -> M nat => Ret 100 : M _) : M _)) : M _) =
     Ret (1 + 100).
Proof. by rewrite /addM bindretf; apply boolp.funext. Abort.
Goal Ret 1 +m (reset (Ret 10 +m (shift (fun f : _ -> M nat => f 100 +m f 1000) : M _)) : M _) =
     Ret (1 + ((10 + 100) + (10 + 1000))).
Proof. by rewrite /addM bindretf; apply boolp.funext. Abort.

Let N : shiftresetMonad (seq nat) := [the shiftresetMonad (seq nat) of ContMonad.acto (seq nat)].
Fixpoint perverse (l : seq nat) : N (seq nat) :=
  if l is h :: t then
    shift (fun f : _ -> N _ => Ret h >>=
      (fun x => perverse t >>= f >>= (fun y => Ret (x :: y))))
  else Ret [::].
Goal reset (perverse [:: 1; 2; 3]) = Ret [:: 3; 2; 1].
by [].
Abort.

Definition stranger :=
  let g b := reset ((shift (fun f : _ -> _ _ _ => f b) >>=
                           (fun x => if x then Ret 2 else Ret 3))) in
  g true +m g false.
Goal stranger = Ret 5. by []. Abort.

Goal reset (Ret 2 +m shift (fun k : _ -> M _ => k 3 +m Ret 1 : M _) : M _) = Ret 6 :> M _.
Proof. by rewrite /addM bindretf; apply boolp.funext. Abort.
Goal reset (Ret 2 *m shift (fun k : _ -> M _ => k 4 +m Ret 1 : M _)
                  *m shift (fun k : _ -> M _ => k 3 +m Ret 1 : M _) : M _ ) = Ret 26 :> M _.
Proof. by rewrite /mulM bindretf; apply boolp.funext. Abort.

End shiftreset_examples.

Module ModelStateForLoop.
Section modelstateforloop.
Variable S : UU0.
Local Notation M := (StateMonad.acto S).
Definition forloop (it min : nat) (body : nat -> M unit) : M unit :=
  forloopM it min body.
Let forloop0 m body : forloop m m body = Ret tt.
Proof. exact: forloopM0. Qed.
Let forloop1 m n body : forloop (m.+1 + n) m body =
  body (m + n) >> forloop (m + n) m body :> M unit.
Proof. exact: forloopM1. Qed.
HB.instance Definition _ := isMonadStateForLoop.Build S M forloop0 forloop1.
End modelstateforloop.
End ModelStateForLoop.
HB.export ModelStateForLoop.

Module ModelReify.
Section modelreify.
Variables S T : UU0.
Definition state_trace := (S * seq T)%type.
Let M := (StateMonad.acto state_trace).
Let reify : forall A, M A -> state_trace -> option (A * state_trace) := fun A m s => Some (m s).
Let reifyret : forall (A : UU0) (a : A) s, @reify _ (Ret a) s = Some (a, s).
Proof. by []. Qed.
Let reifybind : forall (A B : UU0) (m : M A) (f : A -> M B) s,
  @reify _ (m >>= f) s = match @reify _ m s with | Some a's' => @reify _ (f a's'.1) a's'.2 | None => None end.
Proof.
move=> A B m0 f s.
rewrite state_bindE.
rewrite /uncurry /=.
rewrite /comp /= /reify /=.
by case (m0 s).
Qed.
HB.instance Definition _ := isMonadReify.Build state_trace (StateMonad.acto state_trace)
  reifyret reifybind.
End modelreify.
End ModelReify.
HB.export ModelReify.

Module ModelStateTraceReify.
Section modelstatetracereify.
Variables S T : UU0.
Let acto := (StateMonad.acto (S * seq T)).
Let reifystget :  forall s l, @reify _ _ _ (@st_get _ _ [the stateTraceMonad S T of acto]) (s, l) = Some (s, (s, l)).
Proof. by []. Qed.
Let reifystput : forall s l s', @reify _ _ _ (@st_put _ _ [the stateTraceMonad S T of acto] s') (s, l) = Some (tt, (s', l)).
Proof. by []. Qed.
Let reifystmark : forall t s l, @reify _ _ _ (@st_mark _ _ [the stateTraceMonad S T of acto] t) (s, l) = Some (tt, (s, rcons l t)).
Proof. by []. Qed.
HB.instance Definition _ := isMonadStateTraceReify.Build S T (StateMonad.acto (S * seq T)) reifystget reifystput reifystmark.
End modelstatetracereify.
End ModelStateTraceReify.


(* choice_of_Type is removed from infotheo.convex *)
(* Notation choice_of_Type := convex.choice_of_Type. *)
Definition choice_of_Type (T : Type) : choiceType :=
  Choice.Pack (Choice.Class (boolp.gen_choiceMixin T) (boolp.gen_eqMixin T)).

Module ModelBacktrackableState.
Local Open Scope fset_scope.

Section monad.
Variable S : Type.
Local Obligation Tactic := try by [].

Definition acto : Type -> Type :=
  fun A => S -> {fset (choice_of_Type A * choice_of_Type S)}.
Local Notation M := acto.

Let ret : idfun ~~> M := fun A (a : A) s =>
  [fset (a : choice_of_Type A, s : choice_of_Type S)].

Let bind := fun A B (m : acto A)
  (f : A -> S -> {fset (choice_of_Type B * choice_of_Type S)}) =>
  fun s => \bigcup_(i <- (fun x : choice_of_Type A * choice_of_Type S => f x.1 x.2)
                           @` (m s))
                 i.
Let left_neutral : BindLaws.left_neutral bind ret.
Proof.
move=> A B /= m f; rewrite boolp.funeqE => s.
by rewrite /bind /ret imfset_set1 /= big_seq_fset1.
Qed.

Let right_neutral : BindLaws.right_neutral bind ret.
Proof.
move=> A B /=; rewrite boolp.funeqE => s.
apply/fsetP => /= x; apply/bigfcupP'; case: ifPn => xBs.
  set x' := (x : choice_of_Type A * choice_of_Type S).
  exists [fset x']; last by rewrite inE.
  by apply/imfsetP; exists x' => //=; case: x'.
case => /= SA /imfsetP[] /= sa saBs ->{SA} /fset1P => Hx.
by move: xBs; rewrite Hx; apply/negP; rewrite negbK; case: sa saBs Hx.
Qed.

Let associative : BindLaws.associative bind.
Proof.
move=> A B C /= m f g; rewrite boolp.funeqE => s.
have @g' : choice_of_Type B -> choice_of_Type S ->
    {fset choice_of_Type C * choice_of_Type S}.
  by move=> b' s'; exact: (g b' s').
apply/fsetP => /= x; apply/bigfcupP'/bigfcupP'; case => /= CS  /imfsetP[/=].
- move=> bs /bigfcupP'[/= BS]  /imfsetP[/= sa] sams ->{BS} bsfsa ->{CS} xgbs.
  exists (\bigcup_(i <- [fset g' x0.1 x0.2 | x0 in f sa.1 sa.2]) i).
    by apply/imfsetP => /=; exists sa.
  apply/bigfcupP'; exists (g bs.1 bs.2) => //; by apply/imfsetP => /=; exists bs.
- move=> sa sams ->{CS} /bigfcupP'[/= CS]  /imfsetP[/= bs] bsfsa ->{CS} xgbs.
  exists (g bs.1 bs.2) => //; apply/imfsetP => /=; exists bs => //.
  apply/bigfcupP' => /=; exists (f sa.1 sa.2) => //; apply/imfsetP => /=.
  by exists sa.
Qed.

HB.instance Definition _ :=
  isMonad_ret_bind.Build acto left_neutral right_neutral associative.

Lemma bindE (A B : Type) m (f : A -> [the monad of acto] B) :
  m >>= f = fun s =>
    \bigcup_(i <- (fun x : choice_of_Type A * choice_of_Type S => f x.1 x.2)
                 @` (m s))
    i.
Proof.
apply boolp.funext => s.
rewrite bindE /= /join_of_bind /= /bind /=.
set lhs := [fset _ _ | _ in _].
set rhs := [fset _ _ | _ in _].
rewrite (_ : lhs = rhs) //; apply/fsetP => x; rewrite {}/lhs {}/rhs.
apply/idP/imfsetP => /=.
- case/imfsetP => -[a1 a2] /=.
  rewrite /actm /= /map /=.
  case/bigfcupP' => /= b.
  case/imfsetP => -[b1 b2] /= Hb ->{b} /fset1P[-> -> ->{x a1 a2}].
  by exists (b1, b2).
- case=> -[a1 s1] Ha /= ->{x}.
  apply/imfsetP => /=.
  rewrite /actm /= /map /=.
  eexists.
  + apply/bigfcupP' => /=.
    eexists.
      apply/imfsetP => /=.
      by exists (a1, s1).
    by apply/fset1P; reflexivity.
  + by [].
Qed.

End monad.

Section state.
Variable S : Type.
Let get : acto S S :=
  fun s => [fset (s : choice_of_Type S, s : choice_of_Type S)].
Let put := (fun s => (fun _ => [fset (tt : choice_of_Type unit,
                                s : choice_of_Type S)])) : S -> (acto S unit).
Let putput : forall s s', put s >> put s' = put s'.
Proof.
move=> s s'; apply boolp.funext => s''.
rewrite bindE; apply/fsetP => /= x; apply/bigfcupP'/fset1P.
- by case => /= x0 /imfsetP[/= x1] /fset1P _ -> /fset1P.
- move=> -> /=.
  exists [fset ((tt, s') : choice_of_Type unit * choice_of_Type S)] => /=; last first.
    exact/fset1P.
  apply/imfsetP => /=; exists (tt, s) => //; exact/fset1P.
Qed.
Let putget : forall s, put s >> get = put s >> Ret s.
Proof.
move=> s; rewrite boolp.funeqE => s'.
rewrite 2!bindE /=; apply/fsetP => /= x; apply/bigfcupP'/bigfcupP'.
- case => /= x0 /imfsetP[/= x1] /fset1P -> -> /fset1P ->.
  exists [fset ((s, s) : choice_of_Type S * choice_of_Type S)]; last first.
    exact/fset1P.
  apply/imfsetP => /=; exists (tt, s) => //; exact/fset1P.
- case => /= x0 /imfsetP[/= x1] /fset1P -> -> /fset1P ->.
  exists [fset ((s ,s) : choice_of_Type S * choice_of_Type S)]; last first.
    exact/fset1P.
  apply/imfsetP => /=; exists (tt, s) => //; exact/fset1P.
Qed.
Let getput : get >>= put = skip.
Proof.
rewrite boolp.funeqE => s.
rewrite bindE /skip /= /Ret; apply/fsetP => /= x; apply/bigfcupP'/idP.
- case => /= x0 /imfsetP[/= x1] /fset1P -> -> /fset1P ->; exact/fset1P.
- move/fset1P => ->.
  exists [fset ((tt, s) : choice_of_Type unit * choice_of_Type S)]; last first.
    exact/fset1P.
  by apply/imfsetP; exists (s, s) => //; rewrite inE.
Qed.
Let getget : forall (A : UU0) (k : S -> S -> _ A),
  get >>= (fun s => get >>= k s) = get >>= fun s => k s s.
Proof.
move=> A k; rewrite boolp.funeqE => s.
rewrite 2!bindE; apply/fsetP => x; apply/bigfcupP'/bigfcupP'.
- case => /= x0 /imfsetP[/= x1] /fset1P -> ->.
  rewrite bindE => /bigfcupP'[/= x2] /imfsetP[/= x3] /fset1P -> -> xkss.
  exists (k s s s) => //; apply/imfsetP; exists (s, s) => //; by rewrite inE.
- case => /= x0 /imfsetP[/= x1] /fset1P -> -> /= xksss.
  have @k' : choice_of_Type S -> choice_of_Type S ->
    (choice_of_Type S -> {fset choice_of_Type A * choice_of_Type S}).
    move=> a b s'; exact: (k a b s').
  exists (\bigcup_(i <- [fset k' (s, s).1 x2.1 x2.2 |
              x2 in [fset (((s, s).2, (s, s).2) : choice_of_Type S * choice_of_Type S)]]) i).
    apply/imfsetP ; exists (s, s); by [rewrite inE | rewrite bindE].
  apply/bigfcupP'; exists (k s s s) => //; apply/imfsetP; exists (s, s) => //=.
  exact/fset1P.
Qed.

HB.instance Definition _ := isMonadState.Build
  S (acto S) putput putget getput getget.

End state.

Section fail.
Variable S : choiceType.
Let fail : forall A, acto S A := (fun (A : Type) (_ : S) => fset0).
Let bindfailf : BindLaws.left_zero (@bind _ ) fail.
Proof.
move=> A B g; rewrite boolp.funeqE => s; apply/fsetP => x; rewrite inE bindE.
apply/negbTE/bigfcupP'; case => /= x0 /imfsetP[/= sa].
by rewrite (@in_fset0 (choice_of_Type A * choice_of_Type S)%type).
Qed.

HB.instance Definition _ := isMonadFail.Build (acto S) bindfailf.
End fail.

Section alt.
Variable S : choiceType.
Let M := [the monad of acto S].
Let alt := (fun (A : Type) (a b : S -> {fset choice_of_Type A * choice_of_Type S}) (s : S) => a s `|` b s).
Let altA : forall T : UU0, ssrfun.associative (@alt T).
Proof. by move=> A a b c; rewrite boolp.funeqE => s; rewrite /alt fsetUA. Qed.
Let alt_bindDl : BindLaws.left_distributive (@bind M) (@alt).
Proof.
move=> A B /= m1 m2 k; rewrite boolp.funeqE => s; rewrite !bindE /=.
apply/fsetP => /= bs; apply/bigfcupP'/fsetUP.
- case => /= BS /imfsetP[/= sa] /fsetUP[sam1s ->{BS} Hbs|sam2s ->{BS} Hbs].
  + left; apply/bigfcupP' => /=; exists (k sa.1 sa.2) => //.
    by apply/imfsetP; exists sa.
  + right; apply/bigfcupP' => /=; exists (k sa.1 sa.2) => //.
    by apply/imfsetP; exists sa.
- case => /bigfcupP'[/= BS /imfsetP[/= sa sams ->{BS} bsksa]].
  by exists (k sa.1 sa.2) => //; apply/imfsetP; exists sa => //; rewrite inE sams.
  by exists (k sa.1 sa.2) => //; apply/imfsetP; exists sa => //; rewrite inE sams orbT.
Qed.
HB.instance Definition _ := isMonadAlt.Build (acto S) altA alt_bindDl.
End alt.

Section nondet.

Variable S : choiceType.
Let M : failMonad := [the failMonad of acto S].
Let N : altMonad := [the altMonad of acto S].
Let altfailm : @BindLaws.left_id _ (@fail M) (@alt N).
Proof. by move=> A /= m; rewrite boolp.funeqE => s; rewrite /alt /= fset0U. Qed.
Let altmfail : @BindLaws.right_id _ (@fail M) (@alt N).
Proof. by move=> A /= m; rewrite boolp.funeqE => s; rewrite /alt /= fsetU0. Qed.
HB.instance Definition _ := isMonadNondet.Build (acto S) altfailm altmfail.
End nondet.

Section failR0monad.
Variable S : choiceType.
Let bindmfail : BindLaws.right_zero (@bind [the monad of acto S]) (@fail _).
Proof.
move=> A B /= g; rewrite bindE /=; rewrite boolp.funeqE => s; apply/fsetP => /= sa.
apply/idP/idP/bigfcupP'.
case => /= SA /imfsetP[/= bs bsgs ->{SA}].
by rewrite (@in_fset0 (choice_of_Type A * choice_of_Type S)%type).
Qed.
HB.instance Definition _ := isMonadFailR0.Build (acto S) bindmfail.
End failR0monad.

Section preplusmonad.

Variable S : choiceType.
Let alt_bindDr : BindLaws.right_distributive (@bind [the monad of acto S]) (@alt _).
Proof.
move=> A B /= m k1 k2; rewrite boolp.funeqE => s; rewrite !bindE /=.
apply/fsetP => /= bs; apply/bigfcupP'/idP.
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

HB.instance Definition _ := isMonadPrePlus.Build (acto S) alt_bindDr.

End preplusmonad.

End ModelBacktrackableState.
Module ModelArray.
Section modelarray.
Variables (S : UU0) (I : eqType).
Implicit Types (i j : I) (A : UU0).
Definition acto := StateMonad.acto (I -> S).
Local Notation M := acto.
Definition aget i : M S := fun a => (a i, a).
Definition aput i s : M unit := fun a => (tt, insert i s a).
Let aputput i s s' : aput i s >> aput i s' = aput i s'.
Proof.
rewrite state_bindE; apply boolp.funext => a/=.
by rewrite /aput compE/= insert_insert.
Qed.
Let aputget i s A (k : S -> M A) : aput i s >> aget i >>= k = aput i s >> k s.
Proof.
rewrite state_bindE; apply boolp.funext => a/=.
by rewrite /aput compE/= insert_same.
Qed.
Let agetput i : aget i >>= aput i = skip.
Proof.
rewrite state_bindE; apply boolp.funext => a/=.
by rewrite /aput compE/= insert_same2.
Qed.
Let agetget i A (k : S -> S -> M A) :
  aget i >>= (fun s => aget i >>= k s) = aget i >>= fun s => k s s.
Proof. by []. Qed.
Let agetC i j A (k : S -> S -> M A) :
  aget i >>= (fun u => aget j >>= (fun v => k u v)) =
  aget j >>= (fun v => aget i >>= (fun u => k u v)).
Proof. by []. Qed.
Let aputC i j u v : (i != j) \/ (u = v) ->
  aput i u >> aput j v = aput j v >> aput i u.
Proof.
by move=> [ij|->{u}]; rewrite !state_bindE /aput; apply/boolp.funext => a/=;
  [rewrite compE/= insertC|rewrite compE/= insertC2].
Qed.
Let aputgetC i j u A (k : S -> M A) : i != j ->
  aput i u >> aget j >>= k = aget j >>= (fun v => aput i u >> k v).
Proof.
move=> ij; rewrite /aput !state_bindE; apply boolp.funext => a/=.
by rewrite !compE/= state_bindE/= {1}/insert (negbTE ij).
Qed.
HB.instance Definition _ := Monad.on M.
HB.instance Definition _ := isMonadArray.Build
  S I M aputput aputget agetput agetget agetC aputC aputgetC.
End modelarray.
End ModelArray.
HB.export ModelArray.

Module ModelUnion.
Section modelunion.

Variables (S : UU0).
Local Notation I := nat.
Implicit Types (i j : I) (A : UU0).

Definition is_forest (f:I->I) := forall x, (f x) <=  x.

Definition forestType := {f : I -> I | is_forest f}.

Function find_rec (f:forestType) (i:I) {wf lt i} :=
  let y := sval f i in
  if y == i then i else find_rec f y.
Proof.
  - by move=> f x H; apply/ltP; rewrite ltn_neqAle H (proj2_sig f).
  - exact: lt_wf.
Defined.

Definition equiv (f1 f2 : forestType) := find_rec f1 = find_rec f2. 

Definition is_equiv A (g1 g2 : forestType-> (I->S) -> A * forestType * (I->S)) := forall f1 f2 v,
      equiv f1 f2 ->  
      (g1 f1 v).1.1 = (g2 f2 v).1.1 /\ 
      equiv (g1 f1 v).1.2 (g2 f2 v).1.2 /\ 
      (g1 f1 v).2 = (g2 f2 v).2 .

Definition is_eqMonad A g := (@is_equiv A g g).

Definition acto : UU0 -> UU0 := fun A =>
   {g : forestType-> (I->S) -> A * forestType * (I->S) | is_eqMonad g }.

Local Notation M := acto. 

Lemma ret_correct : forall A (a:A), is_eqMonad (fun f g => (a, f, g)).
Proof.
  by move=> A a f1 f2 v Hequiv; do 2 split. 
Qed.

Let ret : idfun ~~> M := fun A a => exist _ (fun f => fun g => (a, f, g)) (ret_correct a). 

Lemma bind_correct : forall (A B : UU0) (m : M A) (t : A -> M B), 
is_eqMonad (fun f g =>
    let: (a, f', g') := (proj1_sig m) f g in
    (proj1_sig (t a)) f' g').
Proof.
  move=> A B m t f1 f2 v Heq;
  case: m => m hm /=;
  move: {hm} (hm _ _ v Heq);
  case: (m f1 v) => [[a1 f1'] g1];
  case: (m f2 v) => [[a2 f2'] g2] /= [] <- Heq';
  case: (t a1) => tm htm /=;
  unfold is_eqMonad in htm;
  case Heq' => Heq'' eqg;
  rewrite eqg;
  exact : (htm _ _ g2 Heq'').
Defined.

Let bind (A B : UU0) (m : M A) (t : A -> M B) : M B :=
  exist _ _  (bind_correct m t).

Local Notation "a '>>=' b" := (bind a b).
Local Notation "a '>>' b" := (bind a (fun _ => b)).

Let left_neutral : BindLaws.left_neutral bind ret.
Proof.
  move => A B a t.
  move H: (t a) => [f' Hf'] /=.
  by apply boolp.eq_exist;
  rewrite /=;
  apply: boolp.funext => f;
  apply: boolp.funext => g;
  rewrite H.
Qed.

Let right_neutral : BindLaws.right_neutral bind ret.
Proof.
  by move=>A t;
  case: t => [f' Hf'] /=;
  apply boolp.eq_exist;
  apply boolp.funext => f; apply boolp.funext => g /=;
  case: (f' f g) => [[a f'0] g']. 
Qed.

Let associative : BindLaws.associative bind.
Proof.
  move=> A B C a b c.
  apply boolp.eq_exist;
  apply boolp.funext => f; apply boolp.funext => g.
  case a => fa Hfa /=.
  by case (fa f g) => [[a0 f'] g'].
Qed.

HB.instance Definition _ := 
  isMonad_ret_bind.Build acto left_neutral right_neutral associative.

Definition find_correct : forall i, is_eqMonad (fun f => fun v => (find_rec f i, f, v)).
Proof.
  by move=> i f1 f2 v Hequiv; rewrite Hequiv. 
Qed.

Definition find (i : I) : M I :=
  exist _ (fun f => fun v => (find_rec f i, f, v)) (find_correct i).

Lemma find_step : forall f i, find_rec f i= find_rec f (proj1_sig f i).
Proof.
  move=> f i.
  functional induction (find_rec f i).
  2: reflexivity.
  have: sval f i = i by move/eqP in e.
  by move=> e_prop; rewrite e_prop find_rec_equation e.
Qed.

Lemma find_return_root : forall f i, sval f (find_rec f i) = find_rec f i.
Proof.
  move=> f i.
  functional induction (find_rec f i).
  by move/eqP in e.
  exact IHn.
Qed.

Lemma find_root : forall i f , find_rec f (find_rec f i) = find_rec f i.
Proof.
  move=> i f.
  rewrite {1} find_rec_equation.
  by rewrite find_return_root eq_refl.
Qed.

Definition union_func (f:forestType) (i:I) (i':I) : I->I :=
  let rep_i := find_rec f i in
  let rep_i' := find_rec f i' in
  if rep_i == rep_i' then proj1_sig f
  else if rep_i < rep_i' then
    (fun j => if j== rep_i' then rep_i else proj1_sig f j)
  else
    (fun j => if j== rep_i then rep_i' else proj1_sig f j).

Lemma is_forest_after_union :
  forall (f : forestType) i i',
  find_rec f i < find_rec f i' ->
  is_forest (fun j => if j == find_rec f i' then find_rec f i else sval f j).
Proof.
  move=> f i i' Hinf j.
  case H: (j == find_rec f i').
  by move /eqP in H; rewrite H; apply ltnW.
  apply (proj2_sig f).
Qed.

Lemma lt_case : forall m n, m < n = false -> m == n = false -> n < m.
Proof.
  by move=> m n; case: ltngtP.
Qed.

Lemma union_correct : forall f i i', is_forest (union_func f i i').
Proof.
  move=> f i i' j.
  rewrite /union_func .
  case: ifPn => Heq.
  by apply (proj2_sig f).
  case Hlne:  ((find_rec f i) < (find_rec f i')); apply is_forest_after_union.
  by apply Hlne.
  apply: (lt_case Hlne).
  by do 2 apply /eqP.
Defined.

Definition union_exist f i i':= exist _ _ (union_correct f i i'). 

Lemma find_changed_union :
  forall i i' j f , find_rec f j = find_rec f i -> 
  find_rec f i' < find_rec f i ->
  find_rec (union_exist f i' i) j = find_rec f i'.
Proof.
  move=> i i' j f Hfind Hlti.
  rewrite /union_exist.
  move: (union_correct f i' i).
  rewrite /union_func.
  have: (find_rec f i' == find_rec f i = false) by apply (ltn_eqF Hlti).
  move=> ->; rewrite Hlti => Hf.
  case Heq: (j == find_rec f i).
  - rewrite {1}find_rec_equation /= Heq.
    case Hroot: (find_rec f i' == j).
    + by move/eqP in Hroot; symmetry.
    rewrite {1}find_rec_equation /=.
    case (find_rec f i' == find_rec f i ).
    + by rewrite eq_refl.
    + by rewrite find_return_root eq_refl.
  - set (new_f := (exist is_forest (fun j0 => if j0 == find_rec f i then find_rec f i' else sval f j0) Hf)).
    functional induction (find_rec new_f j).
    simpl in e.
    rewrite Heq in e. 
    rewrite {1}find_rec_equation in Hfind.
    rewrite e in Hfind.
    by move/eqP in Heq.
  - case Heqf: (sval (exist is_forest (fun j0 => if j0 == find_rec f i then find_rec f i' else sval f j0) Hf) i0 == find_rec f i).
    + move/eqP in Heqf;rewrite Heqf.
    rewrite find_rec_equation /= eq_refl.
    + case Heqf': (find_rec f i' == find_rec f i).
      * by move/eqP in Heqf'.
      * by rewrite find_rec_equation /= Heqf' find_return_root eq_refl. 
    apply IHn => /=; rewrite Heq. 
    + by rewrite find_step in Hfind.
    + by simpl in Heqf; rewrite Heq in Heqf.
Defined.

Lemma find_unchanged_union :
  forall i i' j f, find_rec f j != find_rec f i -> 
  find_rec f i' < find_rec f i ->
  find_rec (union_exist f i' i) j = find_rec f j.
Proof.
  move=> i i' j f Hfind Hlti.
  rewrite /union_exist.
  move: (union_correct f i' i).
  rewrite /union_func.
  have: (find_rec f i' == find_rec f i = false) by apply (ltn_eqF Hlti).
  move=> ->. rewrite Hlti => Hf.
   set (new_f := (exist is_forest (fun j0 => if j0 == find_rec f i then find_rec f i' else sval f j0) Hf)).
    functional induction (find_rec new_f j).
    simpl in e.
    case Heq: (i0 == find_rec f i); rewrite Heq in e.
    - by move/eqP in Heq;
      rewrite find_rec_equation Heq find_return_root eq_refl.
    - by move/eqP in e; rewrite find_rec_equation e eq_refl.
  - symmetry; rewrite find_step; symmetry.
  have: ( sval f i0 = (sval (exist is_forest (fun j0 => if j0 == find_rec f i then find_rec f i' else sval f j0) Hf) i0)).
    +simpl.
      case Heq: (i0 == find_rec f i).
      move/eqP in Heq.
      by rewrite Heq find_rec_equation find_return_root eq_refl eq_refl in Hfind. 
      by reflexivity.
    + move=> ->. apply IHn=>/=.
      case Heq: (i0 == find_rec f i).
      - by move/eqP in Heq;
        rewrite find_rec_equation Heq find_return_root eq_refl eq_refl in Hfind.
      - by rewrite find_step in Hfind.
Defined.

Lemma exist_surjective: forall f Hf, f = (exist is_forest (sval f) Hf).
Proof.
  move=> f.
  case f => [f' Hf']; move=> Hf. 
  by apply boolp.eq_exist.
Qed.

Lemma union_func_Symm : 
forall i i' f, union_func f i i' = union_func f i' i.
Proof.
  move=> i i' f.
  rewrite /union_func eq_sym.
  case Heq : (find_rec f i' == find_rec f i); try reflexivity.
  case Hlt: (find_rec f i < find_rec f i').
  - have: ((find_rec f i' < find_rec f i) = false ) 
    by rewrite ltnNge; apply Bool.negb_false_iff; apply ltnW in Hlt; apply Hlt.
  by move=> ->.
  - rewrite eq_sym in Heq.
  by rewrite (lt_case Hlt Heq).
Qed.

Lemma union_exist_Symm : forall i i' f, 
  union_exist f i i' = union_exist f i' i.
Proof.
  by move=>i i' f; apply boolp.eq_exist, union_func_Symm.
Qed.

Lemma Union_correct_equiv_aux i i' f1 f2 j:
  find_rec f1 = find_rec f2 ->  
  find_rec f1 i < find_rec f1 i' ->
  find_rec (union_exist f1 i i') j = find_rec (union_exist f2 i i') j.
Proof.
  move=> Hequiv Hlti.
  case Hji: (find_rec f1 j == find_rec f1 i'); move/eqP in Hji.
  *  rewrite (find_changed_union  Hji Hlti).
    rewrite Hequiv in Hji, Hlti.
    by rewrite (find_changed_union Hji Hlti) Hequiv.
  * move/eqP in Hji.
    rewrite (find_unchanged_union  Hji Hlti).
    rewrite Hequiv in Hji, Hlti.
    by rewrite (find_unchanged_union Hji Hlti) Hequiv.
Qed.

Lemma Union_correct_equiv : forall i i', is_eqMonad (fun f => fun g => (tt, (union_exist f i i'), g)).
Proof.
  move =>i i' f1 f2 v Hequiv => /=.
  do 2 (split; try easy).
  rewrite /equiv in Hequiv.
  apply boolp.funext => j /=.
  case Heq: (find_rec f1 i == find_rec f1 i').
  -   rewrite /equiv /union_exist.
  move: (union_correct f1 i i') (union_correct f2 i i').
  rewrite /union_func; rewrite  <- Hequiv, Heq.
  by move=> Hf1 Hf2; do 2 rewrite <- exist_surjective; rewrite Hequiv.
  - case Hlti:  (find_rec f1 i < find_rec f1 i').
    by apply Union_correct_equiv_aux.
  - apply (lt_case Hlti) in Heq.
    rewrite !(union_exist_Symm i i').
    by apply Union_correct_equiv_aux. 
Defined.

Definition union (i:I) (i' : I) : M unit :=
exist _ (fun f => fun g => (tt, union_exist f i i', g)) (Union_correct_equiv i i').

Definition Bis A (P Q : M A) :=
  forall f g, 
    (sval P f g).1.1 = (sval Q f g).1.1 /\
    equiv (sval P f g).1.2 (sval Q f g).1.2 /\
    (sval P f g).2 = (sval Q f g).2 .

Local Notation "a '≈' b" := (Bis a b).

Lemma refl A (d : M A) : d ≈ d. 
Proof.
  by move=> f g;case (sval d f g) => [[a f'] g'].
Qed.

Lemma sym A (d1 d2 : M A) : d1 ≈ d2 -> d2 ≈ d1.
Proof.
  move=> Hbisim f g.
  case (Hbisim f g)=>[H0 H1].
  case H1 => [H2 H3].
  revert H0 H2 H3.
  case (sval d2 f g) => [[a1 f1] g1].
  case (sval d1 f g) => [[a2 f2] g2].
  simpl.
  move=>H0 H2 H3.
  do 2 (split; try easy).
Qed.

Lemma trans A (d1 d2 d3 : M A) : d1 ≈ d2 -> d2 ≈ d3 -> d1 ≈ d3.
Proof.
  move => Hb1 Hb2 f g.
  case: (Hb1 f g) => [Hb1_1 [Hb1_2 Hb1_3]].
  case: (Hb2 f g) => [Hb2_1 [Hb2_2 Hb2_3]].
  rewrite /equiv in Hb1_2 Hb2_2 *.
  by rewrite Hb1_1 Hb1_2 Hb1_3.
Qed.

Lemma bindl A B (t : A -> M B) (d1 d2 : M A) : d1 ≈ d2 -> (d1 >>= t) ≈ (d2 >>= t).
Proof.
  move=> Hbisim f g/=.
  case: (Hbisim f g) => [Hbisim1 [Hbisim2 Hbisim3]].
  move: Hbisim1 Hbisim2 Hbisim3.
  case (sval d1 f g)=>[[a f0] g0].
  case (sval d2 f g)=>[[a1 f1] g1] /=.
  move=> -> H ->.
  case (t a1) => t_func Ht /=.
  by apply (Ht f0 f1 g1).
Qed.

Lemma bindr A B (f g : A -> M B) d :
  (forall a, f a ≈ g a) -> (d >>= f) ≈ (d >>= g).
Proof.
  by rewrite /Bis => Hbis f' g' /=; case (sval d f' g') => [[a f0] g0].
Qed.

HB.instance Definition _ := @hasPreorder.Build M Bis
  (@refl) (@trans) (@bindl) (@bindr).

HB.instance Definition _ := @hasEquivalence.Build M (@sym).

Lemma eq_is_bisim : forall A (P Q : M A) , P = Q -> P ≈ Q.
Proof.
  by move=> A P Q Heq; unfold "≈"; rewrite Heq.
Qed.

Let findfind (A : UU0) i (k : I -> I -> M A):
    find i >>= (fun r => find i >>= (fun r' => k r r')) ≈ find i >>= (fun r => k r r).
Proof.
  by
  apply eq_is_bisim, boolp.eq_exist, boolp.funext => f/=;
  apply boolp.funext => g/=.
Qed.

Let unionfind i i': union i i'>> find i ≈ union i i' >> find i'.
Proof.
  apply eq_is_bisim, boolp.eq_exist, boolp.funext => f; apply boolp.funext => g/=.
  do 2 (apply pair_equal_spec; split; try easy).
  rewrite /union_exist.
  case Heq: (find_rec f i == find_rec f i').
  -move: (union_correct f i i').
  rewrite /union_func Heq => Hf.
  rewrite <- exist_surjective.
  by move/eqP in Heq.
  case Hlti:  (find_rec f i < find_rec f i').
  - move/eqP /eqP in Heq.
    by rewrite (find_unchanged_union  Heq Hlti)
          (find_changed_union  erefl Hlti).
  - have Hlti' := (lt_case Hlti Heq).  
    move/eqP /nesym /eqP in Heq.
    fold (union_exist f i i').
    by rewrite (union_exist_Symm i i')
          (find_unchanged_union Heq Hlti')
          (find_changed_union erefl Hlti').
Qed.

Let findunion i i': find i' >>= (fun v => union i v) ≈ union i i'.
Proof.
  apply eq_is_bisim, boolp.eq_exist ,boolp.funext => f; apply boolp.funext => g/=.
  do 2 (apply pair_equal_spec; split; try easy).
  apply boolp.eq_exist.
  by rewrite /union_func find_root.
Qed.

Lemma union_exist_id f i i':
(find_rec f i == find_rec f i') = true ->
(union_exist f i i') = f.
Proof.
  move=> Heq.
  rewrite /union_exist.
  move: (union_correct f i i').
  rewrite /union_func Heq => Hf.
  by rewrite <- exist_surjective.
Qed.

Let unionSymm i i': union i i' ≈ union i' i.
Proof.
  apply eq_is_bisim, boolp.eq_exist, boolp.funext => f; 
  apply boolp.funext => g /=.
  do 2 (rewrite pair_equal_spec;split; try reflexivity).
  apply union_exist_Symm.
Qed.

Lemma findunionfind_lt : forall f i i' u,
find_rec f i < find_rec f i' -> 
find_rec (union_exist f i i') (find_rec f u) = find_rec (union_exist f i i') u.
Proof.
  move=>f i i' u Hlti.
  rewrite -(find_root u (union_exist f i i')).
  case H: (find_rec f u == find_rec f i'); move/eqP in H.
  - rewrite (find_changed_union H Hlti).
    have Hi : find_rec f (find_rec f i) != find_rec f i'
      by rewrite find_root;move/ltn_eqF /eqP /eqP in Hlti.
    rewrite -find_root in H. 
    by rewrite (find_changed_union H Hlti) (find_unchanged_union Hi Hlti) find_root.
  - by move/eqP in H; rewrite (find_unchanged_union H Hlti).
Qed.

Let findunionfind i i' u:
  find u >>= (fun v => union i i' >> find v) ≈ union i i' >> find u.
Proof.
  rewrite /union. 
  apply eq_is_bisim, boolp.eq_exist, boolp.funext => f;apply boolp.funext => g.
  case Heq: (find_rec f i == find_rec f i')=>/=.
  by rewrite (union_exist_id Heq) find_root.
  case Hlti: (find_rec f i < find_rec f i').
  by rewrite findunionfind_lt .
  by rewrite union_exist_Symm (findunionfind_lt u (lt_case Hlti Heq)).
Qed.

Let union_id : forall i, union i i ≈ skip.
Proof.
  move=> i. 
  apply eq_is_bisim, boolp.eq_exist, boolp.funext => f; apply boolp.funext => g.
  by rewrite (union_exist_id (eqxx (find_rec f i))).
Qed.    

Let findC : forall (A : UU0) i i' (k : I -> I -> M A),
    find i >>= (fun u => find i' >>= (fun v => k u v)) ≈
    find i' >>= (fun v => find i >>= (fun u => k u v)).
Proof.
  by move=> A i i' k;
  apply eq_is_bisim,boolp.eq_exist, boolp.funext => f; 
  apply boolp.funext => g /=.
Qed.  

Lemma find_unchanged_unchanged_union: 
forall f i i' u v j,
find_rec f i > find_rec f i' ->
find_rec f j <> find_rec f i ->
find_rec (union_exist f i i') u > find_rec (union_exist f i i') v ->
find_rec f j <> find_rec (union_exist f i i') u ->
find_rec (union_exist (union_exist f i i') u v) j = find_rec f j.
Proof.
  move=>f i i' u v j Hlti /eqP Hji Hltu /eqP Hju.
  -rewrite (union_exist_Symm i i') (union_exist_Symm u v) find_unchanged_union.
  + by apply (find_unchanged_union  Hji Hlti).
  + by rewrite(find_unchanged_union  Hji Hlti) (union_exist_Symm i' i) .
  + by rewrite (union_exist_Symm i' i).
Qed.

Lemma find_unchanged_changed_union_neq: 
forall f i i' u v j,
find_rec f i > find_rec f i' ->
find_rec f j <> find_rec f i ->
find_rec (union_exist f i i') u > find_rec (union_exist f i i') v ->
find_rec f j = find_rec (union_exist f i i') u ->
find_rec (union_exist f i i') v <> find_rec f i ->
find_rec (union_exist (union_exist f i i') u v) j = find_rec (union_exist f i i') v.
Proof.
  move=> f i i' u v j Hlti /eqP Hji Hltu Hju /eqP Heqvi.
  rewrite (union_exist_Symm i i') (union_exist_Symm u v) find_changed_union. 
  + by [].
  + by rewrite (find_unchanged_union Hji Hlti) Hju (union_exist_Symm i i').
  + by rewrite (union_exist_Symm i' i).
Qed.

Lemma find_changed_unchanged_union: 
forall f i i' u v j,
find_rec f i > find_rec f i' ->
find_rec f j = find_rec f i ->
find_rec (union_exist f i i') u > find_rec (union_exist f i i') v ->
find_rec f i' <> find_rec (union_exist f i i') u ->
find_rec (union_exist (union_exist f i i') u v) j = find_rec f i'.
Proof.
  move=> f i i' u v j Hlti Hji Hltu /eqP Hju.
  rewrite (union_exist_Symm i i') (union_exist_Symm u v) find_unchanged_union. 
  + by rewrite find_changed_union. 
  + by rewrite (find_changed_union Hji Hlti) (union_exist_Symm i' i).
  + by rewrite (union_exist_Symm i' i).
Qed.

Lemma union_dec : forall f i i' j,
find_rec (union_exist f i' i) j <= find_rec f j .
Proof.
  move=> f i i' j.
  case Heqi: (find_rec f i' == find_rec f i).
  - rewrite /union_exist.
  move: (union_correct f i' i).
  rewrite /union_func Heqi => Hf.
  by rewrite <- exist_surjective.
  case Hlti : (find_rec f i' < find_rec f i).
  - case Hji: (find_rec f j == find_rec f i); move/eqP in Hji.
    +rewrite (find_changed_union Hji Hlti).
    rewrite <- Hji in Hlti.
    +by apply ltnW.
    by move/eqP in Hji; rewrite (find_unchanged_union Hji Hlti).
  - have Hlti' := lt_case Hlti Heqi; rewrite union_exist_Symm.
    case Hji: (find_rec f j == find_rec f i'); move/eqP in Hji.
    +rewrite (find_changed_union Hji Hlti').
    rewrite <- Hji in Hlti'.
    +by apply ltnW.
    by move/eqP in Hji; rewrite (find_unchanged_union Hji Hlti').
Qed.

Lemma union_root_eq:
forall f i i' j,
find_rec f i > find_rec f i' ->
find_rec (union_exist f i i') j = find_rec (union_exist f i i') (find_rec f j).
Proof.
  move=>f i i' j Hlti.
  case Heq: (find_rec f j == find_rec f i);move/eqP in Heq.
  - by rewrite union_exist_Symm (find_changed_union Heq Hlti) Heq
    (find_changed_union (find_root i f) Hlti).
  - move /eqP in Heq.
    rewrite union_exist_Symm (find_unchanged_union Heq Hlti).
    rewrite -(find_root j f) in Heq.
    by rewrite (find_unchanged_union Heq Hlti) find_root.
Qed.

Lemma find_unchanged_changed_union_eq: 
forall f i i' u v j,
find_rec f i > find_rec f i' ->
find_rec f j <> find_rec f i ->
find_rec f u > find_rec f v ->
find_rec f j = find_rec f u ->
find_rec f v = find_rec f i  ->
find_rec (union_exist f i i') v < find_rec (union_exist f i i') u ->
find_rec (union_exist (union_exist f i i') u v) j = find_rec f i'.
Proof.
  move=> f i i' u v j Hlti /eqP Hji Hltuf Hju Heqvi Hltu.
  rewrite (union_root_eq j Hltu).
  rewrite (union_root_eq j Hlti).
  rewrite -find_root in Hji.
  rewrite (union_exist_Symm i i') (find_unchanged_union Hji Hlti) find_root Hju find_rec_equation /=.
  have Hui : find_rec f u != find_rec f i.
    by rewrite -Heqvi; move/ltn_eqF /eqP /nesym /eqP in Hltuf. 
  have Hfindu : union_func (union_exist f i' i) u v (find_rec f u) = find_rec f i'.
    rewrite union_func_Symm union_exist_Symm /union_func Hltu (ltn_eqF Hltu).
    rewrite union_exist_Symm (find_unchanged_union Hui Hlti) eq_refl.
    by rewrite (find_changed_union Heqvi Hlti).
  have Hfindi' : ((find_rec f u == find_rec f i') = false).
    apply /eqP => Hcontr.
    rewrite Hcontr Heqvi in Hltuf.
    apply (ltn_trans Hltuf) in Hlti.
    by rewrite ltnn in Hlti.
  rewrite Hfindu eq_sym Hfindi' find_rec_equation/=. 
  have Hrooti' : union_func (union_exist f i' i) u v (find_rec f i') = find_rec f i'.
    rewrite union_func_Symm union_exist_Symm /union_func Hltu (ltn_eqF Hltu).
    rewrite union_exist_Symm (find_unchanged_union Hui Hlti) eq_sym Hfindi'/=.
    by rewrite /union_func Hlti !(ltn_eqF Hlti) find_return_root.
  by rewrite Hrooti' eq_refl.
Qed.


Lemma union_diff : forall f i i' j,
find_rec f i < find_rec f i' ->
find_rec (union_exist f i' i) j < find_rec f j ->
find_rec f j = find_rec f i'.
Proof.
  move=>f i i' j Hlti Hlt.
  case H: (find_rec f j == find_rec f i'); move /eqP in H.
  - by [].
  - by move/eqP in H; rewrite (union_exist_Symm i' i) (find_unchanged_union H Hlti) ltnn in Hlt.
Qed.

Lemma lt_union : 
forall f i i' u v,
find_rec f i > find_rec f i' ->
find_rec (union_exist f i i') u > find_rec (union_exist f i i') v ->
find_rec f i' = find_rec (union_exist f i i') u ->
find_rec f v < find_rec f i.
Proof.
  move=> f i i' u v Hlti Hltu Hju.
  case H: (find_rec (union_exist f i' i) v == find_rec f v); move/eqP in H.
  - rewrite Hju in Hlti.
    rewrite (union_exist_Symm i i') H  (union_exist_Symm i' i) in Hltu.
    apply (ltn_trans Hltu Hlti).
  - move/eqP in H. have H' := union_dec f i' i v.
    have: find_rec (union_exist f i i') v < find_rec f v
    by rewrite ltn_neqAle Bool.andb_lazy_alt union_exist_Symm H union_exist_Symm.
    move=> Hlt'. have H0 := union_diff Hlti Hlt'.
    have H1 := (find_changed_union H0 Hlti).
    rewrite union_exist_Symm in H1.
    by rewrite <-Hju, H1, ltnn in Hltu.
Qed.

Lemma find_changed_changed_union: 
forall f i i' u v j,
find_rec f i > find_rec f i' ->
find_rec f j = find_rec f i ->
find_rec (union_exist f i i') u > find_rec (union_exist f i i') v ->
find_rec f i' = find_rec (union_exist f i i') u ->
find_rec (union_exist (union_exist f i i') u v) j = find_rec f v.
Proof.
  move=> f i i' u v j Hlti Hji Hltu Hju.
  have: find_rec f v < find_rec f i by apply (lt_union Hlti Hltu Hju).
  move=>/ltn_eqF /eqP /eqP Hvi;
  rewrite (union_exist_Symm i i') (union_exist_Symm u v) find_changed_union. 
  + by rewrite find_unchanged_union . 
  + by rewrite (find_changed_union Hji Hlti) Hju (union_exist_Symm i' i).
  + by rewrite (union_exist_Symm i' i).
Qed.

Lemma find_eq_union : forall f i i' u v,
find_rec f i = find_rec f i' ->
find_rec f u < find_rec f v ->
find_rec (union_exist f u v) i == find_rec (union_exist f u v) i'.
Proof.
  move=> f i i' u v Heqi Hltu.
  case Heqv: (find_rec f i == find_rec f v); move/eqP in Heqv.
  - rewrite (find_changed_union Heqv Hltu).
    rewrite Heqi in Heqv.
    by rewrite find_changed_union .
  - rewrite contra.Internals.eqType_neqP in Heqv. 
    rewrite (find_unchanged_union Heqv Hltu).
    rewrite Heqi in Heqv.
    rewrite (find_unchanged_union Heqv Hltu).
    by move/eqP in Heqi.
Qed.

Lemma union_exist_id2 : forall f i i' u v,
find_rec f i == find_rec f i' ->
union_exist (union_exist f u v) i i' = union_exist f u v.
Proof.
  move=> f i i' u v /eqP Heqi.
  apply boolp.eq_exist.
  rewrite {1}/union_func /union_exist.
  case Hequ: (find_rec f u == find_rec f v).
  - move: (union_correct f u v).
  rewrite /union_func Hequ => Hf.
  by rewrite <- exist_surjective, Heqi, eq_refl.
  case Hltu: (find_rec f u < find_rec f v)=> /=.
  -  by rewrite (find_eq_union Heqi Hltu).
  - have Hltu' := lt_case Hltu Hequ.
  fold (union_exist f u v).
  by rewrite (union_exist_Symm u v) (find_eq_union Heqi Hltu').
Qed.

Lemma find_eq_unionC: forall i i' u v f,
find_rec f u = find_rec f i->
find_rec f v = find_rec f i'->
(union_exist f u v) = (union_exist f i i').
Proof.
  by move=> i i' u v f Heq Heq';
  apply boolp.eq_exist;
  rewrite /union_func Heq Heq'.
Qed.


Lemma union_case : 
forall f i i' u v,
find_rec f i' < find_rec f i ->
find_rec f v <= find_rec f u ->
(find_rec (union_exist f i i') u  = find_rec (union_exist f i i') v) -> 
find_rec f u = find_rec f v \/ (find_rec f u = find_rec f i /\ find_rec f v = find_rec f i').
Proof.
  move=> f i i' u v Hlti Hltu Heq.
  move/eqP in Heq.
  case Hequv: (find_rec f u == find_rec f v); move/eqP in Hequv.
  - by rewrite Hequv; apply or_introl.
  - apply or_intror.
  move/eqP in Heq.
    case H: (find_rec f u == find_rec f i); move/eqP in H.
    +have Hv : find_rec f v != find_rec f i
        by rewrite H in Hequv;move/nesym /eqP in Hequv.
      by rewrite union_exist_Symm (find_changed_union H Hlti) (find_unchanged_union Hv Hlti) in Heq. 
    + move/eqP in H. 
    rewrite union_exist_Symm (find_unchanged_union H Hlti) in Heq. 
    case Hvi : (find_rec f v == find_rec f i); move/eqP in Hvi.
    * rewrite (find_changed_union Hvi Hlti) in Heq.
      rewrite Heq Hvi in Hltu. 
      by apply (leq_ltn_trans Hltu) in Hlti; rewrite ltnn in Hlti.
    * by move/eqP in Hvi;rewrite (find_unchanged_union Hvi Hlti) in Heq.
Qed.

Lemma find_union_eq : forall f i i' u v,
find_rec f i' < find_rec f i ->
find_rec f u = find_rec f v ->
find_rec (union_exist f i i') u = find_rec (union_exist f i i') v.
Proof.
  move=>f i i' u v  Hlti Hfind.
  case Heq: (find_rec f u == find_rec f i);move/eqP in Heq.
  - rewrite union_exist_Symm (find_changed_union Heq Hlti).
    rewrite Hfind in Heq.
    by rewrite (find_changed_union Heq Hlti).
  - move/eqP in Heq.
    rewrite union_exist_Symm (find_unchanged_union Heq Hlti).
    rewrite Hfind in Heq.
    by rewrite (find_unchanged_union Heq Hlti).
Qed.

Lemma inf_after_union: forall i i' u v f,
find_rec f i < find_rec f i' ->
find_rec (union_exist f i i') u < find_rec (union_exist f i i') v ->
find_rec f u < find_rec f v \/ 
(find_rec f u > find_rec f v /\ find_rec f u = find_rec f i' /\find_rec f v > find_rec f i).
Proof.
  move=> i i' u v f Hlti Hltunion.
  case Hlt: (find_rec f u < find_rec f v).
  by apply or_introl.
  apply or_intror.
  have Huv : ((find_rec f u == find_rec f v) = false).
    apply /eqP => Hcontr. apply (find_union_eq Hlti) in Hcontr.
    move /ltn_eqF /eqP in Hltunion. 
    by rewrite union_exist_Symm in Hltunion.
  have Hlt' := lt_case Hlt Huv.
  have  Hui': find_rec f u = find_rec f i'.
  apply /eqP /contraT => Hcontr. 
    rewrite (find_unchanged_union Hcontr Hlti) in Hltunion.
    move/ltnW in Hltunion. have H' := (leq_trans Hltunion (union_dec f i' i v)).
    move: H'. rewrite leq_eqVlt. rewrite Hlt Huv // .
  have Hvi' : find_rec f v != find_rec f i'. 
    by rewrite -Hui'; apply /negPf /ltn_eqF.
  by rewrite (find_changed_union Hui' Hlti) (find_unchanged_union Hvi' Hlti ) in Hltunion. (* case analysis*)
Qed.

Lemma union_lt_exchange : forall f i i' u v,
find_rec f i < find_rec f i' ->
find_rec f v < find_rec f u ->
find_rec f i' != find_rec f u \/ find_rec f i < find_rec f v ->
find_rec (union_exist f u v) i < find_rec (union_exist f u v) i'.
Proof.
  move=> f i i' u v Hlti Hltuf H.
  case: H => H'.
  - rewrite union_exist_Symm (find_unchanged_union H' Hltuf).
    apply: leq_ltn_trans.
    + apply union_dec.
    + by [].
  - have Hlt := (ltn_trans H' Hltuf).
  move /ltn_eqF /eqP /eqP in Hlt.
  rewrite union_exist_Symm (find_unchanged_union Hlt Hltuf).
  case Hequi': (find_rec f i' == find_rec f u);move/eqP in Hequi'.
  - by rewrite (find_changed_union ).
  - by move/eqP in Hequi'; rewrite find_unchanged_union.
Qed.

Lemma union_lt_exchange2 : forall f i i' u v,
find_rec f i < find_rec f i' ->
find_rec f v < find_rec f u ->
find_rec f i' = find_rec f u ->
find_rec f i > find_rec f v -> 
find_rec (union_exist f u v) i > find_rec (union_exist f u v) i'.
Proof. 
  move=> f i i' u v Hlti Hltuf Heqi'u Hlt.
  rewrite union_exist_Symm (find_changed_union Heqi'u Hltuf).
  have Hdiff : find_rec f i != find_rec f u.
  by rewrite -Heqi'u; apply /negPf /ltn_eqF.
  by rewrite find_unchanged_union.
Qed.

Lemma case_find_union : forall f i i' u ,
find_rec f i < find_rec f i' ->
find_rec f i = find_rec (union_exist f i' i) u ->
find_rec f i = find_rec f u \/ find_rec f i' = find_rec f u.
Proof.
  move=> f i i' u Hlti Hfind.
  case Heq : (find_rec f i == find_rec f u); move/eqP in Heq.
  - by apply or_introl.
  - apply or_intror. 
  case Heq' : (find_rec f u == find_rec f i'); move/eqP in Heq'.
  + by [].
  + by move/eqP in Heq'; rewrite union_exist_Symm (find_unchanged_union Heq' Hlti) in Hfind.
Qed.

Let UnionC_aux : forall f i i' u v j,
find_rec f i < find_rec f i' ->
find_rec (union_exist f i' i) v < find_rec (union_exist f i' i) u ->
find_rec (union_exist (union_exist f i i') u v) j = find_rec (union_exist (union_exist f u v) i i') j.
Proof.
  move=> f i i' u v j Hlti Hltu.
  rewrite union_exist_Symm in Hltu.
  have Hltuf := inf_after_union Hlti Hltu.
  have Heqi := ltn_eqF Hlti.
  have Hequ := ltn_eqF Hltu.
  rewrite  (union_exist_Symm i i') (union_exist_Symm i i').
  case Hij: (find_rec f j == find_rec f i'); move/eqP in Hij.
  case Huj: (find_rec f i == find_rec (union_exist f i i') u); move/eqP in Huj.
    - rewrite (union_exist_Symm i i') in Hltu, Huj;
      rewrite (find_changed_changed_union Hlti Hij Hltu Huj).
      have H: find_rec f i = find_rec f u \/ find_rec f i' = find_rec f u by apply (case_find_union Hlti Huj).
      case H => Hui.
      +have Hltuf' : find_rec f v < find_rec f u.
        rewrite Hui ltnn/= in Hltuf. 
        case Hltuf. 
          by [].
          by move=> H'; case: H' =>[H0 [H1 H2]].
      have Hju: find_rec f j <> find_rec f u 
        by rewrite <- Hui, Hij; apply /nesym /eqP /negPf /ltn_eqF.
      have Hdiff: find_rec f i' != find_rec f u \/ find_rec f i < find_rec f v
        by apply or_introl;rewrite -Hui; move /ltn_eqF /eqP /nesym /eqP in Hlti.
      have Hlti' := union_lt_exchange Hlti Hltuf' Hdiff.
      by rewrite (find_unchanged_changed_union_eq Hltuf' Hju Hlti Hij Hui Hlti').
      + have Hltuf' : find_rec f v < find_rec f u.
        rewrite Hui in Hltuf.
        case: Hltuf => Hltuf'.
        by [].
        by rewrite union_exist_Symm (find_union_eq Hlti (Hltuf'.2.1)) eq_refl in Hequ.
      have Hju: find_rec f j = find_rec f u by rewrite <- Hui.
        have Hdiff : find_rec f i <> find_rec f u by move=> Hcontradiction; rewrite <- Hcontradiction in Hui;rewrite Hui eq_refl in Heqi.
        have Hltvi: find_rec f v < find_rec f i.
          rewrite <-Huj in Hltu.
          have Hdiffv: find_rec f v <> find_rec f i'.
          by move=> Hcontr; move/ltn_eqF in Hltuf'; rewrite <-Hui,Hcontr, eq_refl in Hltuf'.
          by move/eqP in Hdiffv; rewrite union_exist_Symm (find_unchanged_union  Hdiffv Hlti) in Hltu.
        have Hji' : find_rec f v <> find_rec (union_exist f u v) i.
          by move/eqP in Hdiff;
          rewrite union_exist_Symm (find_unchanged_union Hdiff Hltuf')=> Hcontr;
          apply ltn_eqF in Hltvi; rewrite Hcontr eq_refl in Hltvi. 
        have Hlti':= (union_lt_exchange2 Hlti Hltuf' Hui Hltvi).
        by rewrite (union_exist_Symm i' i) (find_changed_unchanged_union Hltuf' Hju Hlti' Hji').
      + rewrite union_exist_Symm in Huj, Hltu.
        rewrite (find_changed_unchanged_union Hlti Hij Hltu Huj).
        have Hju': find_rec f j <> find_rec f u
          by move=>Hcontr; rewrite Hcontr in Hij;rewrite union_exist_Symm (find_changed_union Hij Hlti) in Huj.
        have Hdiffu : find_rec f i <> find_rec f u
          by move=>Hcontr;rewrite Hij in Hju'; move/nesym /eqP in Hju'; rewrite union_exist_Symm (find_unchanged_union Hju' Hlti) in Huj.
        move/eqP in Hdiffu.
        case Hltuf => Hltuf'.
        * have Hiu: find_rec (union_exist f u v) i <> find_rec f u
              by rewrite union_exist_Symm (find_unchanged_union Hdiffu Hltuf'); apply /eqP.
          have Hjud: find_rec f i' != find_rec f u \/ find_rec f i < find_rec f v 
            by apply or_introl; move/eqP in Hju'; rewrite Hij in Hju'. 
          have Hji': find_rec f j = find_rec (union_exist f u v) i'
            by rewrite Hij in Hju'; move/eqP in Hju'; rewrite union_exist_Symm (find_unchanged_union Hju' Hltuf').
          have Hlti' := union_lt_exchange Hlti Hltuf' Hjud.
          rewrite (find_unchanged_changed_union_neq Hltuf' Hju' Hlti' Hji' Hiu).
          by move/eqP in Hiu; rewrite union_exist_Symm (find_unchanged_union Hdiffu Hltuf').
        * case: Hltuf' => Hltuf1 Hltuf''; case: Hltuf'' => Hltuf2 Hltuf3.
        have Hexch : find_rec f i' != find_rec f v \/ find_rec f i < find_rec f u by apply or_intror.
        have Hlti' := union_lt_exchange Hlti Hltuf1 Hexch.
        rewrite -Hltuf2 in Hij.
        have Hui: find_rec f u = find_rec (union_exist f v u) i'
          by symmetry in Hltuf2;rewrite union_exist_Symm (find_changed_union Hltuf2 Hltuf1).
        by rewrite (union_exist_Symm u v) (find_changed_changed_union Hltuf1 Hij Hlti' Hui).
      +  rewrite union_exist_Symm in Hltu.
        case Hju: (find_rec f j == find_rec (union_exist f i' i) u);move/eqP in Hju.
        case Hvi: (find_rec f v == find_rec f i'); move/eqP in Hvi.
        * case Hltuf=>Hltuf'.
          -- have Hdiff : find_rec f u <> find_rec f i' 
            by move=>Hcontr; apply ltn_eqF in Hltuf'; rewrite Hcontr Hvi eq_refl in Hltuf'.
          have Hju': find_rec f j = find_rec f u 
            by move/eqP in Hdiff; rewrite union_exist_Symm (find_unchanged_union Hdiff Hlti) in Hju.
          rewrite (find_unchanged_changed_union_eq Hlti Hij Hltuf' Hju' Hvi Hltu).
          have Hvi': find_rec f v = find_rec (union_exist f u v) i' 
          by rewrite Hju' in Hij;move /nesym /eqP in Hij;
          rewrite union_exist_Symm (find_unchanged_union Hij Hltuf').
          move/nesym /eqP in Hdiff;
          have Hdiff': find_rec f i' != find_rec f u \/ find_rec f i < find_rec f v 
            by apply or_introl.
          have Hlti' := union_lt_exchange Hlti Hltuf' Hdiff'.
          by rewrite (find_changed_changed_union Hltuf' Hju' Hlti' Hvi'). 
        -- case: Hltuf' => [Hltuf1 [Hltuf2 Hltuf3]]. 
          have Hui: find_rec f u != find_rec f i'.
            by rewrite -Hltuf2; move/ltn_eqF /eqP /eqP in Hltuf1.
          have Hexch : find_rec f i' != find_rec f v \/ find_rec f i < find_rec f u
            by apply or_intror.
          have Hlti' := union_lt_exchange Hlti Hltuf1 Hexch.
          have Hvi' : find_rec (union_exist f i' i) v <> find_rec f i'.
            rewrite union_exist_Symm (find_changed_union Hltuf2 Hlti).
            by move /ltn_eqF /eqP in Hlti.
          rewrite (find_unchanged_changed_union_neq Hlti Hij Hltu Hju Hvi').
          rewrite union_exist_Symm (find_unchanged_union Hui Hlti) in Hju.
          rewrite -Hltuf2 in Hij.
          have Hji' : find_rec f j = find_rec (union_exist f v u) i'
            by symmetry in Hltuf2; rewrite  union_exist_Symm (find_changed_union Hltuf2 Hltuf1).
          have Hiv : find_rec (union_exist f v u) i <> find_rec f v
            by rewrite -Hvi in Hlti; move /ltn_eqF /eqP /eqP in Hlti;
            rewrite union_exist_Symm (find_unchanged_union Hlti Hltuf1); apply /eqP.
          rewrite (union_exist_Symm u v) (find_unchanged_changed_union_neq Hltuf1 Hij Hlti' Hji' Hiv).
          have Hvidiff: find_rec f i != find_rec f v
            by rewrite Hltuf2; move/ltn_eqF /eqP /eqP in Hlti.
          by rewrite union_exist_Symm (find_changed_union Hltuf2 Hlti)
            union_exist_Symm ( find_unchanged_union Hvidiff Hltuf1).
        * have Hltuf' : find_rec f v < find_rec f u.
          case : Hltuf=>Hltuf'.
            by [].
            by exfalso; apply Hvi; exact Hltuf'.2.1.
          have Hdiff: find_rec (union_exist f i' i) v <> find_rec f i'
            by move/eqP in Hvi; rewrite union_exist_Symm (find_unchanged_union Hvi Hlti); apply /eqP.
        have H : find_rec f j = find_rec f u \/ find_rec f u = find_rec f i' /\ find_rec f j = find_rec f i.
          case Heq : (find_rec f u == find_rec f i');move/eqP in Heq.
          - by apply or_intror; rewrite union_exist_Symm (find_changed_union Heq Hlti) in Hju; split.
          - by apply or_introl;move/eqP in Heq; rewrite union_exist_Symm (find_unchanged_union Heq Hlti) in Hju.
          case: H => H'.
          -- move/eqP in Hvi. rewrite (find_unchanged_changed_union_neq Hlti Hij Hltu Hju Hdiff).
          rewrite H' in Hij; move/nesym /eqP in Hij.
          have Hdiff0: find_rec f i' != find_rec f u \/ find_rec f i < find_rec f v by apply or_introl. 
          have Hlti' := union_lt_exchange Hlti Hltuf' Hdiff0. 
          have Hvi' : find_rec f v <> find_rec (union_exist f u v) i'.
            by rewrite union_exist_Symm (find_unchanged_union Hij Hltuf'); apply /eqP.
          by rewrite (find_changed_unchanged_union Hltuf' H' Hlti' Hvi')
          union_exist_Symm (find_unchanged_union Hvi Hlti).
          -- case: H' => Hui' Hji.
            move/eqP in Hvi.
            have Hlt : find_rec f v < find_rec f i by
            rewrite union_exist_Symm (find_changed_union Hui' Hlti) 
            (find_unchanged_union Hvi Hlti) in Hltu.
          symmetry in Hui';
          have Hlti' := union_lt_exchange2 Hlti Hltuf' Hui' Hlt.
          have Hdiff': find_rec (union_exist f i' i) v <> find_rec f i'
            by rewrite union_exist_Symm (find_unchanged_union Hvi Hlti); apply /eqP.
          rewrite (find_unchanged_changed_union_neq Hlti Hij Hltu Hju Hdiff').
          rewrite Hui' in Hij.
          have Hji' : find_rec f j = find_rec (union_exist f u v) i.
            by rewrite Hji in Hij; move/eqP in Hij; 
            rewrite union_exist_Symm (find_unchanged_union Hij Hltuf').
          have Hi'u : find_rec (union_exist f u v) i' <> find_rec f u
            by rewrite union_exist_Symm (find_changed_union Hui' Hltuf'); move /ltn_eqF /eqP in Hltuf'.
          by rewrite !(union_exist_Symm i' i) (find_unchanged_changed_union_neq Hltuf' Hij Hlti' Hji' Hi'u)
          (find_unchanged_union Hvi Hlti) union_exist_Symm (find_changed_union Hui' Hltuf').
        *rewrite (find_unchanged_unchanged_union Hlti Hij Hltu Hju).
          case H: (find_rec f u == find_rec f i'); move/eqP in H.
          -- have Hltuf' : find_rec f v < find_rec f u.
              rewrite -H in Hltuf.
              case: Hltuf => Hltuf'.
              by [].
              by rewrite union_exist_Symm (find_union_eq Hlti (Hltuf'.2.1)) eq_refl in Hequ.
            rewrite union_exist_Symm (find_changed_union H Hlti) in Hju.
            have Hvi : find_rec f v <> find_rec f i'
              by move=>Hcontr;rewrite union_exist_Symm (find_changed_union Hcontr Hlti) (find_changed_union H Hlti) ltnn in Hltu.
            move/eqP in Hvi;
            have Hlt : find_rec f v < find_rec f i
              by rewrite union_exist_Symm (find_changed_union H Hlti) (find_unchanged_union Hvi Hlti) in Hltu.
            symmetry in H;
            have Hlti' := union_lt_exchange2 Hlti Hltuf' H Hlt.
            rewrite H in Hij.
            have Hui : find_rec f i <> find_rec f u
              by move=> Hcontr; rewrite Hcontr H eq_refl in Heqi.
            have Hji' : find_rec f j <> find_rec (union_exist f u v) i .
            by move/eqP in Hui; rewrite union_exist_Symm (find_unchanged_union Hui Hltuf').
            by rewrite (union_exist_Symm i' i)  (find_unchanged_unchanged_union Hltuf' Hij Hlti' Hji').
          -- case: Hltuf => Hltuf'.
            ++have Hdiff : find_rec f i' != find_rec f u \/ find_rec f i < find_rec f v
              by move/nesym /eqP in H; apply or_introl.
            have Hlti' := union_lt_exchange Hlti Hltuf' Hdiff.
            have Hji' : find_rec f j <> find_rec (union_exist f u v) i'
              by move/nesym /eqP in H; rewrite union_exist_Symm (find_unchanged_union H Hltuf').
            have Hju' :  find_rec f j <> find_rec f u
              by move/eqP in H; rewrite union_exist_Symm (find_unchanged_union H Hlti) in Hju.
            by rewrite (find_unchanged_unchanged_union Hltuf' Hju' Hlti' Hji').
            ++ case: Hltuf' => [Hltuf1 [Hltuf2 Hltuf3]].
            rewrite -Hltuf2 in Hij.
            have Hdiff : find_rec f i' != find_rec f v \/ find_rec f i < find_rec f u 
              by apply or_intror.
            have Hlti' := union_lt_exchange Hlti Hltuf1 Hdiff.
            have Hji' : find_rec f j <> find_rec (union_exist f v u) i'.
            by symmetry in Hltuf2;rewrite union_exist_Symm (find_changed_union Hltuf2 Hltuf1);
              move/eqP in H; rewrite union_exist_Symm (find_unchanged_union H Hlti) in Hju.
            by rewrite (union_exist_Symm u v) (find_unchanged_unchanged_union Hltuf1 Hij Hlti' Hji').
Qed.

Lemma unionC_aux2 : forall j i i' u v f,
find_rec f i < find_rec f i' ->
find_rec (union_exist (union_exist f i i') u v) j =
find_rec (union_exist (union_exist f u v) i i') j.
Proof.
  move=> j i i' u v f Hlti.
  wlog : u v/find_rec f u <= find_rec f v.
  -move=> Hwlog.
  case Hleu: (find_rec f u <= find_rec f v).
    + by apply Hwlog.
    + have Hlev: find_rec f v <= find_rec f u.
        by move: (leqVgt (find_rec f u) (find_rec f v));rewrite Hleu /=; apply ltnW.
      rewrite !(union_exist_Symm u v).
      by apply Hwlog.
  -move=> Hleu.
    case Hequ: (find_rec (union_exist f i i') u == find_rec (union_exist f i i') v).
    + rewrite eq_sym union_exist_Symm in Hequ; move /eqP in Hequ.
    have H := union_case Hlti Hleu Hequ.
    case H.
    *  by move=>Hequ';move/eqP in Hequ'; rewrite !(union_exist_Symm u v) (union_exist_id Hequ') (union_exist_id2 i i' Hequ').
    *  move=>Hequivi'; case: Hequivi' => Hequi Heqvi'.
        have Heq := find_union_eq Hlti Heqvi'.
        have Heq' := find_union_eq Hlti Hequi.
        by rewrite !(union_exist_Symm u v) (find_eq_unionC  Hequi Heqvi') 
          (union_exist_Symm v u) (union_exist_Symm i i') (find_eq_unionC  Heq Heq').
    case Hltu: (find_rec (union_exist f i i') v < find_rec (union_exist f i i') u).
    +by rewrite union_exist_Symm in Hltu; apply UnionC_aux . 
    + rewrite eq_sym in Hequ. 
    have Hltu' := lt_case Hltu Hequ. 
    rewrite !(union_exist_Symm i i') in Hltu'.
    rewrite !(union_exist_Symm u v).
    by apply UnionC_aux . 
Qed.

Let unionC i i' u v: union i i' >> union u v ≈ union u v >> union i i'.
Proof.
  do 2 (split; try easy).
  rewrite /equiv /=; apply boolp.funext => j/=.
  case Heqi: (find_rec f i == find_rec f i').
  - by  rewrite (union_exist_id Heqi) (union_exist_id2 u v Heqi).
  case Hlti: (find_rec f i < find_rec f i').
  -  apply (unionC_aux2 j u v Hlti).
  - have Hlti' :=  lt_case Hlti Heqi.
    rewrite !(union_exist_Symm i i').
    apply (unionC_aux2 j u v Hlti').
Qed.

Let find_lookup A i (m : M A): (find i>> m) ≈ m.
Proof.
  apply eq_is_bisim. rewrite /bind.
  case m=> m' Hm.
  apply boolp.eq_exist, boolp.funext=>f.
  apply boolp.funext=>g.
  by rewrite /find /find_rec /=.
Qed.


HB.instance Definition _ := isMonadUnion.Build
  S acto  
  findfind 
  unionfind 
  findunion 
  findunionfind
  union_id 
  findC 
  unionSymm
  unionC
  find_lookup.

End modelunion.
End ModelUnion.
HB.export ModelUnion.


Module ModelUnionFail.
Section modelunionfail.

Variable S : UU0.
Definition acto := MX unit (ModelUnion.acto S).
Local Notation M := acto.
Local Notation I := nat.

HB.instance Definition _ := MonadExcept.on M.

Let find i := liftX unit (ModelUnion.find S i).
Let union i j := liftX unit (ModelUnion.union S i j).

Definition Bis A (P Q : M A) := ModelUnion.Bis P Q.


Lemma refl A (d : M A) : d ≈ d. 
Proof. exact: refl. Qed.

Lemma sym A (d1 d2 : M A) : d1 ≈ d2 -> d2 ≈ d1.
Proof. exact: sym. Qed.

Lemma trans A (d1 d2 d3 : M A) : d1 ≈ d2 -> d2 ≈ d3 -> d1 ≈ d3.
Proof. exact: trans. Qed.

Lemma bindl A B (t : A -> M B) (d1 d2 : M A) : d1 ≈ d2 -> (d1 >>= t) ≈ (d2 >>= t).
Proof. exact: bindl. Qed.

Lemma bindr A B (f g : A -> M B) d :
  (forall a, f a ≈ g a) -> (d >>= f) ≈ (d >>= g).
Proof. by move=> rH; apply: bindfeqv; case. Qed.

HB.instance Definition _ := @hasPreorder.Build M Bis
  (@refl) (@trans) (@bindl) (@bindr).

HB.instance Definition _ := @hasEquivalence.Build M (@sym).


Lemma liftequiv A (P Q: ModelUnion.acto S A ) : 
  P ≈ Q -> liftX unit P ≈ liftX unit Q.
Proof. by move=> Hequiv; apply: bindmeqv. Qed.

Let findfind (A : UU0) i (k : I -> I -> M A):
    eqvM (find i >>= fun r => find i >>= k r)
          (find i >>= fun r => k r r).
Proof. exact: (@findfind S (ModelUnion.acto S)). Qed.
  

Let unionfind i j: eqvM (union i j >> find i) (union i j >> find j).
Proof.  
  rewrite /union /find -monadMbind -monadMbind /=.
  by apply: liftequiv;  rewrite (@unionfind S (ModelUnion.acto S)).
Qed.

Let  findunion i j: eqvM (find j >>= union i) (union i j).
Proof. 
  rewrite /union /find -monadMbind /=.
  by apply liftequiv;  rewrite (@findunion S (ModelUnion.acto S)).
Qed.

Lemma lift_fun : forall v i j,
 liftX unit (ModelUnion.union S i j) >> liftX unit (ModelUnion.find S v)  =
 liftX unit (ModelUnion.union S i j >>ModelUnion.find S v).
Abort.

Let  findunionfind  i j u: eqvM (find u >>= fun v => union i j >> find v) (union i j >> find u).
Proof.
  rewrite /union /find -monadMbind /=.
  under eq_bind do rewrite -(monadMbind) /=.
  rewrite -(monadMbind) /=.
  apply: liftequiv.
  exact: (@findunionfind S (ModelUnion.acto S)).
Qed.

Let ret A (a:A) := liftX unit (Ret a : ModelUnion.acto S A).

Let union_id i: eqvM (union i i) (skip : M unit).
Proof.
  rewrite /union /skip.
  rewrite liftequiv; last exact: (@union_id S (ModelUnion.acto S)).
  by [].
Qed.

Let findC (A : UU0) i j (k : I -> I -> M A):
    eqvM  (find i >>= fun u => find j >>= k u)
          (find j >>= fun v => find i >>= k ^~ v).
Proof. exact: (@findC S (ModelUnion.acto S)). Qed.


Let unionSymm i j: eqvM (union i j) (union j i).
Proof. rewrite /union; apply liftequiv; exact: (@unionSymm S (ModelUnion.acto S)). Qed.

Let unionC i j u v: eqvM (union i j >> union u v) (union u v >> union i j).
Proof. rewrite /union -!monadMbind /=; apply liftequiv; exact: (@unionC S (ModelUnion.acto S)). Qed.

Let find_lookup A i (m : M A): (find i>> m) ≈ m.
Proof. exact: (@find_lookup S (ModelUnion.acto S)). Qed.
  
HB.instance Definition _ := isMonadUnion.Build
  S acto  
  findfind 
  unionfind 
  findunion 
  findunionfind
  union_id 
  findC 
  unionSymm
  unionC
  find_lookup.


Let neqfind a b :=  (find a >>= fun a' => find b >>= fun b':I =>  @guard M (a' != b')).

Let neqfindE : forall a b, neqfind a b =
    (find a >>= fun a' => find b >>= fun b':I =>  @guard M (a' != b')).
Proof. by []. Qed.

Notation lift_correct S i :=  (bind_correct (ModelUnion.find S i) (fun x : I => exist (is_eqMonad (A:=unit + I)) (fun f : forestType => [eta pair (inr x, f)]) (ret_correct (inr x)))).

Lemma lift_find i: find i = exist (is_eqMonad (A:=unit + I))
(fun f : forestType => [eta pair (inr (find_rec f i), f)]) (lift_correct S i).
Proof.
  rewrite /find /liftX /bind /= /bindX /retX.
  rewrite /ModelUnion.bind /=.
  by apply boolp.eq_exist, boolp.funext => f /=;apply boolp.funext => g /=.
Qed.

Lemma bindfind a A (k : I -> M A) : (find a >>= fun a' => k a) = (find a >>= fun a' => k a).
Proof.
  rewrite /bind /= /bindX /bind /= /ModelUnion.bind.
  apply boolp.eq_exist, boolp.funext => f;apply boolp.funext => g /=.
Abort.

Lemma find_unchanged_union_eq f i j a:
  (find_rec f a != find_rec f i) ->
  (find_rec f a != find_rec f j)->
  (find_rec (union_exist f i j) a) = find_rec f a.
Proof.
  move=> Hi Hj.
  case Heq: (find_rec f i == find_rec f j).
  -  by rewrite union_exist_id.
  case Hlt : (find_rec f i < find_rec f j).
  - by rewrite find_unchanged_union.
  - have Hlt' := lt_case Hlt Heq.
    by rewrite union_exist_Symm find_unchanged_union.
Qed.

Let unionfind_neq A  i j a (k : I-> M A ): 
    eqvM (neqfind a i>>neqfind a j>> union i j>> find a >>= k)
        (neqfind a i>> neqfind a j>> find a >>= fun a'=> union i j>> k a').
Proof.
  apply eq_is_bisim.
  rewrite /neqfind.
  rewrite lift_find.
  rewrite /bind /= /bindX.
  rewrite /neqfind /bind /= /bindX /ModelUnion.bind.
  apply boolp.eq_exist, boolp.funext => f;apply boolp.funext => g /=.
  case Hi : (find_rec f a != find_rec f i) => /=.
  case Hj : (find_rec f a != find_rec f j) => /=.
  by rewrite find_unchanged_union_eq.
  by [].
  by [].
Qed.

HB.instance Definition _ := isMonadUnionFail.Build
  S acto  
  neqfindE
  unionfind_neq.

End modelunionfail.
End ModelUnionFail.


Module ModelPlusArray.
Section modelplusarray.
Local Open Scope classical_set_scope.
Variable (S : UU0) (I : eqType).
Implicit Types i j : I.
Definition acto (A : UU0) := (I -> S) -> SetMonad.acto (A * (I -> S))%type.
Local Notation M := acto.
Let ret : idfun ~~> M := fun A a => fun s => [set (a, s)].
Let bind := fun A B (m : M A) (f : A -> M B) => fun s => m s >>= uncurry f.
Let left_neutral : BindLaws.left_neutral bind ret.
Proof.
by move=> X Y x f; apply: boolp.funext => a1; rewrite /bind/= bindretf.
Qed.
Let right_neutral : BindLaws.right_neutral bind ret.
Proof.
move=> X/= m; rewrite /bind; apply: boolp.funext => a1.
rewrite /ret /uncurry/=; apply/seteqP; split.
  by move=> [x a2]/= [[x' a3]] ma1x'a3/= ->.
by move=> [x a2] ma1xa2/=; eexists; [exact: ma1xa2|].
Qed.
Let associative : BindLaws.associative bind.
Proof.
move=> X Y Z /= m f g; rewrite /bind; apply: boolp.funext => a.
by rewrite bindA; bind_ext => -[].
Qed.
HB.instance Definition _ :=
  isMonad_ret_bind.Build acto left_neutral right_neutral associative.
Let bindE A B (m : M A) (f : A -> M B) : m >>= f = bind m f.
Proof. by []. Qed.
Definition aget i : M S := fun s => Ret (ModelArray.aget i s).
Definition aput i a : M unit := fun s => Ret (ModelArray.aput i a s).
Let aputput i s s' : aput i s >> aput i s' = aput i s'.
Proof.
apply boolp.funext => a/=; rewrite bindE /bind set_bindE.
by rewrite bigcup_set1/= /aput /ModelArray.aput insert_insert.
Qed.
Let aputget i s (A : UU0) (k : S -> M A) :
  aput i s >> aget i >>= k = aput i s >> k s.
Proof.
apply boolp.funext => a/=; rewrite !bindE /bind set_bindE.
rewrite set_bindE/= bigcup_bigcup !bigcup_set1/= /aput /ModelArray.aput.
by rewrite bindretf/= insert_same.
Qed.
Let agetput i : aget i >>= aput i = skip.
Proof.
apply boolp.funext => a/=; rewrite bindE /bind set_bindE bigcup_set1/=.
by rewrite /aput /ModelArray.aput insert_same2.
Qed.
Let agetget i (A : UU0) (k : S -> S -> M A) :
  aget i >>= (fun s => aget i >>= k s) = aget i >>= fun s => k s s.
Proof.
apply boolp.funext => a/=; rewrite !bindE /bind !set_bindE/= bigcup_set1/=.
by rewrite /aget /ModelArray.aget/= !bindE/= /bind/= !set_bindE/= !bigcup_set1.
Qed.
Let agetC i j (A : UU0) (k : S -> S -> M A) :
  aget i >>= (fun u => aget j >>= (fun v => k u v)) =
  aget j >>= (fun v => aget i >>= (fun u => k u v)).
Proof.
apply boolp.funext => a/=.
rewrite !bindE /bind/= !set_bindE !bigcup_set1/= /aget /ModelArray.aget/=.
by rewrite !bindE /bind/= !set_bindE/= !bigcup_set1.
Qed.
Let aputC i j u v : (i != j) \/ (u = v) ->
  aput i u >> aput j v = aput j v >> aput i u.
Proof.
move=> [ij|->{u}].
  apply boolp.funext => a/=.
  rewrite !bindE /bind/= !set_bindE/= !bigcup_set1/=.
  by rewrite /aput /ModelArray.aput/= insertC.
apply boolp.funext => a/=.
rewrite !bindE /bind/= !set_bindE/= !bigcup_set1/=.
by rewrite /aput /ModelArray.aput/= insertC2.
Qed.
Let aputgetC i j u (A : UU0) (k : S -> M A) : i != j ->
  aput i u >> aget j >>= k = aget j >>= (fun v => aput i u >> k v).
Proof.
move=> ij.
apply boolp.funext => a/=.
rewrite !bindE /bind/= !set_bindE !bigcup_set1/= /aput /ModelArray.aput/=.
by rewrite bindE /bind/= set_bindE bigcup_set1/= {1}/insert (negbTE ij).
Qed.
HB.instance Definition _ := isMonadArray.Build
  S I acto aputput aputget agetput agetget agetC aputC aputgetC.
Let bindfailf : BindLaws.left_zero bind (fun A _ => @set_fail _).
Proof.
by move=> A B/= g; apply boolp.funext => a/=; rewrite /bind bindfailf.
Qed.
HB.instance Definition _ := isMonadFail.Build acto bindfailf.
Definition aalt := fun (T : UU0) (a b : M T) => fun x => a x [~] b x.
Let altA (T : UU0) : ssrfun.associative (@aalt T).
Proof. by move=> x y z; apply: boolp.funext => a; rewrite /aalt altA. Qed.
Let alt_bindDl : BindLaws.left_distributive bind (@aalt).
Proof.
move=> A B/= m1 m2 k; apply boolp.funext => a; rewrite /bind /aalt/=.
by rewrite alt_bindDl.
Qed.
HB.instance Definition _ := isMonadAlt.Build M altA alt_bindDl.
Let altfailm : @BindLaws.left_id _ (@fail [the failMonad of acto])
                                   (@alt [the altMonad of acto]).
Proof.
move=> A m; apply boolp.funext => a/=; apply boolp.funext => -[x a1]/=.
by rewrite /alt/= /aalt altfailm.
Qed.
Let altmfail : @BindLaws.right_id _ (@fail [the failMonad of acto])
                                    (@alt [the altMonad of acto]).
Proof.
move=> A m; apply boolp.funext => a/=; apply boolp.funext => -[x a1]/=.
by rewrite /alt/= /aalt altmfail.
Qed.
HB.instance Definition _ := isMonadNondet.Build M altfailm altmfail.
Let altmm (A : UU0) : idempotent_op (@alt [the altMonad of M] A).
Proof.
move=> m; apply boolp.funext => a/=; apply boolp.funext => -[x a1]/=.
by rewrite /alt/= /aalt altmm.
Qed.
Let altC (A : UU0) : commutative (@alt [the altMonad of M] A).
Proof.
move=> m1 m2; apply boolp.funext => a/=; apply boolp.funext => -[x a1]/=.
by rewrite /alt/= /aalt altC.
Qed.
HB.instance Definition _ := @isMonadAltCI.Build M altmm altC.
Let bindmfail : BindLaws.right_zero bind (@fail [the failMonad of M]).
Proof.
move=> A B /= m; apply boolp.funext => a; apply boolp.funext => -[x a1]/=.
by rewrite /bind/= set_bindE/= bigcup0// => -[].
Qed.
HB.instance Definition _ := isMonadFailR0.Build M bindmfail.
Let alt_bindDr : BindLaws.right_distributive bind (@alt [the altMonad of M]).
Proof.
move=> T1 T2 /= A k1 k2; apply boolp.funext => a; apply boolp.funext => -[x a1].
rewrite /bind/= !set_bindE; apply/boolp.propext; split.
  move=> -[[x1 a2] H1]/= H2.
  by rewrite /alt/= /aalt -alt_bindDr set_bindE; exists (x1, a2).
move=> -[]; rewrite !set_bindE => -[[x1 a2] H1] /= H2; exists (x1, a2) => //.
by left.
by right.
Qed.
HB.instance Definition _ := isMonadPrePlus.Build M alt_bindDr.

(*Lemma arrayMonad_fail A (f : forall (M : arrayMonad S I), M A)
  (M : plusArrayMonad S I) : f M <> fail :> M A.*)

(*Section arrayMonad_fail.
Variables (A : UU0) (f : forall (M : arrayMonad S I), M A).

Lemma arrayMonad_fail : f M <> fail :> M A.
Proof.
have := f (ModelArray.acto S I).
rewrite [X in X -> _](_ : _ = ((I -> S) -> A * (I -> S)))//=.
move=> fM FMail.*)

End modelplusarray.
End ModelPlusArray.
HB.export ModelPlusArray.

(* In the following trivial model, every computation is degenerate to
   (tt : unit), and especially, skip = fail holds.  This suggests an addition of
   another law to MonadPlusArray that distinguish the MonadArray operations
   from the MonadPlus ones.  Two ideas exist:
   1. use parametricity:
      _ : forall (T : UU0) (I : eqType) A (M : plusArrayMonad T I)
                 (m : forall (M : arrayMonad T I) , M A),
                 m M <> fail :> M A.
      this would need parametricity axioms for its validation in a model.
   2. use syntactic reflection:
      _ : forall (T : UU0) (I : eqType) A (M : plusArrayMonad T I) (m : M A),
          {S | evalArrayMonad S = m} -> m <> fail.
      here, S is an abstract syntax tree for a computation in MonadArray and
      evalArrayMonad is an evaluator that interprets S into a computation *)
Module TrivialPlusArray.
Section def.
Variable (S : UU0) (I : eqType).
Implicit Types i j : I.
Definition acto (A : UU0) := unit.
Local Notation M := acto.
Let ret : idfun ~~> M := fun A a => tt.
Let bind := fun A B (m : M A) (f : A -> M B) => tt : M B.
Let left_neutral : BindLaws.left_neutral bind ret.
Proof. by move=> ? ? x f; case: (f x). Qed.
Let right_neutral : BindLaws.right_neutral bind ret.
Proof. by move=> ? []. Qed.
Let associative : BindLaws.associative bind.
Proof. by []. Qed.
HB.instance Definition _ :=
  isMonad_ret_bind.Build acto left_neutral right_neutral associative.
Let bindE A B (m : M A) (f : A -> M B) : m >>= f = bind m f.
Proof. by []. Qed.
Definition aget i : M S := tt.
Definition aput (i : I) (a : S) : M unit := tt.
Let aputput i s s' : aput i s >> aput i s' = aput i s'. Proof. by []. Qed.
Let aputget i s (A : UU0) (k : S -> M A) :
  aput i s >> aget i >>= k = aput i s >> k s.
Proof. by []. Qed.
Let agetput i : aget i >>= aput i = skip. Proof. by []. Qed.
Let agetget i (A : UU0) (k : S -> S -> M A) :
  aget i >>= (fun s => aget i >>= k s) = aget i >>= fun s => k s s.
Proof. by []. Qed.
Let agetC i j (A : UU0) (k : S -> S -> M A) :
  aget i >>= (fun u => aget j >>= (fun v => k u v)) =
  aget j >>= (fun v => aget i >>= (fun u => k u v)).
Proof. by []. Qed.
Let aputC i j u v : (i != j) \/ (u = v) ->
  aput i u >> aput j v = aput j v >> aput i u.
Proof. by []. Qed.
Let aputgetC i j u (A : UU0) (k : S -> M A) : i != j ->
  aput i u >> aget j >>= k = aget j >>= (fun v => aput i u >> k v).
Proof. by []. Qed.
HB.instance Definition _ := isMonadArray.Build
  S I acto aputput aputget agetput agetget agetC aputC aputgetC.
Let fail A := tt : M A.
Let bindfailf : BindLaws.left_zero bind fail.
Proof. by []. Qed.
HB.instance Definition _ := isMonadFail.Build acto bindfailf.
Definition aalt := fun (T : UU0) (a b : M T) => tt.
Let altA (T : UU0) : ssrfun.associative (@aalt T). Proof. by []. Qed.
Let alt_bindDl : BindLaws.left_distributive bind (@aalt). Proof. by []. Qed.
HB.instance Definition _ := isMonadAlt.Build M altA alt_bindDl.
Let altfailm : @BindLaws.left_id M fail aalt. Proof. by []. Qed.
Let altmfail : @BindLaws.right_id M fail aalt. Proof. by []. Qed.
HB.instance Definition _ := isMonadNondet.Build M altfailm altmfail.
Let altmm (A : UU0) : idempotent_op (@aalt (M A)). Proof. by case. Qed.
Let altC (A : UU0) : commutative (@aalt (M A)). Proof. by []. Qed.
HB.instance Definition _ := @isMonadAltCI.Build M altmm altC.
Let bindmfail : BindLaws.right_zero bind fail. Proof. by []. Qed.
HB.instance Definition _ := isMonadFailR0.Build M bindmfail.
Let alt_bindDr : BindLaws.right_distributive bind aalt. Proof. by []. Qed.
HB.instance Definition _ := isMonadPrePlus.Build M alt_bindDr.
End def.
End TrivialPlusArray.

(* TODO?
(* result of a discussion with Maxime and Enrico on 2019-09-12 *)
(* Equality between monads from the hierarchy and their counterparts built    *)
(* using monad transformers and the identity monad:                           *)
(* - stateT_id_ModelState, exceptT_id_ModelExcept, contT_id_ModelCont         *)
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
*)

(*Section instantiations_with_the_identity_monad.

Lemma stateT_id_ModelState S :
  stateT S [the monad of idfun] = [the monad of StateMonad.acto S].
Proof.
rewrite /= /stateTmonadM /=.
have FG : MS_functor S ModelMonad.identity = ModelMonad.State.functor S.
  apply: functor_ext => /=; apply funext_dep => A; apply funext_dep => B.
  apply boolp.funext => f; apply boolp.funext => m; apply boolp.funext => s.
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
  apply: functor_ext => /=; apply funext_dep => A; apply funext_dep => B.
  apply boolp.funext => f; apply boolp.funext => m.
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
  apply: functor_ext => /=; apply funext_dep => A; apply funext_dep => B.
  by apply boolp.funext => f; apply boolp.funext => m.
apply (@monad_of_ret_bind_ext _ _ _ _ _ _ FG) => /=.
  apply/natural_ext => A a /=; exact: (@eq_rect_cont_ret A r _ (esym FG)).
set x := @bindC _ _; exact: (@eq_rect_bind_cont r x (esym FG)).
Qed.

End instantiations_with_the_identity_monad.*)

Section monad_transformer_calcul.

Let contTi T := MC T [the monad of idfun].

Definition break_if_none (m : monad) (break : _) (acc : nat) (x : option nat) : m nat :=
  if x is Some x then Ret (x + acc) else break acc.

Definition sum_until_none (xs : seq (option nat)) : contTi nat nat :=
  callcc (fun break : nat -> contTi nat nat => foldM (break_if_none break) 0 xs).

Goal sum_until_none [:: Some 2; Some 6; None; Some 4] = @^~ 8.
by cbv.
Abort.

Definition calcul : contTi nat nat :=
  (_ # (fun x => 8 + x))
  (callcc (fun k : _ -> contTi nat _ => (k 5) >>= (fun y => Ret (y + 4)))).

Goal calcul = @^~ 13.
by cbv.
Abort.

End monad_transformer_calcul.

Section examples_of_algebraic_lifting.

Section state_exceptT.
Let M S := [the monad of StateMonad.acto S].

Definition aLGet {Z S} :
    [the functor of StateOpsGet.acto S].-aoperation (exceptT Z (M S)) :=
  alifting (get_aop S) (Lift _ (M S)).

Definition aLPut {Z S} :
    [the functor of StateOpsPut.acto S].-operation (exceptT Z (M S)) :=
  alifting (put_aop S) (Lift _ (M S)).

Goal forall Z (S : UU0) X (k : S -> exceptT Z (M S) X), aLGet _ k = get_op _ k.
Proof. by move=> Z S X k; rewrite /aLGet aliftingE. Qed.

Goal forall Z S, aLGet _ Ret = Lift [the monadT of exceptT Z] (M S) _
                           (@get S [the stateMonad S of StateMonad.acto S]).
Proof. by move=> Z S; rewrite /aLGet aliftingE. Qed.

End state_exceptT.

Section continuation_stateT.
Variable (r S : UU0).
Let M : monad := [the monad of ContMonad.acto r].

Definition aLCallcc :
    [the functor of ContOpsAcallcc.acto r].-aoperation (stateT S M) :=
  alifting (callcc_aop r) (Lift _ M).

Goal forall A (f : (stateT S M A -> r) -> stateT S M A),
  aLCallcc _ f = (fun s k => f (fun m => uncurry m (s, k)) s k) :> stateT S M A.
Proof. by move=> A f; rewrite /aLCallcc aliftingE. Qed.

Definition usual_callccS (A B : UU0) (f : (A -> stateT S M B) -> stateT S M A) : stateT S M A :=
  fun s k => f (fun x _ _ => k (x, s)) s k.

Lemma callccS_E A B f : @aLCallcc _
    (fun k : stateT S M A -> r =>
       f (fun x => (fun (_ : S) (_ : B * S -> r) => k (Ret x)) : stateT S M B)) =
  usual_callccS f.
Proof. by rewrite /aLCallcc aliftingE. Qed.

End continuation_stateT.

End examples_of_algebraic_lifting.

Module ModelMonadStateRun.
Section modelmonadstaterun.
Variable S : UU0.
Let N : monad := option_monad.
Definition M : stateMonad S := [the stateMonad S of stateT S N].

Let runStateT : forall A : UU0, M A -> S -> N (A * S)%type := fun A : UU0 => id.
Let runStateTret : forall (A : UU0) (a : A) (s : S), @runStateT _ (Ret a) s = Ret (a, s).
Proof. by []. Qed.
Let runStateTbind : forall (A B : UU0) (m : M A) (f : A -> M B) (s : S),
  @runStateT _ (m >>= f) s = @runStateT _ m s >>= fun x => @runStateT _ (f x.1) x.2.
Proof.
move=> A M m f s /=.
rewrite /= /runStateT bindE /= /join_of_bind /bindS /=.
rewrite MS_mapE /actm !compE/=.
by case: (m s).
Qed.
Let runStateTget : forall s : S, runStateT get s = Ret (s, s) :> N _.
Proof. by []. Qed.
Let runStateTput : forall s' s : S, @runStateT _ (put s') s = Ret (tt, s').
Proof. by []. Qed.

HB.instance Definition _ :=
  isMonadStateRun.Build S N (MS S N)
  runStateTret
  runStateTbind
  runStateTget
  runStateTput.

End modelmonadstaterun.
End ModelMonadStateRun.
HB.export ModelMonadStateRun.

Module ModelMonadExceptStateRun.
Section modelmonadexceptstaterun.
Variable S : UU0.
Let N : exceptMonad := option_monad.
Definition M : stateRunMonad S N := [the stateRunMonad S N of MS S N].

Definition failure : forall A, MS S N A := fun A => liftS (@fail N A).

Let Bindfailf : BindLaws.left_zero (@bind [the monad of MS S N]) failure.
Proof. by []. Qed.

HB.instance Definition _ := @isMonadFail.Build (MS S N) failure Bindfailf.

Let Catch (A : UU0) := mapStateT2 (@catch N (A * S)%type).

Let Catchmfail : forall A, right_id (liftS (@fail N A)) (@Catch A).
Proof.
move=> A x; rewrite /Catch /mapStateT2; apply boolp.funext => s.
by rewrite catchmfail.
Qed.
Let Catchfailm : forall A, left_id (liftS (@fail N A)) (@Catch A).
Proof.
move=> A x; rewrite /Catch /mapStateT2; apply boolp.funext => s.
by rewrite catchfailm.
Qed.
Let CatchA : forall A, ssrfun.associative (@Catch A).
Proof.
move=> A; rewrite /Catch /mapStateT2 => a b c; apply boolp.funext => s.
by rewrite catchA.
Qed.
Let Catchret : forall A x, @left_zero (M A) (M A) (Ret x) (@Catch A).
Proof.
move=> A x y; rewrite /Catch /mapStateT2; apply boolp.funext => s.
by rewrite catchret.
Qed.

HB.instance Definition _ :=
  @isMonadExcept.Build (MS S N) Catch Catchmfail Catchfailm CatchA Catchret.

Let RunStateTfail (A : UU0) (s : S) :
  runStateT (@fail [the failMonad of (MS S N)] A) s = @fail N _.
Proof. by []. Qed.
Let RunStateTcatch (A : UU0) (s : S) (m1 m2 : _ A) :
  runStateT (Catch m1 m2) s = catch (runStateT m1 s) (runStateT m2 s).
Proof. by []. Qed.

HB.instance Definition _ := @isMonadExceptStateRun.Build S N (MS S N)
  RunStateTfail RunStateTcatch.

End modelmonadexceptstaterun.
End ModelMonadExceptStateRun.
