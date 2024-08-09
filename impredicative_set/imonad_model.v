From mathcomp Require Import all_ssreflect.
Require Import ipreamble.
From HB Require Import structures.
Require Import ihierarchy imonad_lib ifail_lib istate_lib itrace_lib.
Require Import imonad_transformer.
Require PropExtensionality.

(******************************************************************************)
(*                       Models for various monads                            *)
(*                                                                            *)
(* Sample models for monads in hierarchy.v (see also other *_model.v files).  *)
(* As for naming, we tend to use the identifier acto for the actions on       *)
(* objects and actm for the actions on morphisms.                             *)
(*                                                                            *)
(* Instances of monads (Modules):                                             *)
(* IdentityMonad      == identity monad idfun                                 *)
(* ListMonad          == list monad seq                                       *)
(* ExceptMonad        == exception monad E + A                                *)
(* option_monad       == alias for ExceptMonad.acto unit                      *)
(* OutputMonad        == output monad X * seq L                               *)
(* EnvironmentMonad   == environment monad E -> A                             *)
(* StateMonad         == state monad S -> A * S                               *)
(* ContMonad          == continuation monad (A -> r) -> r                     *)
(*                                                                            *)
(* Sigma-operations (with algebraicity proofs):                               *)
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
(*                                                                            *)
(* Models of interfaces:                                                      *)
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
(* Module ModelArray       == array monad                                     *)
(* Module ModelMonadStateRun       == stateRunMonad for MS                    *)
(* Module ModelMonadExceptStateRun == exceptStateRunMonad                     *)
(*                                                                            *)
(* references:                                                                *)
(* - Wadler, P. Monads and composable continuations. LISP and Symbolic        *)
(*   Computation 7, 39–55 (1994)                                              *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.

(* TODO: move *)
Section assoc.
Variables (I : eqType) (S : UU0).
Definition insert i s (a : I -> S) j := if i == j then s else a j.
Lemma insert_insert i s' s a :
  insert i s' (insert i s a) = insert i s' a.
Proof.
by apply funext => j; rewrite /insert; case: ifPn => // /negbTE ->.
Qed.
Lemma insert_same i a s : insert i s a i = s.
Proof. by rewrite /insert eqxx. Qed.
Lemma insert_same2 i a : insert i (a i) a = a.
Proof.
by apply funext => j; rewrite /insert; case: ifPn => // /eqP ->.
Qed.
Lemma insertC j i v u a : i != j ->
  insert j v (insert i u a) = insert i u (insert j v a).
Proof.
move=> h; apply funext => k; rewrite /insert; case: ifPn => // /eqP <-{k}.
by rewrite (negbTE h).
Qed.
Lemma insertC2 j i v a : insert j v (insert i v a) = insert i v (insert j v a).
Proof.
apply funext => k; rewrite /insert; case: ifPn => // /eqP <-{k}.
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
Let acto := (@idfun UU0).
HB.instance Definition _ := isMonad_ret_bind.Build
  acto left_neutral right_neutral associative.
End identitymonad.
End IdentityMonad.
HB.export IdentityMonad.

Module ListMonad.
Section listmonad.
Definition acto := fun A : UU0 => seq A.
Local Notation M := acto.
Let ret : idfun ~~> M := fun (A : UU0) x => (@cons A) x [::].
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

Module EnvironmentMonad.
Section environment.
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
End environment.
End EnvironmentMonad.
HB.export EnvironmentMonad.

Lemma environment_bindE (E A B : UU0) (M := EnvironmentMonad.acto E)
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
Proof. by move=> A B a f; apply funext. Qed.
Let right_neutral : BindLaws.right_neutral bind ret.
Proof.
by move=> A f; apply funext => s; rewrite /bind /=; case: (f s).
Qed.
Let associative : BindLaws.associative bind.
Proof.
move=> A B C a b c; rewrite /bind compA; congr (_ \o _).
by apply funext => -[].
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
Proof. by move=> A B a f; apply funext => Br. Qed.
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
Proof. by move=> A; apply funext => -[]. Qed.
Let func_comp : FunctorLaws.comp actm.
Proof. by move=> A B C f g; apply funext => -[]. Qed.
HB.instance Definition _ := isFunctor.Build acto func_id func_comp.
End empty.
End Empty.
HB.export Empty.

Module Append.
Section append.
Definition acto (X : UU0) := (X * X)%type.
Let actm (X Y : UU0) (f : X -> Y) (t : acto X) : acto Y :=
  let: (x1, x2) := t in (f x1, f x2).
Let func_id : FunctorLaws.id actm.
Proof. by move=> A; apply funext => -[]. Qed.
Let func_comp : FunctorLaws.comp actm.
Proof. by move=> A B C f g; apply funext => -[]. Qed.
HB.instance Definition _ := isFunctor.Build acto func_id func_comp.
End append.
End Append.
HB.export Append.

Section appendop.
Local Notation M := [the monad of ListMonad.acto].

Definition empty : Empty.acto \o M ~~> M := fun A _ => @nil A.

Let naturality_empty : naturality (Empty.acto \o M) M empty.
Proof. by move=> A B h; exact: funext. Qed.

HB.instance Definition _ :=
  isNatural.Build (Empty.acto \o M) M empty naturality_empty.

Definition empty_op : Empty.acto.-operation M := [the _ ~> _ of empty].

Lemma algebraic_empty : algebraicity empty_op.
Proof. by []. Qed.

Definition append : Append.acto \o M ~~> M :=
  fun A x => let: (s1, s2) := x in (s1 ++ s2).

Let naturality_append : naturality (Append.acto \o M) M append.
Proof.
move=> A B h; apply funext => -[s1 s2] /=.
rewrite /actm /=.
by rewrite map_cat flatten_cat.
Qed.

HB.instance Definition _ :=
  isNatural.Build (Append.acto \o M) M append naturality_append.

Definition append_op : Append.acto.-operation M := [the _ ~> _ of append].

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
Proof. by move=> A; apply funext; case. Qed.
Let func_comp : FunctorLaws.comp actm.
Proof. by move=> A B C f g; apply funext; case. Qed.
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
apply: funext => -[w [x w']].
by rewrite /output /= catA.
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
Proof. by move=> A B h; apply: funext => -[]. Qed.

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
apply funext => w.
by rewrite /output /= /imonad_model.output /= cats0.
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
Proof. by move=> A; apply funext => -[]. Qed.
Let func_comp : FunctorLaws.comp actm.
Proof. by move=> A B C g h; apply funext => -[]. Qed.
HB.instance Definition _ := isFunctor.Build acto func_id func_comp.
End local.
End Local.
HB.export Local.

Section environmentops.
Variable E : UU0.
Local Notation M := (EnvironmentMonad.acto E).

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
Proof. by move=> A B h; apply: funext => -[]. Qed.

HB.instance Definition _ := isNatural.Build
  (Local.acto E \o M) M local naturality_local.

Definition local_op : (Local.acto E).-operation M :=
  [the _ ~> _ of local].

(* NB: local is not algebraic *)
Lemma algebraic_local : algebraicity local_op.
Proof.
move=> A B f t.
rewrite environment_bindE.
rewrite /local_op /=.
rewrite /local /=.
rewrite /actm /=.
case: t => /= ee m.
rewrite environment_bindE.
apply funext=> x /=.
Abort.

End environmentops.

(* wip *)
Module Environment.
Section environment.
Variable E : UU0.
Local Notation M := (EnvironmentMonad.acto E).
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
Proof. by move=> A; apply funext => -[]. Qed.
Let func_comp : FunctorLaws.comp actm.
Proof. by move=> A B C g h; apply funext => -[]. Qed.
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

Proof. by move=> A B h; apply: funext => -[[]]. Qed.

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
Proof. by move=> A; apply funext. Qed.
Let func_comp : FunctorLaws.comp actm.
Proof. by move=> A B C g h; apply funext. Qed.
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
Proof. by move=> A; apply: funext => -[]. Qed.
Let func_comp : FunctorLaws.comp actm.
Proof. by move=> A B C g h; apply: funext. Qed.
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
move=> A B h; apply: funext => /= m; apply: funext => s.
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
by move=> A B h; apply: funext => /= -[s m /=]; apply: funext.
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

End fail.
End Fail.
HB.export Fail.

Module Except.
Section except.
Let M : failMonad := option_monad.
Definition handle : forall A, M A -> M A -> M A :=
  fun A m1 m2 => @handle_op unit _ (m1, (fun _ => m2)).
Lemma handleE : handle = (fun A m m' => if m is inr x then m else m').
Proof. by apply funext_dep => A; apply funext => -[]. Qed.
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

End Alt.
HB.export Alt.

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

End Nondet.

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
Proof. by move=> *; apply funext => -[]. Qed.
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
Proof. by rewrite /addM bindretf; apply funext. Abort.

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
Proof. by rewrite /addM bindretf; apply funext. Abort.
Goal Ret 1 +m (reset (Ret 10 +m (shift (fun f : _ -> M nat => Ret 100 : M _) : M _)) : M _) =
     Ret (1 + 100).
Proof. by rewrite /addM bindretf; apply funext. Abort.
Goal Ret 1 +m (reset (Ret 10 +m (shift (fun f : _ -> M nat => f 100 +m f 1000) : M _)) : M _) =
     Ret (1 + ((10 + 100) + (10 + 1000))).
Proof. by rewrite /addM bindretf; apply funext. Abort.

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
Proof. by rewrite /addM bindretf; apply funext. Abort.
Goal reset (Ret 2 *m shift (fun k : _ -> M _ => k 4 +m Ret 1 : M _)
                  *m shift (fun k : _ -> M _ => k 3 +m Ret 1 : M _) : M _ ) = Ret 26 :> M _.
Proof. by rewrite /mulM bindretf; apply funext. Abort.

End shiftreset_examples.

(* wip *)
Module ModelStateLoop.
Section modelstateloop.
Variable S : UU0.
Local Notation M := (StateMonad.acto S).
Fixpoint mforeach (it min : nat) (body : nat -> M unit) : M unit :=
  if it <= min then Ret tt
  else if it is it'.+1 then
      (body it') >>= (fun _ => mforeach it' min body)
      else Ret tt.
Let loop0 m body : mforeach m m body = Ret tt.
Proof. by case: m => //= n; rewrite ltnS leqnn. Qed.
Let loop1 m n body : mforeach (m.+1 + n) m body =
     (body (m + n)) >> mforeach (m + n) m body :> M unit.
Proof. by rewrite /mforeach /=; case: ifPn => //; rewrite ltnNge leq_addr. Qed.
HB.instance Definition _ := isMonadStateLoop.Build S M loop0 loop1.
End modelstateloop.
End ModelStateLoop.
HB.export ModelStateLoop.

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
rewrite state_bindE; apply funext => a/=.
by rewrite /aput insert_insert.
Qed.
Let aputget i s A (k : S -> M A) : aput i s >> aget i >>= k = aput i s >> k s.
Proof.
rewrite state_bindE; apply funext => a/=.
by rewrite /aput insert_same.
Qed.
Let agetput i : aget i >>= aput i = skip.
Proof.
rewrite state_bindE; apply funext => a/=.
by rewrite /aput insert_same2.
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
by move=> [ij|->{u}]; rewrite !state_bindE /aput; apply/funext => a/=;
  [rewrite insertC|rewrite insertC2].
Qed.
Let aputgetC i j u A (k : S -> M A) : i != j ->
  aput i u >> aget j >>= k = aget j >>= (fun v => aput i u >> k v).
Proof.
move=> ij; rewrite /aput !state_bindE; apply funext => a/=.
by rewrite state_bindE/= {1}/insert (negbTE ij).
Qed.
HB.instance Definition _ := Monad.on M.
HB.instance Definition _ := isMonadArray.Build
  S I M aputput aputget agetput agetget agetC aputC aputgetC.
End modelarray.
End ModelArray.

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
  apply funext => f; apply funext => m; apply funext => s.
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
  apply funext => f; apply funext => m.
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
  by apply funext => f; apply funext => m.
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
rewrite MS_mapE /actm /=.
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
move=> A x; rewrite /Catch /mapStateT2; apply funext => s.
by rewrite catchmfail.
Qed.
Let Catchfailm : forall A, left_id (liftS (@fail N A)) (@Catch A).
Proof.
move=> A x; rewrite /Catch /mapStateT2; apply funext => s.
by rewrite catchfailm.
Qed.
Let CatchA : forall A, ssrfun.associative (@Catch A).
Proof.
move=> A; rewrite /Catch /mapStateT2 => a b c; apply funext => s.
by rewrite catchA.
Qed.
Let Catchret : forall A x, @left_zero (M A) (M A) (Ret x) (@Catch A).
Proof.
move=> A x y; rewrite /Catch /mapStateT2; apply funext => s.
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
