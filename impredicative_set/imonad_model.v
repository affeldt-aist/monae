From mathcomp Require Import all_ssreflect.
Require Import imonae_lib.
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
(* option_monad       == notation for ExceptMonad.acto unit                   *)
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
(* Module Fail             == failMonad for option_monad, ListMonad.acto      *)
(* Module Except           == exceptMonad for ExcetMonad.acto unit            *)
(* Module State            == stateMonad for StateMonad.acto S                *)
(* Module Alt              == altMonad for ListMonad.acto                     *)
(* Module AltCI            == altCIMonad for ListMonad.acto                   *)
(* Module Nondet           == nondetMonad for ListMonad.acto                  *)
(* Module ModelStateTrace  == stateTraceMonad for StateMonad.acto (S * seq T) *)
(* Module ModelCont        == contMonad for ContMonad.acto r                  *)
(* Module ModelShiftReset  == shiftResetMonad for ContMonad.acto r            *)
(* Module ModelReify       == reifyModel for StateMonad.acto (S * seq T)      *)
(* Module ModelStateTraceReify == stateTraceReify monad for                   *)
(*                                StateMonad.acto (S * seq T)                 *)
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

Module IdentityMonad. Section identitymonad.
Let bind := fun A B (a : FId A) (f : A -> FId B) => f a.
Local Lemma fmapE (A B : UU0) (f : A -> B) (m : FId A) :
  (FId # f) m = @bind _ _ m (@NId FId _ \o f).
Proof. by []. Qed.
Local Lemma left_neutral : BindLaws.left_neutral bind (NId FId).
Proof. by []. Qed.
Local Lemma right_neutral : BindLaws.right_neutral bind (NId FId).
Proof. by []. Qed.
Local Lemma associative : BindLaws.associative bind. Proof. by []. Qed.
HB.instance Definition _ := @Monad_of_ret_bind.Build idfun (NId FId)
  bind fmapE left_neutral right_neutral associative.
End identitymonad. End IdentityMonad.
HB.export IdentityMonad.

Module ListMonad. Section listmonad.
Definition acto := fun (A :UU0) => seq A.
Local Notation M := acto.
Let map_id : @FunctorLaws.id seq (@map).
Proof. by move=> A; apply fun_ext => x; rewrite map_id. Qed.
Let map_comp : @FunctorLaws.comp seq (@map).
Proof. by move=> A B C g h; apply fun_ext => x; rewrite map_comp. Qed.
HB.instance Definition _ := isFunctor.Build M map_id map_comp.
Let ret_component := fun A : Type => (@cons A)^~ [::].
Let ret_naturality : naturality FId [the functor of M] ret_component.
Proof. by move=> A B h; apply fun_ext. Qed.
Let ret : FId ~> M := Natural.Pack (Natural.Mixin ret_naturality).
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
Let fmapE (A B : UU0) (f : A -> B) (m : M A) :
  ([the functor of M] # f) m = bind m (@ret _ \o f).
Proof.
rewrite /= /actm /= /bind /ret_component /=.
by rewrite map_comp /= flatten_seq1.
Qed.
HB.instance Definition _ := @Monad_of_ret_bind.Build M ret bind
  fmapE left_neutral right_neutral associative.
End listmonad. End ListMonad.
HB.export ListMonad.

Lemma ListMonadE (A B : UU0) (M := ListMonad.acto) (m : M A) (f : A -> M B) :
  m >>= f = flatten (map f m).
Proof. by []. Qed.

Module ExceptMonad.
Section exceptmonad.
Variable E : UU0.
Definition acto := fun A : UU0 => (E + A)%type.
Local Notation M := acto.
Let map := fun (A B : UU0) (f : A -> B) (a : M A) =>
  match a with inl z => inl z | inr b => inr (f b) end.
Let map_id : FunctorLaws.id map.
Proof. by move=> *; apply fun_ext; case. Qed.
Let map_comp : FunctorLaws.comp map.
Proof. by move=> *; apply fun_ext; case. Qed.
HB.instance Definition _ := isFunctor.Build M map_id map_comp.
Let ret_component := @inr E.
Let natural : naturality FId [the functor of M] ret_component.
Proof. by move=> A B h; apply fun_ext. Qed.
Let ret : FId ~> M := Natural.Pack (Natural.Mixin natural).
Let bind := fun A B (m : M A) (f : A -> M B) =>
  match m with inl z => inl z | inr b => f b end.
Let left_neutral : BindLaws.left_neutral bind ret.
Proof. by []. Qed.
Let right_neutral : BindLaws.right_neutral bind ret.
Proof. by move=> ? []. Qed.
Let associative : BindLaws.associative bind.
Proof. by move=> ? ? ? []. Qed.
Let fmapE (A B : UU0) (f : A -> B) (m : acto A) :
  ([the functor of M] # f) m = bind m (@ret _ \o f).
Proof. by rewrite /= /actm /= /ret_component /bind; case: m. Qed.
HB.instance Definition _ := @Monad_of_ret_bind.Build M ret bind fmapE
  left_neutral right_neutral associative.
End exceptmonad.
End ExceptMonad.
HB.export ExceptMonad.

Lemma ExceptMonadE (E A B : UU0) (M := ExceptMonad.acto E) (m : M A) (f : A -> M B) :
  m >>= f = match m with inl z => inl z | inr b => f b end.
Proof. by []. Qed.

Notation option_monad := (ExceptMonad.acto unit).

Module OutputMonad.
Section output.
Variable L : UU0.
Definition acto := fun X : UU0 => (X * seq L)%type.
Local Notation M := acto.
Let map (A B : UU0) (f : A -> B) (m : M A) : M B :=
  let: (a, s) := m in (f a, s).
Let map_id : FunctorLaws.id map.
Proof. by move=> A; apply fun_ext; case. Qed.
Let map_comp : FunctorLaws.comp map.
Proof. by move=> A B C g h; apply fun_ext; case. Qed.
HB.instance Definition _ := isFunctor.Build M map_id map_comp.
Let ret_component : FId ~~> M := fun A a => (a, [::]).
Let naturality_ret : naturality FId [the functor of M] ret_component.
Proof. by move=> A B h; apply fun_ext. Qed.
Let ret : FId ~> M := Natural.Pack (Natural.Mixin naturality_ret).
Let bind := fun A B (m : M A) (f : A -> M B) =>
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
Let fmapE (A B : UU0) (f : A -> B) (m : M A) :
  ([the functor of acto] # f) m = bind m (@ret _ \o f).
Proof. by rewrite /actm /= /bind /=; case: m => h t; rewrite cats0. Qed.
HB.instance Definition _ := @Monad_of_ret_bind.Build M ret bind fmapE
  left_neutral right_neutral associative.
End output.
End OutputMonad.
HB.export OutputMonad.

Lemma OutputMonadE (L A B : UU0) (M := OutputMonad.acto L) (m : M A) (f : A -> M B) :
  m >>= f = let: (x, w) := m in let: (x', w') := f x in (x', w ++ w').
Proof. by []. Qed.

Module EnvironmentMonad.
Section environment.
Variable E : UU0.
Definition acto := fun A : UU0 => E -> A.
Local Notation M := acto.
Let map (A B : UU0) (f : A -> B) (m : M A) : M B := fun e => f (m e).
Let map_id : FunctorLaws.id map. Proof. by []. Qed.
Let map_comp : FunctorLaws.comp map.
Proof. by move=> A B C g h; apply fun_ext. Qed.
HB.instance Definition _ := isFunctor.Build M map_id map_comp.
Definition ret_component : FId ~~> M := fun A x => fun e => x.
(* computation that ignores the environment *)
Let naturality_ret : naturality FId [the functor of M] ret_component.
Proof. by move=> A B h; apply fun_ext. Qed.
Let ret : FId ~> M := Natural.Pack (Natural.Mixin naturality_ret).
Let bind := fun A B (m : M A) (f : A -> M B) => fun e => f (m e) e.
(* binds m f applied the same environment to m and to the result of f *)
Let left_neutral : BindLaws.left_neutral bind ret.
Proof. by []. Qed.
Let right_neutral : BindLaws.right_neutral bind ret.
Proof. by []. Qed.
Let associative : BindLaws.associative bind.
Proof. by []. Qed.
Let fmapE (A B : UU0) (f : A -> B) (m : M A) :
  ([the functor of M] # f) m = bind m (@ret _ \o f).
Proof.
by rewrite /actm /= /bind /ret_component; apply fun_ext => e.
Qed.
HB.instance Definition _ := @Monad_of_ret_bind.Build M ret bind fmapE
  left_neutral right_neutral associative.
End environment.
End EnvironmentMonad.
HB.export EnvironmentMonad.

Lemma EnvironmentMonadE (E A B : UU0) (M := EnvironmentMonad.acto E) (m : M A) (f : A -> M B) :
  m >>= f = fun e => f (m e) e.
Proof. by []. Qed.

Module StateMonad.
Section state.
Variable S : UU0. (* type of states *)
Definition acto := fun A : UU0 => S -> A * S.
Local Notation M := acto.
Let map (A B : UU0) (f : A -> B) (m : M A) : M B :=
  fun (s : S) => let (x1, x2) := m s in (f x1, x2).
Let map_id : FunctorLaws.id map.
Proof.
move=> x; apply fun_ext => y; apply fun_ext => z /=.
by  rewrite /map; case: y.
Qed.
Let map_comp : FunctorLaws.comp map.
Proof.
move=> A B C g h; apply fun_ext => m; apply fun_ext => s.
by rewrite /map /=; case: m.
Qed.
HB.instance Definition _ := isFunctor.Build M map_id map_comp.
Let ret_component : FId ~~> M := fun A a => fun s => (a, s).
Let naturality_ret : naturality FId [the functor of M] ret_component.
Proof. by move=> A B h; apply fun_ext => a /=; apply fun_ext. Qed.
Let ret : FId ~> M := Natural.Pack (Natural.Mixin naturality_ret).
Let bind := fun A B (m : M A) (f : A -> M B) => uncurry f \o m.
Let left_neutral : BindLaws.left_neutral bind ret.
Proof. by move=> A B a f; apply fun_ext. Qed.
Let right_neutral : BindLaws.right_neutral bind ret.
Proof.
by move=> A f; apply fun_ext => s; rewrite /bind /=; case: (f s).
Qed.
Let associative : BindLaws.associative bind.
Proof.
move=> A B C a b c; rewrite /bind compA; congr (_ \o _).
by apply fun_ext => -[].
Qed.
Let fmapE (A B : UU0) (f : A -> B) (m : M A) :
  ([the functor of acto] # f) m = bind m (@ret _ \o f).
Proof.
by rewrite /actm /= /bind /ret_component /=; apply fun_ext => s.
Qed.
HB.instance Definition _ := @Monad_of_ret_bind.Build
  M ret bind fmapE left_neutral right_neutral associative.
End state.
End StateMonad.
HB.export StateMonad.

Lemma StateMonadE (S A B : UU0) (M := StateMonad.acto S) (m : M A) (f : A -> M B) :
  m >>= f = uncurry f \o m.
Proof. by []. Qed.

(* see Sect. 3 of of [Wadler, 94] for the model of the ret and the bind of the
continuation monad *)
Module ContMonad.
Section cont.
Variable r : UU0. (* the type of answers *)
Definition acto := fun A : UU0 => (A -> r) -> r.
Local Notation M := acto.
Let actm (A B : UU0) (f : A -> B) (m : M A) : M B :=
  fun Br : B -> r => m (fun a : A => Br (f a)).
Let map_id : FunctorLaws.id actm.
Proof. by move=> A; apply fun_ext => m; apply fun_ext. Qed.
Let map_comp : FunctorLaws.comp actm.
Proof. by move=> *; apply fun_ext => m; apply fun_ext. Qed.
HB.instance Definition _ := isFunctor.Build M map_id map_comp.
Let naturality_ret : naturality FId [the functor of M] (fun A a => fun k => k a).
Proof. by move=> A B f; apply fun_ext => a /=; apply fun_ext. Qed.
Let ret : FId ~> M:= Natural.Pack (Natural.Mixin naturality_ret).
Let bind := fun A B (m : M A) (f : A -> M B) => fun k => m (fun a => f a k).
Let left_neutral : BindLaws.left_neutral bind ret.
Proof. by move=> A B a f; apply fun_ext => Br. Qed.
Let right_neutral : BindLaws.right_neutral bind ret.
Proof. by []. Qed.
Let associative : BindLaws.associative bind.
Proof. by []. Qed.
Let fmapE (A B : UU0) (f : A -> B) (m : M A) :
  ([the functor of acto] # f) m = bind m (@ret _ \o f).
Proof.
by rewrite /actm /= /bind /ret_component /=; apply fun_ext => s.
Qed.
HB.instance Definition _ := @Monad_of_ret_bind.Build
  M ret bind fmapE left_neutral right_neutral associative.
End cont.
End ContMonad.
HB.export ContMonad.

Lemma ContMonadE (r A B : UU0) (M := ContMonad.acto r) (m : M A) (f : A -> M B) :
  m >>= f = fun k => m (fun a => f a k).
Proof. by []. Qed.

Module Empty. Section empty.
Definition acto (X : UU0) : UU0 := unit.
Let actm (X Y : UU0) (f : X -> Y) (t : acto X) : acto Y := tt.
Let func_id : FunctorLaws.id actm.
Proof. by move=> A; apply fun_ext; case. Qed.
Let func_comp : FunctorLaws.comp actm.
Proof. by move=> A B C f g; apply fun_ext; case. Qed.
HB.instance Definition _ := isFunctor.Build acto func_id func_comp.
End empty. End Empty.
HB.export Empty.

Module Append. Section append.
Definition acto (X : UU0) := (X * X)%type.
Let actm (X Y : UU0) (f : X -> Y) (t : acto X) : acto Y :=
  let: (x1, x2) := t in (f x1, f x2).
Let func_id : FunctorLaws.id actm.
Proof. by move=> A; apply fun_ext; case. Qed.
Let func_comp : FunctorLaws.comp actm.
Proof. by move=> A B C f g; apply fun_ext; case. Qed.
HB.instance Definition _ := isFunctor.Build acto func_id func_comp.
End append. End Append.
HB.export Append.

Section tmp.
Local Notation M := [the monad of ListMonad.acto].

Definition empty A : unit -> M A := fun _ => @nil A.
Lemma naturality_empty : naturality ([the functor of Empty.acto] \O M) M empty.
Proof. by move=> A B h; apply fun_ext. Qed.
Definition empty_op : [the functor of Empty.acto].-operation M :=
  Natural.Pack (Natural.Mixin naturality_empty).
Lemma algebraic_empty : algebraicity empty_op.
Proof. by []. Qed.

Definition append A : (M A * M A)%type -> M A :=
  fun x => let: (s1, s2) := x in (s1 ++ s2).
Let naturality_append : naturality ([the functor of Append.acto] \O M) M append.
Proof.
move=> A B h; apply fun_ext; case=> s1 s2 /=.
by rewrite /actm /= map_cat.
Qed.
Definition append_op : [the functor of Append.acto].-operation M :=
  Natural.Pack (Natural.Mixin naturality_append).
Lemma algebraic_append : algebraicity append_op.
Proof.
move=> A B f [t1 t2] /=.
by rewrite 3!ListMonadE -flatten_cat -map_cat.
Qed.
End tmp.

Module Output. Section output. Variable L : UU0.
Definition acto (X : UU0) := (seq L * X)%type.
Let actm (X Y : UU0) (f : X -> Y) (t : acto X) : acto Y :=
  let: (w, x) := t in (w, f x).
Let func_id : FunctorLaws.id actm.
Proof. by move=> A; apply fun_ext; case. Qed.
Let func_comp : FunctorLaws.comp actm.
Proof. by move=> A B C f g; apply fun_ext; case. Qed.
HB.instance Definition _ := isFunctor.Build acto func_id func_comp.
End output. End Output.
HB.export Output.

Module Flush. Section flush.
Definition acto (X : UU0) := X.
Let actm (X Y : UU0) (f : X -> Y) (t : acto X) : acto Y := f t.
Let func_id : FunctorLaws.id actm. Proof. by []. Qed.
Let func_comp : FunctorLaws.comp actm. Proof. by []. Qed.
HB.instance Definition _ := isFunctor.Build acto func_id func_comp.
End flush. End Flush.
HB.export Flush.

Section outputops.
Variable L : UU0.
Local Notation M := (OutputMonad.acto L).

Definition output (A : UU0) : (seq L * M A) -> M A :=
  fun m => let: (x, w') := m.2 in (x, m.1 ++ w'). (*NB: w'++m.1 in the esop paper*)
Let naturality_output : naturality ([the functor of Output.acto L] \O [the functor of M]) [the functor of M] output.
Proof.
by move=> A B h; apply fun_ext; case => w [x w'].
Qed.
Definition output_op : [the functor of Output.acto L].-operation [the monad of M] :=
  Natural.Pack (Natural.Mixin naturality_output).
Lemma algebraic_output : algebraicity output_op.
Proof.
move=> A B f [w [x w']].
rewrite OutputMonadE /=.
rewrite /output /=.
rewrite OutputMonadE.
by case: f => x' w''; rewrite catA.
Qed.

Definition flush A : M A -> M A := fun m => let: (x, _) := m in (x, [::]).
(* performing a computation in a modified environment *)
Let naturality_flush : naturality ([the functor of Flush.acto] \O [the functor of M]) [the functor of M] flush.
Proof. by move=> A B h; apply fun_ext; case. Qed.
Definition flush_op : [the functor of Flush.acto].-operation [the monad of M] := Natural.Pack (Natural.Mixin naturality_flush).
(* NB: flush is not algebraic *)
Lemma algebraic_flush : algebraicity flush_op.
Proof.
move=> A B f [x w].
rewrite OutputMonadE.
rewrite /flush_op /=.
rewrite /flush /=.
rewrite /actm /=.
rewrite OutputMonadE.
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
apply fun_ext => w.
by rewrite /output /= /imonad_model.output /= cats0.
Qed.
(* TODO: complete with an interface for the output monad and instantiate *)
End output.
End Output'.

Module Ask. Section ask. Variable E : UU0.
Definition acto (X : UU0) := E -> X.
Let actm (X Y : UU0) (f : X -> Y) (t : acto X) : acto Y := f \o t.
Let func_id : FunctorLaws.id actm. Proof. by []. Qed.
Let func_comp : FunctorLaws.comp actm. Proof. by []. Qed.
HB.instance Definition _ := isFunctor.Build acto func_id func_comp.
End ask. End Ask.
HB.export Ask.

Module Local. Section local. Variable E : UU0.
Definition acto (X : UU0) := ((E -> E) * X)%type.
Let actm (X Y : UU0) (f : X -> Y) (t : acto X) : acto Y :=
  let: (e, x) := t in (e, f x).
Let func_id : FunctorLaws.id actm.
Proof. by move=> A; apply fun_ext; case. Qed.
Let func_comp : FunctorLaws.comp actm.
Proof. by move=> A B C g h; apply fun_ext; case. Qed.
HB.instance Definition _ := isFunctor.Build acto func_id func_comp.
End local. End Local.
HB.export Local.

Section environmentops.
Variable E : UU0.
Local Notation M := (EnvironmentMonad.acto E).

Definition ask A : (E -> M A) -> M A := fun f s => f s s. (* reading the environment *)
Let naturality_ask : naturality ([the functor of Ask.acto E] \O [the functor of M]) [the functor of M] ask.
Proof. by []. Qed.
Definition ask_op : [the functor of Ask.acto E].-operation [the monad of M] :=
  Natural.Pack (Natural.Mixin naturality_ask).
Lemma algebraic_ask : algebraicity ask_op.
Proof. by []. Qed.

Definition local A : (E -> E) * M A -> M A := fun x s => let: (e, t) := x in t (e s).
(* performing a computation in a modified environment *)
Lemma naturality_local : naturality ([the functor of Local.acto E] \O [the functor of M]) [the functor of M] local.
Proof. by move=> A B h; apply fun_ext; case. Qed.
Definition local_op : [the functor of Local.acto E].-operation [the monad of M] :=
  Natural.Pack (Natural.Mixin naturality_local).
(* NB: local is not algebraic *)
Lemma algebraic_local : algebraicity local_op.
Proof.
move=> A B f t.
rewrite EnvironmentMonadE.
rewrite /local_op /=.
rewrite /local /=.
rewrite /actm /=.
case: t => /= ee m.
rewrite EnvironmentMonadE.
apply fun_ext=> x /=.
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

Module Throw. Section throw. Variable Z : UU0.
Definition acto (X : UU0) := Z.
Let actm (X Y : UU0) (f : X -> Y) (t : acto X) : acto Y := t.
Let func_id : FunctorLaws.id actm. Proof. by []. Qed.
Let func_comp : FunctorLaws.comp actm. Proof. by []. Qed.
HB.instance Definition _ := isFunctor.Build acto func_id func_comp.
End throw. End Throw.
HB.export Throw.

Module Handle. Section handle. Variable Z : UU0.
Definition acto (X : UU0) := (X * (Z -> X))%type.
Let actm (X Y : UU0) (f : X -> Y) (t : acto X) : acto Y :=
  let: (x, h) := t in (f x, fun z => f (h z)).
Let func_id : FunctorLaws.id actm.
Proof. by move=> A; apply fun_ext; case. Qed.
Let func_comp : FunctorLaws.comp actm.
Proof. by move=> A B C g h; apply fun_ext; case. Qed.
HB.instance Definition _ := isFunctor.Build acto func_id func_comp.
End handle. End Handle.
HB.export Handle.

Section exceptops.
Variable Z : UU0.
Local Notation M := (ExceptMonad.acto Z).

Definition throw (A : UU0) : Z -> M A := fun z => inl z.
Let naturality_throw : naturality ([the functor of Throw.acto Z] \O [the functor of M]) [the functor of M] throw.
Proof. by []. Qed.
Definition throw_op : [the functor of Throw.acto Z].-operation [the monad of M] :=
  Natural.Pack (Natural.Mixin naturality_throw).
Lemma algebraic_throw : algebraicity throw_op.
Proof. by []. Qed.
Definition throw_aop : [the functor of Throw.acto Z].-aoperation [the monad of M] :=
  AOperation.Pack (AOperation.Class (AOperation.Mixin algebraic_throw)).

Definition handle A (m : M A) (h : Z -> M A) : M A :=
  match m with inl z => h z | inr x => inr x end.
Let naturality_handle :
  naturality ([the functor of Handle.acto Z] \O [the functor of M]) [the functor of M] (fun A => uncurry (@handle A)).
Proof. by move=> A B h; apply fun_ext; case; case. Qed.
Definition handle_op : [the functor of Handle.acto Z].-operation [the monad of M] :=
  Natural.Pack (Natural.Mixin naturality_handle).
(* NB: handle is not algebraic *)
Lemma algebraic_handle : algebraicity handle_op.
Proof.
move=> A B f t.
rewrite ExceptMonadE.
rewrite /handle_op /=.
rewrite /handle /=.
rewrite /uncurry /prod_curry /Datatypes.uncurry /=.
case: t => -[z//|a] g /=.
rewrite ExceptMonadE.
case: (f a) => // z.
rewrite ExceptMonadE.
case: (g z) => [z0|a0].
Abort.

End exceptops.

Arguments throw_op {Z}.
Arguments handle_op {Z}.

(* NB: see also Module Ask *)
Module StateOpsGet. Section get. Variable S : UU0.
Definition acto (X : UU0) := S -> X.
Let actm (X Y : UU0) (f : X -> Y) (t : acto X) : acto Y := f \o t.
Let func_id : FunctorLaws.id actm.
Proof. by move=> A; apply fun_ext. Qed.
Let func_comp : FunctorLaws.comp actm.
Proof. by move=> A B C g h; apply fun_ext. Qed.
HB.instance Definition _ := isFunctor.Build acto func_id func_comp.
End get. End StateOpsGet.
HB.export StateOpsGet.

Module StateOpsPut. Section put. Variable S : UU0.
Definition acto (X : UU0) := (S * X)%type.
Let actm (X Y : UU0) (f : X -> Y) (sx : acto X) : acto Y := (sx.1, f sx.2).
Let func_id : FunctorLaws.id actm.
Proof. by move=> A; apply fun_ext; case. Qed.
Let func_comp : FunctorLaws.comp actm.
Proof. by move=> A B C g h; apply fun_ext. Qed.
HB.instance Definition _ := isFunctor.Build acto func_id func_comp.
End put. End StateOpsPut.
HB.export StateOpsPut.

Section stateops.
Variable S : UU0.
Local Notation M := (StateMonad.acto S).

Let get A (k : S -> M A) : M A := fun s => k s s.
Let naturality_get : naturality ([the functor of StateOpsGet.acto S] \O [the functor of M]) [the functor of M] get.
Proof.
move=> A B h; apply fun_ext => /= m /=.
by apply fun_ext => s; rewrite FCompE.
Qed.
Definition get_op : [the functor of StateOpsGet.acto S].-operation [the monad of M] :=
  Natural.Pack (Natural.Mixin naturality_get).
Lemma algebraic_get : algebraicity get_op.
Proof. by []. Qed.
Definition get_aop : [the functor of StateOpsGet.acto S].-aoperation [the monad of M] :=
  AOperation.Pack (AOperation.Class (AOperation.Mixin algebraic_get)).

Let put A (s : S) (m : M A) : M A := fun _ => m s.
Let naturality_put :
  naturality ([the functor of StateOpsPut.acto S] \O [the functor of M]) [the functor of M] (fun A => uncurry (put (A:=A))).
Proof.
move=> A B h.
by apply fun_ext => /=; case => s m /=; apply fun_ext.
Qed.
Definition put_op : [the functor of StateOpsPut.acto S].-operation [the monad of M] :=
  Natural.Pack (Natural.Mixin naturality_put).
Lemma algebraic_put : algebraicity put_op.
Proof. by move=> ? ? ? []. Qed.
Definition put_aop : [the functor of StateOpsPut.acto S].-aoperation [the monad of M] :=
  AOperation.Pack (AOperation.Class (AOperation.Mixin algebraic_put)).

End stateops.

Arguments get_op {S}.
Arguments put_op {S}.

Module ContOpsAbort. Section abort. Variable r : UU0.
Definition acto (X : UU0) := r.
Let actm (A B : UU0) (f : A -> B) (x : acto A) : acto B := x.
Let func_id : FunctorLaws.id actm. Proof. by []. Qed.
Let func_comp : FunctorLaws.comp actm. Proof. by []. Qed.
HB.instance Definition _ := isFunctor.Build acto func_id func_comp.
(*Definition F := Functor.Pack (Functor.Class func_mixin).*)
End abort. End ContOpsAbort.
HB.export ContOpsAbort.

Module ContOpsAcallcc. Section acallcc. Variable r : UU0.
Definition acto := fun A : UU0 => (A -> r) -> A.
Let actm (X Y : UU0) (f : X -> Y) (t : acto X) : acto Y :=
  fun (g : Y -> r) => f (t (fun x => g (f x))).
Let func_id : FunctorLaws.id actm. Proof. by []. Qed.
Let func_comp : FunctorLaws.comp actm. Proof. by []. Qed.
HB.instance Definition _ := isFunctor.Build acto func_id func_comp.
End acallcc. End ContOpsAcallcc.
HB.export ContOpsAcallcc.

Section contops.
Variable r : UU0.

Local Notation M := (ContMonad.acto r).

Definition abort (A : UU0) : r -> M A := fun r _ => r.
Lemma naturality_abort : naturality ([the functor of ContOpsAbort.acto r] \O [the monad of M]) [the monad of M] abort.
Proof. by []. Qed.
Definition abort_op : [the functor of ContOpsAbort.acto r].-operation [the monad of M] :=
  Natural.Pack (Natural.Mixin naturality_abort).
Lemma algebraicity_abort : algebraicity abort_op.
Proof. by []. Qed.
Definition abort_aop : [the functor of ContOpsAbort.acto r].-aoperation [the monad of M] :=
  AOperation.Pack (AOperation.Class (AOperation.Mixin algebraicity_abort)).

(* alebgraic call/cc *)
Definition acallcc A (f : (M A -> r) -> M A) : M A :=
  fun k => f (fun m => m k) k.
Lemma naturality_acallcc : naturality ([the functor of ContOpsAcallcc.acto r] \O [the functor of M]) [the functor of M] acallcc.
Proof. by []. Qed.
Definition acallcc_op : [the functor of ContOpsAcallcc.acto r].-operation [the monad of M] :=
  Natural.Pack (Natural.Mixin naturality_acallcc).
Lemma algebraicity_callcc : algebraicity acallcc_op.
Proof. by []. Qed.
Definition callcc_aop : [the functor of ContOpsAcallcc.acto r].-aoperation [the monad of M] :=
  AOperation.Pack (AOperation.Class (AOperation.Mixin algebraicity_callcc)).

End contops.

Module Fail.

Definition option_fail : forall A, option_monad A := fun A => @throw unit A tt.
Local Lemma option_bindfailf : BindLaws.left_zero (@bind [the monad of option_monad]) option_fail.
Proof. by []. Qed.
HB.instance Definition _ := @isMonadFail.Build option_monad
  option_fail option_bindfailf.

Definition list_fail : forall A, ListMonad.acto A := fun A => @empty _ tt.
Local Lemma list_bindfailf : BindLaws.left_zero (@bind [the monad of ListMonad.acto]) list_fail.
Proof. by []. Qed.
HB.instance Definition _ := @isMonadFail.Build ListMonad.acto list_fail list_bindfailf.

End Fail.
HB.export Fail.

Module Except.
Section except.
Let M : failMonad := [the failMonad of ExceptMonad.acto unit].
Definition handle : forall A, M A -> M A -> M A :=
  fun A m1 m2 => @handle_op unit _ (m1, (fun _ => m2)).
Lemma handleE : handle = (fun A m m' => if m is inr x then m else m').
Proof. by apply fun_ext_dep => A; apply fun_ext; case. Qed.
Let catchmfail : forall A, right_id fail (@handle A).
Proof. by move=> A; case => //; case. Qed.
Let catchfailm : forall A, left_id fail (@handle A).
Proof. by move=> A; case. Qed.
Let catchA : forall A, ssrfun.associative (@handle A).
Proof. by move=> A; case. Qed.
Let catchret : forall A x, @left_zero (M A) (M A) (Ret x) (@handle A).
Proof. by move=> A x; case. Qed.
HB.instance Definition _ := isMonadExcept.Build (ExceptMonad.acto unit)
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
Let getputskip : get >>= put = skip.
Proof. by []. Qed.
Let getget : forall (A : UU0) (k : S -> S -> M A), get >>= (fun s => get >>= k s) = get >>= fun s => k s s.
Proof. by []. Qed.
HB.instance Definition _ := isMonadState.Build S (StateMonad.acto S)
  putput putget getputskip getget.
End state.
End State.
HB.export State.

Module Alt.

Section list.
Let M := ListMonad.acto.
Definition list_alt : forall T, M T -> M T -> M T := fun A => curry (@append A).
Let altA : forall T : UU0, ssrfun.associative (@list_alt T).
Proof. by move=> T a b c; rewrite /list_alt /= /curry /= catA. Qed.
Let alt_bindDl : BindLaws.left_distributive (@bind [the monad of ListMonad.acto]) list_alt.
Proof.
move=> A B /= s1 s2 k.
rewrite ListMonadE.
by rewrite map_cat flatten_cat.
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
Let st_getputskip : st_get >>= st_put = skip.
Proof. by move=> *; apply fun_ext; case. Qed.
Let st_getget : forall (A : UU0) (k : S -> S -> M A),
      st_get >>= (fun s => st_get >>= k s) = st_get >>= fun s => k s s.
Proof. by []. Qed.
Let st_putmark : forall s e, st_put s >> st_mark e = st_mark e >> st_put s.
Proof. by []. Qed.
Let st_getmark : forall e (k : _ -> M S), st_get >>= (fun v => st_mark e >> k v) =
                         st_mark e >> st_get >>= k.
Proof. by []. Qed.
HB.instance Definition _ := @isMonadStateTrace.Build S T (StateMonad.acto (S * seq T)%type)
  st_get st_put st_mark st_putput st_putget st_getputskip st_getget st_putmark st_getmark.
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
Proof. by rewrite /addM bindretf; apply fun_ext. Abort.

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
Proof. by rewrite /addM bindretf; apply fun_ext. Abort.
Goal Ret 1 +m (reset (Ret 10 +m (shift (fun f : _ -> M nat => Ret 100 : M _) : M _)) : M _) =
     Ret (1 + 100).
Proof. by rewrite /addM bindretf; apply fun_ext. Abort.
Goal Ret 1 +m (reset (Ret 10 +m (shift (fun f : _ -> M nat => f 100 +m f 1000) : M _)) : M _) =
     Ret (1 + ((10 + 100) + (10 + 1000))).
Proof. by rewrite /addM bindretf; apply fun_ext. Abort.

Let N : shiftresetMonad (seq nat) := [the shiftresetMonad (seq nat) of ContMonad.acto (seq nat)].
Fixpoint perverse (l : seq nat) : N (seq nat) :=
  if l is h :: t then
    shift (fun f : _ -> N _ => Ret h >>= (fun x => perverse t >>= f >>= (fun y => ret _ (x :: y))))
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
Proof. by rewrite /addM bindretf; apply fun_ext. Abort.
Goal reset (Ret 2 *m shift (fun k : _ -> M _ => k 4 +m Ret 1 : M _)
                  *m shift (fun k : _ -> M _ => k 3 +m Ret 1 : M _) : M _ ) = Ret 26 :> M _.
Proof. by rewrite /mulM bindretf; apply fun_ext. Abort.

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
Let reify : forall A, M A -> state_trace -> option (A * state_trace) := (fun A m s => Some (m s)).
Let reifyret : forall (A : UU0) (a : A) s, @reify _ (Ret a) s = Some (a, s).
Proof. by []. Qed.
Let reifybind : forall (A B : UU0) (m : M A) (f : A -> M B) s,
      @reify _ (m >>= f) s = match @reify _ m s with | Some a's' => @reify _ (f a's'.1) a's'.2 | None => None end.
Proof.
move=> A B m0 f s.
rewrite StateMonadE.
rewrite /uncurry /prod_curry /Datatypes.uncurry /=.
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

(* TODO
Section instantiations_with_the_identity_monad.

Lemma stateT_id_ModelState S :
  stateT S [the monad of idfun] = [the monad of StateMonad.acto S].
Proof.
rewrite /= /stateTmonadM /=.
have FG : MS_functor S ModelMonad.identity = ModelMonad.State.functor S.
  apply: functor_ext => /=; apply fun_ext_dep => A; apply fun_ext_dep => B.
  apply fun_ext => f; apply fun_ext => m; apply fun_ext => s.
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
  apply fun_ext => f; apply fun_ext => m.
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
  by apply fun_ext => f; apply fun_ext => m.
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

Definition aLGet {Z S} : [the functor of StateOpsGet.acto S].-aoperation (exceptT Z (M S)) :=
  alifting (get_aop S) (Lift (exceptT Z) (M S)).

Definition aLPut {Z S} : [the functor of StateOpsPut.acto S].-operation (exceptT Z (M S)) :=
  alifting (put_aop S) (Lift (exceptT Z) (M S)).

Goal forall Z (S : UU0) X (k : S -> exceptT Z (M S) X), aLGet _ k = get_op _ k.
by [].
Abort.

Goal forall Z S, aLGet _ Ret = Lift (exceptT Z) (M S) _ (@get S [the stateMonad S of StateMonad.acto S]).
by [].
Abort.

End state_exceptT.

Section continuation_stateT.
Variable (r S : UU0).
Let M : monad := [the monad of ContMonad.acto r].
Let stS : monadT := stateT S.

Definition aLCallcc : [the functor of ContOpsAcallcc.acto r].-aoperation (stS M) :=
  alifting (callcc_aop r) (Lift stS M).

Goal forall A (f : (stS M A -> r) -> stS M A),
  aLCallcc _ f = (fun s k => f (fun m => uncurry m (s, k)) s k) :> stS M A.
move=> A f.
by rewrite /aLCallcc /= /stS /= /stateT /= /stateTmonadM /=; unlock.
Abort.

Definition usual_callccS (A B : UU0) (f : (A -> stS M B) -> stS M A) : stS M A :=
  fun s k => f (fun x _ _ => k (x, s)) s k.

Lemma callccS_E A B f : @aLCallcc _
    (fun k : stS M A -> r =>
       f (fun x => (fun (_ : S) (_ : B * S -> r) => k (Ret x)) : stS M B)) =
  usual_callccS f.
Proof.
by rewrite /aLCallcc /= /stS /= /stateT /= /stateTmonadM /=; unlock.
Qed.

End continuation_stateT.

End examples_of_algebraic_lifting.

Module ModelMonadStateRun.
Section modelmonadstaterun.
Variable S : UU0.
Let N : monad := [the monad of ExceptMonad.acto unit].
Definition M : stateMonad S := [the stateMonad S of stateT S N].

Let runStateT : forall A : UU0, M A -> S -> N (A * S)%type := fun A : UU0 => id.
Let runStateTret : forall (A : UU0) (a : A) (s : S), @runStateT _ (Ret a) s = Ret (a, s).
Proof. by []. Qed.
Let runStateTbind : forall (A B : UU0) (m : M A) (f : A -> M B) (s : S),
  @runStateT _ (m >>= f) s = @runStateT _ m s >>= fun x => @runStateT _ (f x.1) x.2.
Proof.
move=> A M m f s /=.
rewrite /= /runStateT bindE /= /join_of_bind /bindS /=.
rewrite /actm /= /MS_map /actm /=.
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
Let N : exceptMonad := [the exceptMonad of ExceptMonad.acto unit].
Definition M : stateRunMonad S N := [the stateRunMonad S N of MS S N].

Definition failure : forall A, MS S N A := fun A => liftS (@fail N A).

Let Bindfailf : BindLaws.left_zero (@bind [the monad of MS S N]) failure.
Proof. by []. Qed.

HB.instance Definition _ := @isMonadFail.Build (MS S N) failure Bindfailf.

Let Catch (A : UU0) := mapStateT2 (@catch N (A * S)%type).

Let Catchmfail : forall A, right_id (liftS (@fail N A)) (@Catch A).
Proof.
by move=> A x; rewrite /Catch /mapStateT2; apply fun_ext => s; rewrite catchmfail.
Qed.
Let Catchfailm : forall A, left_id (liftS (@fail N A)) (@Catch A).
Proof.
by move=> A x; rewrite /Catch /mapStateT2; apply fun_ext => s; rewrite catchfailm.
Qed.
Let CatchA : forall A, ssrfun.associative (@Catch A).
Proof.
move=> A; rewrite /Catch /mapStateT2 => a b c; apply fun_ext => s.
by rewrite catchA.
Qed.
Let Catchret : forall A x, @left_zero (M A) (M A) (Ret x) (@Catch A).
Proof.
by move=> A x y; rewrite /Catch /mapStateT2; apply fun_ext => s; rewrite catchret.
Qed.

HB.instance Definition _ :=
  @isMonadExcept.Build (MS S N) Catch Catchmfail Catchfailm CatchA Catchret.

Let RunStateTfail (A : UU0) (s : S) :
  runStateT (@fail [the failMonad of (MS S N)] A) s = @fail N _.
Proof. by []. Qed.
Let RunStateTcatch (A : UU0) (s : S) (m1 m2 : _ A) :
  runStateT (Catch m1 m2) s = catch (runStateT m1 s) (runStateT m2 s).
Proof. by []. Qed.

HB.instance Definition _ := @isMonadExceptStateRun.Build S N (MS S N) RunStateTfail RunStateTcatch.

End modelmonadexceptstaterun.
End ModelMonadExceptStateRun.
