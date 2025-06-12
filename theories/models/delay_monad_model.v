(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2025 monae authors, license: LGPL-2.1-or-later               *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require boolp.
From HB Require Import structures.
Require Import hierarchy monad_lib Morphisms.

(**md**************************************************************************)
(* # Model of the Delay monad                                                 *)
(*                                                                            *)
(* Delay monad (Module `DelayMonad`):                                         *)
(* ```                                                                        *)
(*           Delay == action on objects                                       *)
(*     strongBisim == relation between computations in the Delay monad         *)
(*  strongBisim_eq == strongBisim implies equality (admitted)                 *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.

Module DelayMonad.
Section delaymonad.

CoInductive Delay (A : UU0) : Type :=
  Now : A -> Delay A
| Later : Delay A -> Delay A.

Local Notation M := Delay.

Let ret : idfun ~~> M := @Now.

Let bind := fun A B (m : M A) (f : A -> M B) =>
  (cofix bind_ u := match u with
                    | Now x => f x
                    | Later m' => Later (bind_ m')
                    end) m.

Notation "m >>= f" := (bind m f) : monae_scope.

Lemma DelayE (A : UU0) (m : M A) : m = match m with
                                       | Now x => Now x
                                       | Later m' => Later m'
                                       end.
Proof. by case: m. Qed.

Lemma left_neutral : BindLaws.left_neutral bind ret.
Proof. by move=> A B a f; rewrite [LHS]DelayE [RHS]DelayE. Qed.

CoInductive strongBisim (A : UU0) : M A -> M A -> Prop :=
| sBRefl (m : M A) : strongBisim m m
| sBLater (m m' : M A) :
  strongBisim m m' -> strongBisim (Later m) (Later m').
Arguments strongBisim [A].
Arguments sBLater [A].

#[deprecated(since="0.9.1", note = "non standard axiom for strong bisimilarity")]
Axiom strongBisim_eq : forall A (m m' : M A), strongBisim m m' -> m = m'.

CoFixpoint right_neutral_bisim A (m : M A) : strongBisim (m >>= @ret A) m.
Proof.
case: m=> [a|m].
  rewrite [X in strongBisim X]DelayE /=.
  exact: sBRefl.
rewrite [X in strongBisim X]DelayE /=.
apply: sBLater.
exact: right_neutral_bisim.
Qed.

Lemma right_neutral : BindLaws.right_neutral bind ret.
Proof. by move=> *; exact/strongBisim_eq/right_neutral_bisim. Qed.

CoFixpoint associative_bisim A B C (m : M A) (f : A -> M B) (g : B -> M C) :
  strongBisim ((m >>= f) >>= g) (m >>= (fun x => f x >>= g)).
Proof.
case: m=> [a|m].
  rewrite [X in strongBisim _ X]DelayE.
  rewrite [X in strongBisim X]DelayE /=.
  exact: sBRefl.
rewrite [X in strongBisim _ X]DelayE.
rewrite [X in strongBisim X]DelayE.
simpl.
apply: sBLater.
exact: associative_bisim.
Qed.

Lemma associative : BindLaws.associative bind.
Proof. by move=> *; exact/strongBisim_eq/associative_bisim. Qed.

HB.instance Definition _ := isMonad_ret_bind.Build Delay
  left_neutral right_neutral associative.

End delaymonad.
End DelayMonad.
HB.export DelayMonad.

Module DelayOps.
Section delayops.
Import boolp.
Local Notation M := Delay.

Fixpoint steps A n (x : M A) : M A :=
  if n is m.+1 then
    match x with
    | Now a => Now a
    | Later da => steps m da
    end
  else x.

Lemma terminatesP A (a : M A) : decidable (exists c m, steps m a = Now c).
Proof.
case/boolP : `[< exists c m, steps m a = Now c >].
  by move/asboolP; left.
by move/asboolP; right.
Qed.

Lemma stepsD A n m (x : M A) : steps (m + n) x = steps n (steps m x).
Proof.
elim: m x => //= m IH [a|x].
  by case: n {IH}.
exact: IH.
Qed.

Lemma steps_Now A n (a : A) : steps n (Now a) = Now a.
Proof. by case: n. Qed.

Lemma monotonicity_steps' A n (a : A) : forall x : M A,
  steps n (Later x) = Now a -> steps n x = Now a.
Proof.
elim: n => //= n IH [a'|x'] Ha.
  by rewrite -(steps_Now n a').
exact: IH.
Qed.

Lemma monotonicity_steps A (x : M A) a n :
  steps n x = Now a -> forall m, n <= m -> steps m x = Now a.
Proof.
move => Hn m.
elim: m => //= [|m IH].
  rewrite leqn0 => /eqP n0.
  by rewrite -Hn n0.
case: x Hn IH => [a'|x'] Ha' IH.
  by rewrite -Ha' -{1}(steps_Now n a').
rewrite leq_eqVlt => /predU1P[H| H].
  by rewrite -Ha' H.
exact/monotonicity_steps'/IH.
Qed.

CoFixpoint spin A : M A := Later (spin A).

Lemma spinE A : Later (@spin A) = @spin A.
Proof.
apply strongBisim_eq.
cofix IH.
rewrite [X in Later X]DelayE [X in strongBisim _ X]DelayE /=.
exact/sBLater/IH.
Qed.

Inductive Terminate (A : UU0) : M A -> A -> Prop :=
| Terminate_Now a : Terminate (Now a) a
| Terminate_Later d a : Terminate d a -> Terminate (Later d) a.

Lemma Now_Terminate (A : UU0) (a b : A) : Terminate (Now a) b -> a = b.
Proof. by inversion 1. Qed.

Lemma Later_Terminate (A : UU0) (a : M A) b :
  Terminate (Later a) b -> Terminate a b.
Proof. by inversion 1. Qed.

Lemma Terminate_steps A (d : M A) a :
  Terminate d a <-> exists n, steps n d = Now a.
Proof.
split => [Ht|Hda].
  elim: Ht => [a'|d' a' IH1] /=.
    by exists 0.
  move=> [n IH2].
  by exists n.+1.
case: (Hda) => m H.
move: d Hda H.
elim: m => [d Hda /= Hs|n IH d' Hs Hd].
  rewrite Hs.
  exact: Terminate_Now.
case: d' Hs Hd => [a'|d'] Hs.
  rewrite steps_Now => ->.
  exact: Terminate_Now.
move=> /= Hd.
apply: Terminate_Later.
case: Hs => m Hs.
apply IH => //.
case: m Hs => [|m] Hs //.
exists m.
by rewrite -Hs.
Qed.

Lemma Terminate_fun A (d : M A) (a b : A) :
  Terminate d a -> Terminate d b -> a = b.
Proof.
case/Terminate_steps => n Ha.
case/Terminate_steps => m Hb.
wlog : n m a b Ha Hb/ n <= m.
  have /orP[nm H|nm H] := leqVgt n m.
    exact: (H _ _ _ _ Ha Hb).
  apply/esym/(H _ _ _ _ Hb Ha).
  exact: ltnW.
move => nm.
move: Hb.
by rewrite (monotonicity_steps Ha nm) => -[].
Qed.

Definition Diverge A (d : M A) : Prop := ~ exists a, Terminate d a.

Lemma TerminateP A (d : M A) : decidable (exists a, Terminate d a).
Proof.
case/boolP: `[< exists a, Terminate d a >].
  by move/asboolP; left.
by move/asboolP; right.
Qed.

Lemma not_DivergeP A (d : M A) : ~ Diverge d <-> exists a, Terminate d a.
Proof. by split => [| ? ? //]; rewrite notE. Qed.

Lemma Diverge_spinP A (d : M A) : Diverge d <-> d = @spin A.
Proof.
split.
  case: (TerminateP d) => //= HD _.
  apply strongBisim_eq.
  move: d HD.
  cofix CIH => d HD.
  case: d HD => [a|d'] HD.
    contradict HD.
    exists a.
    exact: Terminate_Now.
  rewrite -spinE.
  apply sBLater.
  apply: CIH => -[a Hd'].
  apply HD.
  exists a.
  exact (Terminate_Later Hd').
move => HD.
rewrite /Diverge {}HD /not.
move => [a /Terminate_steps [n Hs]].
contradict Hs.
elim: n => //=.
by rewrite -spinE.
Qed.

CoInductive wBisim A : M A -> M A -> Prop :=
  | wBTerminate d1 d2 a : Terminate d1 a -> Terminate d2 a -> d1 ≈ d2
  | wBLater d1 d2 : d1 ≈ d2 -> Later d1 ≈ Later d2
where "a '≈' b" := (wBisim a b).

Lemma Now_wBisim {A : UU0} {a : A} b : Now a ≈ b ->
  exists2 c, Terminate (Now a) c & Terminate b c.
Proof. by inversion 1; exists a0. Qed.

Lemma Later_wBisim {A : UU0} {a : M A} b : Later a ≈ b ->
  (exists2 c, Terminate (Later a) c & Terminate b c) \/
  (exists2 c, b = Later c & a ≈ c).
Proof. by inversion 1; [left; exists a0 => //|right; exists d2]. Qed.

CoFixpoint wBisim_refl A (d : M A) : d ≈ d.
Proof.
case: d => [a|d].
  by apply: wBTerminate; exact: Terminate_Now.
exact: wBLater.
Qed.

Lemma wBisim_sym A : forall d1 d2 : M A, d1 ≈ d2 -> d2 ≈ d1.
Proof.
cofix CIH.
move=> [a [b|b]|b [a|a]].
- by move/Now_wBisim => [c] /[swap]; exact: wBTerminate.
- by move/Now_wBisim => [c] /[swap]; exact: wBTerminate.
- by move/Later_wBisim => [[c]|[//]] /[swap]; exact: wBTerminate.
- move/Later_wBisim => [[c] /[swap]|[c -> /CIH cb]].
  + exact: wBTerminate.
  + exact: wBLater.
Qed.

Lemma Terminate_wBisim A (d1 d2 : M A) a :
  Terminate d1 a -> d1 ≈ d2 -> Terminate d2 a.
Proof.
move=> d1a; elim: d1a d2 => [b d2|d a' Ha IH d2].
  move/Now_wBisim => [c] /[swap] d2c bc.
  by rewrite (Now_Terminate bc).
move/Later_wBisim => [[c dc]|[c ->{d2} dc]].
  have {}dc := Later_Terminate dc.
  by rewrite (Terminate_fun Ha dc).
exact/Terminate_Later/IH.
Qed.

Lemma Diverge_wBisim A (d1 d2 : M A) : Diverge d1 -> d1 ≈ d2 -> Diverge d2.
Proof.
move=> + /wBisim_sym Ho [a Ht].
apply.
exists a.
exact: (Terminate_wBisim Ht Ho).
Qed.

CoFixpoint wBisim_trans A (d1 d2 d3 : M A) : d1 ≈ d2 -> d2 ≈ d3 -> d1 ≈ d3.
Proof.
case => [{}d1 {}d2 a d1a d2a d2d3|{}d1 {}d2 d1d2].
  exact/(wBTerminate d1a)/(Terminate_wBisim d2a).
move=> /Later_wBisim[[c d2c] d3c|[c ->{d3} d2c]].
  have {}d2c := Later_Terminate d2c.
  have d1c : Terminate (Later d1) c.
    exact/Terminate_Later/(Terminate_wBisim d2c)/wBisim_sym.
  exact: (wBTerminate d1c).
exact/wBLater/(wBisim_trans _ _ _ _ d1d2).
Qed.

Add Parametric Relation A : (M A) (@wBisim A)
  reflexivity proved by (@wBisim_refl A)
  symmetry proved by (@wBisim_sym A)
  transitivity proved by (@wBisim_trans A)
  as wBisim_rel.
Hint Extern 0 (wBisim _ _) => setoid_reflexivity.

CoFixpoint wBisim_Later A (d : M A) : Later d ≈ d.
Proof.
case: d => [a|d'].
  apply: wBTerminate.
    exact/Terminate_Later/Terminate_Now.
  exact/Terminate_Now.
exact/wBLater/wBisim_Later.
Qed.

Lemma wBisim_steps A (d : M A) (n : nat) : steps n d ≈ d.
Proof.
elim: n d => [//|n ih] d.
case: d ih => //= d ->.
by rewrite wBisim_Later.
Qed.

Definition wBisims (A : UU0) (d1 d2 : M A) : Prop :=
  exists n, steps n d1 = steps n d2.
Local Notation "a '≈s' b" := (wBisims a b) (at level 70).

Lemma wBisims_refl A (a : M A) : a ≈s a.
Proof. by exists 0. Qed.

Lemma wBisims_sym A (d1 d2 : M A) : d1 ≈s d2 -> d2 ≈s d1.
Proof. by move=> [n Hs];  exists n. Qed.

Lemma wBisims_trans A (d1 d2 d3 : M A) : d1 ≈s d2 -> d2 ≈s d3 -> d1 ≈s d3.
Proof.
move=> [n Hs1] [m Hs2].
exists (n + m).
by rewrite stepsD Hs1 addnC stepsD -Hs2 -stepsD -stepsD addnC.
Qed.

Add Parametric Relation A : (M A) (@wBisims A)
  reflexivity proved by (@wBisims_refl A)
  symmetry proved by (@wBisims_sym A)
  transitivity proved by (@wBisims_trans A)
  as wBisims_rel.
Hint Extern 0 (wBisims _ _) => setoid_reflexivity.

Lemma wBisims_Later A (d : M A) : Later d ≈s d.
Proof.
have [[a /Terminate_steps [n Hs]]|/Diverge_spinP Hs] := TerminateP d.
  exists n.+1.
  by rewrite (monotonicity_steps Hs).
by rewrite Hs spinE.
Qed.

Lemma wBisims_steps A (d : M A) n : steps n d ≈s d .
Proof.
elim: n d => [|n IH] d //.
case: d IH => // d IH /=.
by rewrite IH wBisims_Later.
Qed.

Lemma Terminate_wBisims A (d1 d2 : M A) (a : A) :
  Terminate d1 a -> d1 ≈s d2 -> Terminate d2 a.
Proof.
elim => [b [n]|d b db ih].
  rewrite steps_Now => Hd.
  apply Terminate_steps.
  by exists n.
by rewrite wBisims_Later.
Qed.

Corollary Terminate_stepsP {A} (d : M A) n (a : A) :
  Terminate d a <-> Terminate (steps n d) a.
Proof.
split => Ht.
  exact: (Terminate_wBisims Ht (wBisims_sym (wBisims_steps d n))).
exact: (Terminate_wBisims Ht (wBisims_steps d n)).
Qed.

Lemma Terminate_wBisimsRet {A} (d : M A) (a : A) : Terminate d a <-> d ≈s Ret a.
Proof.
split.
  elim=> [//|d' a' _ H].
  by rewrite (wBisims_Later d') H.
move=> [m H].
apply/(Terminate_stepsP d m a).
rewrite H steps_Now.
exact: Terminate_Now.
Qed.

Corollary Diverge_stepsP {A} (d : M A) n : Diverge d <-> Diverge (steps n d).
Proof.
apply iff_not2; split.
  move=> [a Ht].
  exists a.
  by apply Terminate_stepsP.
move=> [a Ht].
exists a.
exact/(Terminate_stepsP _ n _).
Qed.

Lemma Diverge_wBisim_spinP {A} (d : M A) : Diverge d <-> d ≈ @spin A.
Proof.
split.
  by move=> /Diverge_spinP ->.
move=> Ho [a Ht].
have : Diverge (@spin A) by apply/Diverge_spinP.
apply.
exists a.
exact: (Terminate_wBisim Ht Ho).
Qed.

Lemma Diverge_wBisims_spinP {A} (d : M A) : Diverge d <-> d ≈s @spin A.
Proof.
split.
  by move=> /Diverge_spinP ->.
move=> [n Hs].
apply/(Diverge_stepsP d n).
rewrite Hs.
exact/(Diverge_stepsP (@spin A) n)/(Diverge_spinP).
Qed.

Theorem wBisims_wBisim A (d1 d2 : M A) : d1 ≈s d2 <-> d1 ≈ d2.
Proof.
split.
  have [[a Ht] Hd|/Diverge_spinP ->] := TerminateP d1.
    exact: (wBTerminate Ht (Terminate_wBisims Ht Hd)).
  by move=> /wBisims_sym/Diverge_wBisims_spinP/Diverge_spinP ->.
have [[a Ht]|/Diverge_spinP ->] := TerminateP d1.
  move/(Terminate_wBisim Ht).
  move: Ht => /Terminate_steps [n Ht1] /Terminate_steps [m Ht2].
  by rewrite -(wBisims_steps d1 n) -(wBisims_steps d2 m) Ht1 Ht2.
by move/wBisim_sym/Diverge_wBisim_spinP/Diverge_spinP => ->.
Qed.
(*
Lemma steps_bind {A B} (n : nat) (m : M A) (f : A -> M B) : steps n (m >>= f) ≈s  m >>= ((steps n) \o f).
Abort.
Lemma steps_ret {A} (n:nat) (a : A) : steps n (@ret M A a) ≈s @ret M A a.
Abort.
Lemma steps_monotonisity {A} (n : nat) (d : Delay A) : steps n d  ≈s d.
Abort.
*)

CoFixpoint while {A B} (body : A -> M (B + A)) : A -> M B :=
  fun a => body a >>= (fun ab => match ab with
                                 | inr a => Later (while body a)
                                 | inl b => Now b
                       end).

Lemma whileE A B (f : A -> M (B + A)) (a : A) :
  while f a = f a >>= (fun ab => match ab with
                                 | inr a => Later (while f a)
                                 | inl b => Now b
                       end).
Proof.
rewrite [LHS](DelayE) //=.
by case: (f a) => [[b'|a'] | d]; rewrite [RHS]DelayE.
Qed.

Lemma bind_Later A B (m : M A) (f : A -> M B) : Later m >>= f = Later (m >>= f).
Proof. by rewrite [LHS]DelayE. Qed.

Lemma Diverge_bindspinf A B (f : A -> M B) : Diverge (@spin A >>= f).
Proof.
apply/Diverge_spinP/strongBisim_eq.
cofix CIH.
rewrite -spinE -(spinE B) bind_Later.
exact: sBLater.
Qed.

Lemma Terminate_bindmf A B (d : M A) (a : A) (f : A -> M B) :
  Terminate d a -> d >>= f ≈s f a.
Proof.
elim => [a'|d' a' Ht Hd'].
  by rewrite bindretf.
by rewrite -Hd' bind_Later wBisims_Later.
Qed.

Lemma bindmwBisims {A B} (f : A -> M B) (d1 d2 : M A) :
  d1 ≈s d2 -> d1 >>= f ≈s d2 >>= f.
Proof.
case: (TerminateP d1) => [[a d1a] /(Terminate_wBisims d1a) Ht2|/Diverge_spinP ->].
  by rewrite (Terminate_bindmf f d1a) (Terminate_bindmf f Ht2).
by move=> /wBisims_sym/Diverge_wBisims_spinP/Diverge_spinP ->.
Qed.

Lemma bindmwBisim {A B} (f : A -> M B) (d1 d2 : M A) :
  d1 ≈ d2 -> d1 >>= f ≈ d2 >>= f.
Proof.
move=> /wBisims_wBisim H.
exact/wBisims_wBisim/bindmwBisims.
Qed.

Lemma bindfwBisims {A B} (f g : A -> M B) (d : M A) :
  (forall a, f a ≈s g a) -> d >>= f ≈s d >>= g.
Proof.
move=> fg.
apply/wBisims_wBisim.
move: d.
cofix CIH => d.
case: d => [a|d].
  rewrite! bindretf.
  by apply wBisims_wBisim.
rewrite !bind_Later.
exact: wBLater.
Qed.

Add Parametric Morphism A B : bind with signature
  (@wBisims A) ==> (pointwise_relation A (@wBisims B)) ==> (@wBisims B)
  as bind_mors.
Proof.
move=> x y Hxy f g Hfg.
apply: wBisims_trans.
- exact: (bindmwBisims _ Hxy).
- exact: (bindfwBisims y Hfg).
Qed.

Lemma bindfwB {A B} (f g : A -> M B) (d : M A) :
  (forall a, f a ≈ g a) -> d >>= f ≈ d >>= g.
Proof.
move=> H.
apply wBisims_wBisim.
apply bindfwBisims => a.
exact/wBisims_wBisim/(H a).
Qed.

CoFixpoint whilewBs1 {X A} (f g : X -> M (A + X)) :
  (forall x, f x ≈s g x) ->
  forall d1 d2 : M (A + X),
    d1 ≈s d2 ->
    d1 >>= (fun ax : A + X => match ax with
                              | inl a => Now a
                              | inr x => Later (while f x)
                              end) = @spin A ->
    strongBisim (d2 >>= (fun ax : A + X => match ax with
                                           | inl a => Now a
                                           | inr x => Later (while g x)
                                           end))
                (@spin A).
Proof.
move => Hfg d1 d2.
case: d1 => [[b|a]|d1'].
- move => _ contr.
  contradict contr.
  by rewrite bindretf -spinE.
- case: d2 => [ba|d2'].
    move=> [n].
    rewrite steps_Now steps_Now => Hd.
    rewrite -Hd bindretf bindretf -spinE.
    case.
    rewrite whileE whileE => Hf.
    apply sBLater.
    exact: (whilewBs1 _ _ f g Hfg _ _ (Hfg a)).
  move=> Hd Hf.
  rewrite -spinE bind_Later.
  apply sBLater.
  apply: (whilewBs1 _ _ f g Hfg (Now (inr a)) d2') => //.
  by rewrite Hd wBisims_Later.
case: d2 =>[[b|a]|d2'] Hd.
- move/Diverge_spinP/Diverge_wBisims_spinP.
  rewrite (bindmwBisims _ Hd) bindretf => /Diverge_wBisims_spinP/Diverge_spinP contr.
  contradict contr.
  by rewrite -spinE.
- set x := (x in Later d1' >>= x).
  move => Hf.
  rewrite bindretf -spinE whileE.
  apply/sBLater/(whilewBs1 _ _ _ _ Hfg _ _ (Hfg a)).
  rewrite -whileE.
  apply/Diverge_spinP/Diverge_wBisims_spinP.
  assert (Hs : (Later d1' >>= x) ≈s (Now (inr a) >>= x)).
    by rewrite (bindmwBisims _ Hd).
  move: Hs.
  subst x.
  rewrite Hf bindretf.
  move => Hs.
  by rewrite Hs wBisims_Later.
- move => Hf.
  rewrite -spinE bind_Later.
  apply: sBLater.
  apply: (whilewBs1 _ _ f g Hfg (Later d1') d2') => //.
  by rewrite Hd wBisims_Later.
Qed.

Lemma whilewBs2 {A B} (d1 d2 : M (B + A)) (f g : A -> M (B + A)) (b : B) :
  (forall a, f a ≈s g a) ->
  d1 ≈s d2 ->
  (d1 >>= (fun ab : B + A => match ab with
                             | inl b => Now b
                             | inr a => Later (while f a)
                             end)) ≈s @ret M B b ->
  (d2 >>= (fun ab : B + A => match ab with
                             | inl b => Now b
                             | inr a => Later (while g a)
                             end)) ≈s @ret M B b.
Proof.
move => Hfg Hd [n].
move: d1 d2 Hd.
rewrite steps_Now.
elim: n => [d1 d2|n IH d1 d2].
  case: d1 => [[b'|a']|d1'].
    rewrite bindretf => /wBisims_sym Hd //= Hf.
    by rewrite (bindmwBisims _ Hd) bindretf Hf.
  by rewrite bindretf /= => _ Hf.
  by rewrite bind_Later /= => _ Hf.
case: d1 => [[b'|a']|d1'] H.
- by rewrite bindretf steps_Now -(bindmwBisims _ H) bindretf => ->.
- rewrite bindretf /= -(bindmwBisims _ H) bindretf wBisims_Later whileE whileE.
  exact: (IH (f a') (g a') (Hfg a')).
- move: H.
  rewrite bind_Later /= wBisims_Later.
  exact: IH.
Qed.

Lemma whilewBs {A B} (f g : A -> M (B + A)) (a : A) :
  (forall a, (f a) ≈s (g a)) ->
  while f a ≈s while g a.
Proof.
move => Hfg.
have [[b /Terminate_wBisimsRet HT]|/Diverge_spinP HD] := TerminateP (while f a).
  rewrite HT.
  setoid_symmetry.
  move: HT.
  rewrite !whileE.
  exact: (whilewBs2 Hfg (Hfg a)).
- rewrite HD.
  setoid_symmetry.
  apply/Diverge_wBisims_spinP/Diverge_spinP/strongBisim_eq.
  move: HD.
  rewrite !whileE.
  exact: (whilewBs1 Hfg (Hfg a)).
Qed.

HB.instance Definition _ := @hasWBisim.Build M wBisim
  wBisim_refl wBisim_sym wBisim_trans (@bindmwBisim) (@bindfwB).

Add Parametric Morphism A B : bind with signature
  (@wBisim A) ==> (pointwise_relation A (@wBisim B)) ==> (@wBisim B)
  as bind_mor.
Proof.
move => x y Hxy f g Hfg.
apply: wBisim_trans.
- exact: (bindmwBisim _ Hxy).
- exact: (bindfwB y Hfg).
Qed.

(* the next four laws derived from Complete Elgot monads *)
Lemma fixpointEs {A B} (f : A -> M (B + A)) (a : A) :
  while f a ≈s f a >>= sum_rect (fun => M B) (@ret M B) (while f).
Proof.
rewrite whileE.
apply: bindfwBisims => -[b'|a'] //=.
exact: wBisims_Later.
Qed.

Lemma fixpointE {A B} (f : A -> M (B + A)) (a : A) :
  while f a ≈ f a >>= sum_rect (fun => M B) (@ret M B ) (while f).
Proof. by apply wBisims_wBisim; exact: fixpointEs. Qed.

CoFixpoint naturalityE' {A B C} (f : A -> M (B + A)) (g : B -> M C) (d : M (B + A)) :
  (d >>= (fun ab : B + A => match ab with
                            | inl b => Now b
                            | inr a => Later (while f a)
                            end)) >>= g
  ≈
  (d >>= sum_rect (fun=> M (C + A)) (M # inl \o g) (M # inr \o (@ret M A))) >>=
   (fun ab : C + A => match ab with
                      | inl b => Now b
                      | inr a => Later (while (fun y : A => f y >>= sum_rect (fun=> M (C + A)) (M # inl \o g) (M # inr \o (@ret M A))) a)
                      end).
Proof.
case: d => [[b|a]|d].
- apply wBisims_wBisim.
  rewrite !bindretf /= fmapE bindA.
  have [[c Ht]|/Diverge_spinP HD] := TerminateP (g b).
    set h := fun x => (Ret \o inl) x >>= _.
    rewrite (Terminate_bindmf h Ht).
    rewrite {}/h /= bindretf.
    move: Ht => /Terminate_steps [n Ht].
    by rewrite -(wBisims_steps (g b) n) Ht.
  rewrite HD.
  setoid_symmetry.
  exact/Diverge_wBisims_spinP/Diverge_bindspinf.
- rewrite! bindretf /= fmapE bindA bindretf /= bindretf /= bind_Later.
  apply wBLater.
  rewrite whileE whileE.
  exact: naturalityE'.
- rewrite !bind_Later.
  apply: wBLater.
  exact: naturalityE'.
Qed.

Lemma naturalityE {A B C} (f : A -> M (B + A)) (g : B -> M C) (a : A) :
  (while f a) >>= g ≈
  while (fun y => f y >>= sum_rect (fun => M (C + A)) (M # inl \o g) (M # inr \o (@ret M A ))) a.
Proof. by rewrite whileE whileE; apply naturalityE'. Qed.

CoFixpoint codiagonalE' {A B} (f: A -> M ((B + A) + A))(d: M ((B + A) + A)) :
  ((d >>= (Ret \o sum_rect (fun=> (B + A)%type) idfun inr)) >>=
  (fun ab : B + A => match ab with
                     | inl b => Now b
                     | inr a => Later (while (M # sum_rect (fun=> (B + A)%type) idfun inr \o f) a)
                     end))
  ≈
  ((d >>= (fun ab : B + A + A => match ab with
                                 | inl b => Now b
                                 | inr a => Later (while f a)
                                  end)) >>=
   (fun ab : B + A => match ab with
                      | inl b => Now b
                      | inr a => Later (while (while f) a)
                      end)).
Proof.
case: d => [ [[b|a]|a]|d'].
- by rewrite bindretf bindretf bindretf //= bindretf.
- rewrite bindretf bindretf bindretf //= bindretf whileE whileE whileE //= fmapE.
  exact/wBLater/codiagonalE'.
- rewrite bindretf bindretf bindretf //= bind_Later whileE whileE //= fmapE.
  exact/wBLater/codiagonalE'.
- rewrite !bind_Later.
  apply: wBLater.
  exact: codiagonalE'.
Qed.

Lemma codiagonalE {A B} (f : A -> M ((B + A) + A)) (a : A) :
  while ((Delay # ((sum_rect (fun => (B + A)%type) idfun inr))) \o f) a
  ≈
  while (while f) a.
Proof. by rewrite whileE whileE whileE //= fmapE; apply codiagonalE'. Qed.

Lemma whilewB {A B} (f g : A -> M (B + A)) (a : A) :
  (forall a, f a ≈ g a) -> while f a ≈ while g a.
Proof.
move=> H.
apply wBisims_wBisim.
apply whilewBs => a'.
apply wBisims_wBisim.
exact: H.
Qed.

Add Parametric Morphism A B : while with signature
  (pointwise_relation A (@wBisim (B + A))) ==> @eq A ==> (@wBisim B)
  as while_mor.
Proof. by move=> f g + a; exact: whilewB. Qed.

Lemma steps_bind A B (m : M A) (f : A -> M B) b n1 :
  steps n1 (m >>= f) = Now b ->
  exists a n2, steps n2 m = Now a /\ steps (n1 - n2) (f a) = Now b.
Proof.
elim: n1 m => [|n1 IH] [a|m] /=.
- rewrite bindretf => fa.
  by exists a, 0.
- by rewrite bind_Later.
- move=> Hfa.
  by exists a, 0.
- move=> /IH[a [n2]].
  exists a, n2.+1.
  by rewrite subSS.
Qed.

Lemma steps_bindD A B (m : M A) (f : A -> M B) n1 n2 a b :
  steps n1 m = Now a -> steps n2 (f a) = Now b ->
  steps (n1 + n2) (m >>= f) = Now b.
Proof.
elim: n1 m => /= [m ->|n1 IH [a' [] ->|m']].
    by rewrite bindretf.
  move=> Hfa.
  have := monotonicity_steps Hfa (m:=(n1 + n2).+1).
  apply.
  by rewrite -addSn leq_addl.
move=> Ha Hb.
by apply: IH.
Qed.

Lemma uniformE {A B C} (f : A -> M (B + A)) (g : C -> M (B + C)) (h : C -> A) :
  (forall c, f (h c) ≈ g c >>= sum_rect (fun => M (B + A))
                                        ((M # inl) \o Ret)
                                        ((M # inr) \o Ret \o h)) ->
  forall c, while f (h c) ≈ while g c.
Proof.
move => H c.
case: (TerminateP (while g c)).
  case => b Tgb.
  suff Tfb : Terminate (while f (h c)) b.
    exact/wBTerminate/Tgb.
  case/Terminate_steps: Tgb => n.
  elim/ltn_ind: n c b => n IH c b.
  rewrite whileE whileE.
  move=> Hsteps.
  have [a [n2] [Hg Ha]] := steps_bind Hsteps.
  move/wBisim_sym: (H c).
  set gch := g c >>= _.
  have Tgch : Terminate gch
              (match a with inl b => inl b | inr a => inr (h a) end).
    apply/Terminate_steps.
    exists n2.
    rewrite /gch -(addn0 n2).
    apply: (steps_bindD Hg).
    by case a => a' /= ; rewrite fmapE bindretf.
  move/(Terminate_wBisim Tgch).
  clear gch Tgch.
  case/Terminate_steps => n1 Tfhc.
  destruct a as [b'|a].
    apply/Terminate_steps.
    exists (n1 + 0).
    apply: (steps_bindD Tfhc).
    by rewrite -Ha !steps_Now.
  have Hnn2 : n - n2 > 0 by case: (n - n2) Ha.
  rewrite -(prednK Hnn2) /= in Ha.
  have Hn : (n - n2).-1 < n by rewrite prednK // leq_subr.
  have := IH _ Hn _ _ Ha.
  case/Terminate_steps => n3 Hwf.
  apply/Terminate_steps.
  exists (n1 + n3.+1).
  exact: (steps_bindD Tfhc).
move=> Twgc.
case: (TerminateP (while f (h c))); last first.
  move/Diverge_spinP ->.
  by move/Diverge_spinP: Twgc => ->.
case=> b Twfh.
elim: Twgc.
case/Terminate_steps: Twfh => n.
elim/ltn_ind: n c b => n IH c b.
rewrite whileE whileE.
move=> Hsteps.
have [a [n2] [Hg Ha]] := steps_bind Hsteps.
have Tfhc : Terminate (f (h c)) a.
  apply/Terminate_steps.
  by exists n2.
move: (H c).
move/(Terminate_wBisim Tfhc).
case/Terminate_steps => n1 Tgc.
have [[b'|a'] [n3] [] /= Hgc] := steps_bind Tgc.
  rewrite fmapE bindretf /= steps_Now => -[] Hb'.
  exists b'.
  apply/Terminate_steps.
  exists (n3 + 0).
  exact: (steps_bindD Hgc).
rewrite fmapE bindretf /= steps_Now => -[] Hha'.
rewrite -Hha' in Ha.
have Hnn2 : n - n2 > 0 by case: (n - n2) Ha.
rewrite -(prednK Hnn2) /= in Ha.
have Hn : (n - n2).-1 < n by rewrite prednK // leq_subr.
have [b'] := IH _ Hn _ _ Ha.
case/Terminate_steps => n4 Hwg.
exists b'.
apply/Terminate_steps.
exists (n3 + n4.+1).
exact: (steps_bindD Hgc).
Qed.

HB.instance Definition _ := @isMonadDelay.Build M (@while)
 (@whilewB) (@fixpointE) (@naturalityE) (@codiagonalE) (@uniformE).

End delayops.
End DelayOps.
HB.export DelayOps.
