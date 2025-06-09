(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2025 monae authors, license: LGPL-2.1-or-later               *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require boolp.
From HB Require Import structures.
Require Import hierarchy monad_lib Morphisms.
Import Setoid.

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
  DNow : A -> Delay A
| DLater : Delay A -> Delay A.

Local Notation M := Delay.

Let ret : idfun ~~> M := @DNow.
Let bind := fun A B (m : M A) (f : A -> M B) =>
  (cofix bind_ u := match u with
                    | DNow x => f x
                    | DLater m' => DLater (bind_ m')
                    end) m.

Notation "m >>= f" := (bind m f) : monae_scope.

Lemma DelayE (A : UU0) (m : M A) :
  m = match m with
      | DNow x => DNow x
      | DLater m' => DLater m'
      end.
Proof. by case: m. Qed.

Lemma left_neutral : BindLaws.left_neutral bind ret.
Proof. by move=> A B a f; rewrite [LHS]DelayE [RHS]DelayE. Qed.

CoInductive strongBisim (A : UU0) : M A -> M A -> Prop :=
| sBRefl (m : M A) : strongBisim m m
| sBLater (m m' : M A) :
  strongBisim m m' -> strongBisim (DLater m) (DLater m').
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
Proof. move=> *; exact/strongBisim_eq/associative_bisim. Qed.

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
    | DNow a => DNow a
    | DLater da => steps m da
    end
  else x.

Lemma stepsD A n m (x : M A) : steps (m + n) x = steps n (steps m x).
Proof.
elim: m x => //= m IH [a|x].
  by case: n {IH}.
exact: IH.
Qed.

Lemma steps_Dnow A n (a : A) : steps n (DNow a) = DNow a.
Proof. by elim: n => //=. Qed.

Lemma monotonicity_steps' A n (a : A) : forall (x : M A),
  steps n (DLater x) = DNow a -> steps n x = DNow a.
Proof.
elim: n => //= n IH [a'|x'] Ha.
  by rewrite -(steps_Dnow n a').
by apply: (IH x').
Qed.

Lemma monotonicity_steps A (x : M A) (a : A) (n : nat) :
  steps n x = DNow a -> forall m, n <= m -> steps m x = DNow a.
Proof.
move => Hn m.
elim: m => //= [|m IH].
  rewrite leqn0 => /eqP n0.
  by rewrite -Hn n0.
case: x Hn IH => [a'|x'] Ha' IH.
  by rewrite -Ha' -{1}(steps_Dnow n a').
rewrite leq_eqVlt => /predU1P[H| H].
  by rewrite -Ha' H.
exact/monotonicity_steps'/IH.
Qed.

CoFixpoint spin A : M A := DLater (spin A).

Lemma spinE A : DLater (@spin A) = @spin A.
Proof.
apply strongBisim_eq.
cofix IH.
rewrite [X in DLater X]DelayE [X in strongBisim _ X]DelayE /=.
exact/sBLater/IH.
Qed.

Inductive Terminates A : M A -> A -> Prop :=
| TDNow a : Terminates (DNow a) a
| TDLater d a : Terminates d a -> Terminates (DLater d) a.

Lemma Terminates_steps A (d : M A) (a : A) :
  Terminates d a <-> (exists n, steps n d = DNow a).
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
  exact: (TDNow a).
case: d' Hs Hd => [a'|d'] Hs.
  rewrite steps_Dnow => ->.
  exact: (TDNow a).
move=> /= Hd.
apply: TDLater.
case: Hs => m Hs.
apply IH => //.
case: m Hs => [|m] Hs //.
exists m.
by rewrite -Hs.
Qed.

Lemma Terminates_func A (d : M A) (a b : A) :
  Terminates d a -> Terminates d b -> a = b.
Proof.
case/Terminates_steps => n Ha.
case/Terminates_steps => m Hb.
wlog : n m a b Ha Hb/ n <= m.
  have /orP[nm H|nm H] := leqVgt n m.
    exact: (H _ _ _ _ Ha Hb).
  apply/esym/(H _ _ _ _ Hb Ha).
  exact: ltnW.
move => nm.
move: Hb.
by rewrite (monotonicity_steps Ha nm) => -[].
Qed.

Definition Diverges A (d : M A) : Prop := ~ exists a, Terminates d a.

Lemma TerminatesP A (d : M A) : decidable (exists a, Terminates d a).
Proof.
case/boolP: `[< exists a, Terminates d a >].
  by move/asboolP; left.
by move/asboolP; right.
Qed.

Lemma iff_not_Diverges_Terminates A (d : M A) :
  ~ Diverges d <-> (exists a, Terminates d a).
Proof. by split => [| ? ? //]; rewrite notE. Qed.

Lemma Diverges_spinP A (d : M A) : Diverges d <-> d = @spin A.
Proof.
split.
  case: (TerminatesP d) => //= HD _.
  apply strongBisim_eq.
  move: d HD.
  cofix CIH => d HD.
  case: d HD => [a|d'] HD.
    contradict HD.
    exists a.
    exact: TDNow.
  rewrite -spinE.
  apply sBLater.
  apply: CIH => -[a Hd'].
  apply HD.
  exists a.
  exact (TDLater Hd').
move => HD.
rewrite /Diverges {}HD /not.
move => [a /Terminates_steps [n Hs]].
contradict Hs.
elim: n => //=.
by rewrite -spinE.
Qed.

CoInductive wBisim A : M A -> M A -> Prop :=
  | wBTerminate d1 d2 a : Terminates d1 a -> Terminates d2 a -> wBisim d1 d2
  | wBLater d1 d2 : wBisim d1 d2 -> wBisim (DLater d1) (DLater d2).
Local Notation "a '≈' b" := (wBisim a b).

CoFixpoint wBisim_refl A (d : M A) : d ≈ d.
Proof.
case: d => [a|d].
  by apply: wBTerminate; exact: TDNow.
exact: wBLater.
Qed.

Lemma wBisim_sym A : forall (d1 d2 : M A), d1 ≈ d2 -> d2 ≈ d1.
Proof.
cofix CIH.
move => d1 d2.
case: d1.
- case: d2.
  + move => a b H12.
    inversion H12.
    exact: (wBTerminate H0 H).
  + move => d a H12.
    inversion H12.
    exact: (wBTerminate H0 H).
- case: d2.
  + move => a d H12.
    inversion H12.
    exact: (wBTerminate H0 H).
  + move => d1 d2 H12.
    inversion H12.
    * exact: (wBTerminate H0 H).
    * exact: (wBLater (CIH d2 d1 H1)).
Qed.

Lemma Terminates_wBisim A (d1 d2 : M A) (a : A) :
  Terminates d1 a -> d1 ≈ d2 -> Terminates d2 a.
Proof.
move => Ha.
elim: Ha d2 => [a' d2 Ho|d a' Ha IH d2 Ho].
  inversion Ho.
  inversion H.
  by subst.
inversion Ho.
  inversion H.
  subst.
  by rewrite (Terminates_func Ha H4).
apply: TDLater.
exact: IH.
Qed.

Lemma Diverges_wBisim A (d1 d2 : M A) : Diverges d1 -> d1 ≈ d2 -> Diverges d2.
Proof.
move=> + /wBisim_sym Ho [a Ht].
apply.
exists a.
exact: (Terminates_wBisim Ht Ho).
Qed.

CoFixpoint wBisim_trans A (d1 d2 d3 : M A) : d1 ≈ d2 -> d2 ≈ d3 -> d1 ≈ d3.
Proof.
move=> Hd1 Hd2.
case: d1 d2 /Hd1 Hd2 => d1 d2.
  move => a Ht1 Ht2 Hd2.
  apply: (wBTerminate Ht1).
  exact: (Terminates_wBisim Ht2).
move => Hd1 .
inversion 1.
  subst.
  have Hda : Terminates (DLater d1) a.
    apply TDLater.
    inversion H; subst.
    apply: (Terminates_wBisim  H2).
    exact: wBisim_sym.
  exact: (wBTerminate Hda).
exact/wBLater/(wBisim_trans _ _ _ _ Hd1).
Qed.

Add Parametric Relation A : (M A) (@wBisim A)
  reflexivity proved by (@wBisim_refl A)
  symmetry proved by (@wBisim_sym A)
  transitivity proved by (@wBisim_trans A)
  as wBisim_rel.
Hint Extern 0 (wBisim _ _) => setoid_reflexivity.

CoFixpoint wBisim_DLater A (d : M A) : DLater d ≈ d.
Proof.
case: d => [a|d'].
  apply: wBTerminate.
    exact/TDLater/TDNow.
  exact/TDNow.
exact/wBLater/wBisim_DLater.
Qed.

Lemma wBisim_steps A (d : M A) (n : nat) : steps n d ≈ d .
Proof.
elim: n d => [//|n ih] d.
case: d ih => //= d ->.
by rewrite wBisim_DLater.
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

Lemma terminatesP A (a : M A) : decidable (exists c m, steps m a = DNow c).
Proof.
case/boolP : `[< exists c m, steps m a = DNow c >].
  by move/asboolP; left.
by move/asboolP; right.
Qed.

Lemma wBisims_DLater A (d : M A) : DLater d ≈s d.
Proof.
have [[a /Terminates_steps [n Hs]]|/Diverges_spinP Hs] := TerminatesP d.
  exists n.+1.
  by rewrite (monotonicity_steps Hs).
by rewrite Hs spinE.
Qed.

Lemma wBisims_steps A (d : M A) n : steps n d ≈s d .
Proof.
elim: n d => [|n IH] d //.
case: d IH => // d IH /=.
by rewrite IH wBisims_DLater.
Qed.

Lemma Terminates_wBisims A (d1 d2 : M A) (a : A) :
  Terminates d1 a -> d1 ≈s d2 -> Terminates d2 a.
Proof.
elim => [b [n]|d b db ih].
  rewrite steps_Dnow => Hd.
  apply Terminates_steps.
  by exists n.
by rewrite wBisims_DLater.
Qed.

Corollary iff_Terminates_steps {A} (d : M A) n (a : A) :
  Terminates d a <-> Terminates (steps n d) a.
Proof.
split => Ht.
  exact: (Terminates_wBisims Ht (wBisims_sym (wBisims_steps d n))).
exact: (Terminates_wBisims Ht (wBisims_steps d n)).
Qed.

Lemma iff_Terminates_wBret {A} (d : M A) (a : A) :
  Terminates d a <-> (d ≈s Ret a).
Proof.
split.
  elim=> [//|d' a' _ H].
  by rewrite (wBisims_DLater d') H.
move=> [m H].
apply (iff_Terminates_steps d m a).
rewrite H steps_Dnow.
exact: TDNow.
Qed.

Corollary iff_Diverges_steps {A} (d : M A) n :
  Diverges d <-> Diverges (steps n d).
Proof.
apply iff_not2; split.
  move=> [a Ht].
  exists a.
  by apply iff_Terminates_steps.
move => [a Ht].
exists a.
exact/(iff_Terminates_steps _ n _).
Qed.

Lemma iff_Diverges_wBisimspin {A} (d : M A) : Diverges d <-> d ≈ @spin A.
Proof.
split.
  by move=> /Diverges_spinP ->.
move=> Ho [a Ht].
have : Diverges (@spin A) by apply/Diverges_spinP.
apply.
exists a.
exact: (Terminates_wBisim Ht Ho).
Qed.

Lemma iff_Diverges_wBisimsspin {A} (d : M A) : Diverges d <-> d ≈s @spin A.
Proof.
split.
  by move=> /Diverges_spinP ->.
move=> [n Hs].
apply/(iff_Diverges_steps d n).
rewrite Hs.
exact/(iff_Diverges_steps (@spin A) n)/(Diverges_spinP).
Qed.

Theorem iff_wBisims_wBisim A (d1 d2 : M A) : d1 ≈s d2 <-> d1 ≈ d2.
Proof.
split.
  have [[a Ht] Hd|/Diverges_spinP ->] := TerminatesP d1.
    exact: (wBTerminate Ht (Terminates_wBisims Ht Hd)).
  by move=> /wBisims_sym/iff_Diverges_wBisimsspin/Diverges_spinP ->.
have [[a Ht]|/Diverges_spinP ->] := TerminatesP d1.
  move/(Terminates_wBisim Ht).
  move: Ht => /Terminates_steps [n Ht1] /Terminates_steps [m Ht2].
  by rewrite -(wBisims_steps d1 n) -(wBisims_steps d2 m) Ht1 Ht2.
by move/wBisim_sym/iff_Diverges_wBisimspin/Diverges_spinP => ->.
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
                                 | inr a => DLater (while body a)
                                 | inl b => DNow b
                       end).

Lemma whileE A B (f : A -> M (B + A)) (a : A) :
  while f a = f a >>= (fun ab => match ab with
                                 | inr a => DLater (while f a)
                                 | inl b => DNow b
                       end).
Proof.
rewrite [LHS](DelayE) //=.
by case: (f a) => [[b'|a'] | d]; rewrite [RHS]DelayE.
Qed.

Lemma bindDmf A B (m : M A) (f : A -> M B) : DLater m >>= f = DLater (m >>= f).
Proof. by rewrite [LHS]DelayE. Qed.

Lemma Diverges_bindspinf A B (f : A -> M B) : Diverges (@spin A >>= f).
Proof.
apply/Diverges_spinP/strongBisim_eq.
cofix CIH.
rewrite -spinE -(spinE B) bindDmf.
by apply sBLater.
Qed.

Lemma Terminates_bindmf A B (d : M A) (a : A) (f : A -> M B) :
  Terminates d a -> d >>= f ≈s f a.
Proof.
elim => [a'|d' a' Ht Hd'].
  by rewrite bindretf.
by rewrite -Hd' bindDmf wBisims_DLater.
Qed.

Lemma bindmwBs {A B} (f : A -> M B) (d1 d2 : M A) :
  d1 ≈s d2 -> d1 >>= f ≈s d2 >>= f.
Proof.
case: (TerminatesP d1) => [[a Ht1] /(Terminates_wBisims Ht1) Ht2|/Diverges_spinP ->].
  by rewrite (Terminates_bindmf f Ht1) (Terminates_bindmf f Ht2).
by move=> /wBisims_sym/iff_Diverges_wBisimsspin/Diverges_spinP ->.
Qed.

Lemma bindmwB {A B} (f : A -> M B) (d1 d2 : M A) :
  d1 ≈ d2 -> d1 >>= f ≈ d2 >>= f.
Proof.
move=> /iff_wBisims_wBisim H.
apply iff_wBisims_wBisim.
exact: (bindmwBs _ H).
Qed.

Lemma bindfwBs {A B} (f g : A -> M B) (d : M A) :
  (forall a, f a ≈s g a) -> d >>= f ≈s d >>= g.
Proof.
move=> fg.
apply/iff_wBisims_wBisim.
move: d.
cofix CIH => d.
case: d => [a|d].
  rewrite! bindretf.
  by apply iff_wBisims_wBisim.
rewrite !bindDmf.
exact: wBLater.
Qed.

Add Parametric Morphism A B : bind with signature
  (@wBisims A) ==> (pointwise_relation A (@wBisims B)) ==> (@wBisims B)
  as bindmors.
Proof.
move=> x y Hxy f g Hfg.
apply: wBisims_trans.
- exact: (bindmwBs _ Hxy).
- exact: (bindfwBs y Hfg).
Qed.

Lemma bindfwB {A B} (f g : A -> M B) (d : M A) :
  (forall a, f a ≈ g a) -> d >>= f ≈ d >>= g.
Proof.
move=> H.
apply iff_wBisims_wBisim.
apply bindfwBs => a.
exact/iff_wBisims_wBisim/(H a).
Qed.


CoFixpoint whilewBs1 {X A} (f g : X -> M (A + X)) :
  (forall x, f x ≈s g x) ->
  forall d1 d2 : M (A + X),
    d1 ≈s d2 ->
    d1 >>= (fun ax : A + X => match ax with
                              | inl a => DNow a
                              | inr x => DLater (while f x)
                              end) = @spin A ->
    strongBisim (d2 >>= (fun ax : A + X => match ax with
                                           | inl a => DNow a
                                           | inr x => DLater (while g x)
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
    rewrite steps_Dnow steps_Dnow => Hd.
    rewrite -Hd bindretf bindretf -spinE.
    case.
    rewrite whileE whileE => Hf.
    apply sBLater.
    exact: (whilewBs1 _ _ f g Hfg _ _ (Hfg a)).
  move=> Hd Hf.
  rewrite -spinE bindDmf.
  apply sBLater.
  apply: (whilewBs1 _ _ f g Hfg (DNow (inr a)) d2') => //.
  by rewrite Hd wBisims_DLater.
case: d2 =>[[b|a]|d2'] Hd.
- move/Diverges_spinP/iff_Diverges_wBisimsspin.
  rewrite (bindmwBs _ Hd) bindretf => /iff_Diverges_wBisimsspin/Diverges_spinP contr.
  contradict contr.
  by rewrite -spinE.
- set x := (x in DLater d1' >>= x).
  move => Hf.
  rewrite bindretf -spinE whileE.
  apply/sBLater/(whilewBs1 _ _ _ _ Hfg _ _ (Hfg a)).
  rewrite -whileE.
  apply/Diverges_spinP/iff_Diverges_wBisimsspin.
  assert (Hs : (DLater d1' >>= x) ≈s (DNow (inr a) >>= x)).
    by rewrite (bindmwBs _ Hd).
  move: Hs.
  subst x.
  rewrite Hf bindretf.
  move => Hs.
  by rewrite Hs wBisims_DLater.
- move => Hf.
  rewrite -spinE bindDmf.
  apply sBLater.
  apply: (whilewBs1 _ _ f g Hfg (DLater d1') d2') => //.
  by rewrite Hd wBisims_DLater.
Qed.

Lemma whilewBs2 {A B} (d1 d2 : M (B + A)) (f g : A -> M (B + A)) (b : B) :
  (forall a, f a ≈s g a) ->
  d1 ≈s d2 ->
  (d1 >>= (fun ab : B + A => match ab with
                             | inl b => DNow b
                             | inr a => DLater (while f a)
                             end)) ≈s @ret M B b ->
  (d2 >>= (fun ab : B + A => match ab with
                             | inl b => DNow b
                             | inr a => DLater (while g a)
                             end)) ≈s @ret M B b.
Proof.
move => Hfg Hd [n].
move: d1 d2 Hd.
rewrite steps_Dnow.
elim: n => [d1 d2|n IH d1 d2].
  case: d1 => [[b'|a']|d1'].
    rewrite bindretf => /wBisims_sym Hd //= Hf.
    by rewrite (bindmwBs _ Hd) bindretf Hf.
  by rewrite bindretf /= => _ Hf.
  by rewrite bindDmf /= => _ Hf.
case: d1 => [[b'|a']|d1'] H.
- by rewrite bindretf steps_Dnow -(bindmwBs _ H) bindretf => ->.
- rewrite bindretf /= -(bindmwBs _ H) bindretf wBisims_DLater whileE whileE.
  exact: (IH (f a') (g a') (Hfg a')).
- move: H.
  rewrite bindDmf /= wBisims_DLater.
  exact: IH.
Qed.

Lemma whilewBs {A B} (f g : A -> M (B + A)) (a : A) :
  (forall a, (f a) ≈s (g a)) ->
  while f a ≈s while g a.
Proof.
move => Hfg.
have [[b /iff_Terminates_wBret HT]| /Diverges_spinP HD] := TerminatesP (while f a).
  rewrite HT.
  setoid_symmetry.
  move: HT.
  rewrite !whileE.
  exact: (whilewBs2 Hfg (Hfg a)).
- rewrite HD.
  setoid_symmetry.
  apply/iff_Diverges_wBisimsspin/Diverges_spinP/strongBisim_eq.
  move: HD.
  rewrite !whileE.
  exact: (whilewBs1 Hfg (Hfg a)).
Qed.

HB.instance Definition _ := @hasWBisim.Build M wBisim
  wBisim_refl wBisim_sym wBisim_trans (@bindmwB) (@bindfwB).

Add Parametric Morphism A B : bind with signature
  (@wBisim A) ==> (pointwise_relation A (@wBisim B)) ==> (@wBisim B)
  as bindmor.
Proof.
move => x y Hxy f g Hfg.
apply: wBisim_trans.
- exact: (bindmwB _ Hxy).
- exact: (bindfwB y Hfg).
Qed.

(* the next four laws derived from Complete Elgot monads *)
Lemma fixpointEs {A B} (f : A -> M (B + A)) (a : A) :
  while f a ≈s f a >>= sum_rect (fun => M B) (@ret M B) (while f).
Proof.
rewrite whileE.
apply: bindfwBs => -[b'|a'] //=.
exact: wBisims_DLater.
Qed.

Lemma fixpointE {A B} (f : A -> M (B + A)) (a : A) :
  while f a ≈ f a >>= sum_rect (fun => M B) (@ret M B ) (while f).
Proof. by apply iff_wBisims_wBisim; exact: fixpointEs. Qed.

CoFixpoint naturalityE' {A B C} (f : A -> M (B + A)) (g : B -> M C) (d : M (B + A)) :
  (d >>= (fun ab : B + A => match ab with
                            | inl b => DNow b
                            | inr a => DLater (while f a)
                            end)) >>= g
  ≈
  (d >>= sum_rect (fun=> M (C + A)) (M # inl \o g) (M # inr \o (@ret M A))) >>=
   (fun ab : C + A => match ab with
                      | inl b => DNow b
                      | inr a => DLater (while (fun y : A => f y >>= sum_rect (fun=> M (C + A)) (M # inl \o g) (M # inr \o (@ret M A))) a)
                      end).
Proof.
case: d => [[b|a]|d].
- apply iff_wBisims_wBisim.
  rewrite !bindretf /= fmapE bindA.
  have [[c Ht]|/Diverges_spinP HD] := TerminatesP (g b).
    set h := fun x => (Ret \o inl) x >>= _.
    rewrite (Terminates_bindmf h Ht).
    rewrite {}/h /= bindretf.
    move: Ht => /Terminates_steps [n Ht].
    by rewrite -(wBisims_steps (g b) n) Ht.
  rewrite HD.
  setoid_symmetry.
  apply/iff_Diverges_wBisimsspin.
  by apply Diverges_bindspinf.
- rewrite! bindretf /= fmapE bindA bindretf /= bindretf /= bindDmf.
  apply wBLater.
  rewrite whileE whileE.
  exact: naturalityE'.
- rewrite! bindDmf.
  apply wBLater.
  exact: naturalityE'.
Qed.

Lemma naturalityE {A B C} (f : A -> M (B + A)) (g : B -> M C) (a : A) :
  (while f a) >>= g ≈
  while (fun y => f y >>= sum_rect (fun => M (C + A)) (M # inl \o g) (M # inr \o (@ret M A ))) a.
Proof. by rewrite whileE whileE; apply naturalityE'. Qed.

CoFixpoint codiagonalE' {A B} (f: A -> M ((B + A) + A))(d: M ((B + A) + A)) :
  ((d >>= (Ret \o sum_rect (fun=> (B + A)%type) idfun inr)) >>=
  (fun ab : B + A => match ab with
                     | inl b => DNow b
                     | inr a => DLater (while (M # sum_rect (fun=> (B + A)%type) idfun inr \o f) a)
                     end))
  ≈
  ((d >>= (fun ab : B + A + A => match ab with
                                 | inl b => DNow b
                                 | inr a => DLater (while f a)
                                  end)) >>=
   (fun ab : B + A => match ab with
                      | inl b => DNow b
                      | inr a => DLater (while (while f) a)
                      end)).
Proof.
case: d => [ [[b|a]|a]|d'].
- by rewrite bindretf bindretf bindretf //= bindretf.
- rewrite bindretf bindretf bindretf //= bindretf whileE whileE whileE //= fmapE.
  by apply/wBLater/codiagonalE'.
- rewrite bindretf bindretf bindretf //= bindDmf whileE whileE //= fmapE.
  by apply/wBLater/codiagonalE'.
- rewrite! bindDmf.
  apply wBLater.
  exact: codiagonalE'.
Qed.

Lemma codiagonalE {A B} (f : A -> M ((B + A) + A)) (a : A) :
  while ((Delay # ((sum_rect (fun => (B + A)%type) idfun inr))) \o f) a
  ≈
  while (while f) a.
Proof. by rewrite whileE whileE whileE //= fmapE; apply codiagonalE'. Qed.

Lemma whilewB {A B} (f g : A -> M (B + A)) (a : A) :
  (forall a, (f a) ≈ (g a)) ->
  while f a ≈ while g a.
Proof.
move=> H.
apply iff_wBisims_wBisim.
apply whilewBs => a'.
apply iff_wBisims_wBisim.
exact: (H a').
Qed.

Add Parametric Morphism A B : while with signature
  (pointwise_relation A (@wBisim (B + A))) ==> @eq A ==> (@wBisim B )
  as whilemor.
Proof. by move=> f g + a; exact: whilewB. Qed.

Lemma uniformE {A B C} (f : A -> M (B + A)) (g : C -> M (B + C)) (h : C -> A) :
  (forall c, f (h c) = g c >>= sum_rect (fun => M (B + A))
                                        ((M # inl) \o Ret)
                                        ((M # inr) \o Ret \o h)) ->
  forall c, while f (h c) ≈ while g c.
Proof.
move => H c.
rewrite whileE (H c) whileE.
set d := (g c).
move: d.
cofix CIH => d.
case: d => [[b'|c']|d].
- by rewrite !bindretf/= fmapE !bindretf/=.
- rewrite !bindretf/= fmapE !bindretf/=.
  apply: wBLater.
  rewrite whileE whileE H.
  exact: CIH.
- rewrite !bindDmf.
  apply: wBLater.
  exact: CIH.
Qed.

HB.instance Definition _ := @isMonadDelay.Build M (@while)
 (@whilewB) (@fixpointE) (@naturalityE) (@codiagonalE) (@uniformE).

End delayops.
End DelayOps.
HB.export DelayOps.
