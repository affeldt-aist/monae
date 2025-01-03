From mathcomp Require Import all_ssreflect.
From mathcomp Require boolp.
From HB Require Import structures.
Require Import hierarchy monad_lib.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.

Module DelayMonad.
Section delaymonad.

CoInductive Delay (A : UU0) : Type := DNow : A -> Delay A | DLater : Delay A -> Delay A.
Local Notation M := Delay.
Let ret : idfun ~~> M := @DNow.
Let bind := fun A B (m : M A) (f: A -> M B) =>
              (cofix bind_ u := match u with
                                | DNow x => f x
                                | DLater m' => DLater (bind_ m')
                                end) m.
Lemma DelayE (A : UU0) (m : M A) :
  m = match m with
      | DNow x => DNow x
      | DLater m' => DLater m'
      end.
Proof. by case: m. Qed.
Lemma left_neutral : BindLaws.left_neutral bind ret.
Proof. by move=> A B a f; rewrite [LHS]DelayE [RHS]DelayE. Qed.
CoInductive strongBisim (A : UU0) : M A -> M A -> Prop :=
| sBRefl (m : M A) : @strongBisim A m m
| sBLater (m m' : M A) :
  @strongBisim A m m' -> @strongBisim A (DLater m) (DLater m').
Arguments strongBisim [A].
Arguments sBLater [A].
Axiom strongBisim_eq : forall A (m m' : M A), strongBisim m m' -> m = m'.
CoFixpoint right_neutral_bisim A (m : M A) : strongBisim (bind m (@ret A)) m.
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
  strongBisim (bind (bind m f) g) (bind m (fun x => bind (f x) g)).
Proof.
case: m=> [a|m].
  rewrite [X in strongBisim _ X]DelayE.
  rewrite [X in strongBisim X]DelayE.
  simpl.
  exact: sBRefl.
rewrite [X in strongBisim _ X]DelayE.
rewrite [X in strongBisim X]DelayE.
simpl.
apply: sBLater.
exact: associative_bisim.
Qed.
Lemma associative : BindLaws.associative bind.
Proof. move=> *; exact/strongBisim_eq/associative_bisim. Qed.
HB.instance Definition _ := isMonad_ret_bind.Build
                              Delay left_neutral right_neutral associative.
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
elim: m x => //=.
move => m IH [a | x].
- by elim: n {IH}.
- by apply IH.
Qed.
Lemma steps_Dnow A n (a : A) : steps n (DNow a) = DNow a.
Proof. by elim: n => //=. Qed.
Lemma monotonicity_steps' A n (a : A) : forall (x : M A), steps n (DLater x) = DNow a -> steps n x = DNow a.
Proof.
elim: n => //=.
move => n IH //= x.
case: x IH.
- move => a0 IH Ha.
  by rewrite steps_Dnow in Ha.
- move => d IH Ha.
  apply (IH d).
  by apply Ha.
Qed.

Lemma monotonicity_steps A (x : M A) (a : A) (n : nat) :  steps n x = DNow a -> forall m, n <= m -> steps m x = DNow a.
Proof.
move => Hn m.
elim: m => //=.
- rewrite leqn0.
  move => /eqP Hnm.
  rewrite Hnm in Hn.
  move: Hn => Hn //=.
- move => m IH.
  case: x Hn IH => a0 Ha Hm.
  + case: n Ha Hm => //=.
  + rewrite leq_eqVlt => /orP [/eqP H| H].
    * by rewrite H in Ha.
    * apply Hm in H.
      by apply monotonicity_steps'.
Qed.
CoFixpoint spin A : M A  := DLater (spin A).
Lemma spinE A: DLater (@spin A) = (@spin A).
Proof.
apply strongBisim_eq.
cofix IH.
rewrite [X in DLater X]DelayE [X in strongBisim _ X]DelayE /=.
exact/sBLater/IH.
Qed.
Inductive Terminates A : M A -> A -> Prop :=
  |TDNow a : Terminates (DNow a) a
  |TDLater d a : Terminates d a -> Terminates (DLater d) a.
Lemma Terminates_steps A (d : M A) (a : A) : Terminates d a <-> (exists n, steps n d = DNow a).
Proof.
split.
- move => Ht.
  elim: Ht => //=.
  + move => a0.
    by exists 0.
  + move => d0 a0 IH1 IH2.
    case: IH2 => x IH2.
    by exists x.+1.
- move => Hda.
  inversion Hda.
  move: d H Hda.
  elim: x.
  + move => d //= Hda //=Hs.
    rewrite Hda.
    by apply (TDNow a).
  + move => n IH //= d Hs [m Haa0].
    case: d Hs IH Haa0.
    + move => a0 Hs IH Haa0.
      rewrite Hs.
      apply (TDNow a).
    + move => d Hs IH Hda.
      apply TDLater.
      inversion Hs.
      case: m Hda.
      + by move => //= Hda.
      + move => n0 //= Hda0.
        apply IH => //=.
        by exists n0.
Qed.
Lemma Terminates_func A (d : M A) (a b : A) : Terminates d a -> Terminates d b -> a = b.
Proof.
case/Terminates_steps => n Ha.
case/Terminates_steps => m Hb.
wlog:n m a b Ha Hb/ n <= m.
- case/orP: (leqVgt n m) => nm H.
  + by apply: (H _ _ _ _ Ha Hb).
  + symmetry.
     apply: (H _ _ _ _ Hb Ha).
     exact:ltnW.
- move => nm.
  rewrite (monotonicity_steps Ha nm) in Hb .
  by case: Hb.
Qed.
Definition Diverges A (d : M A) : Prop := ~ (exists a, Terminates d a).
(*TerminatesPに直す*)
Lemma TerminatesP A (d : M A) : decidable (exists a, Terminates d a).
Proof.
case/boolP: `[< exists a, Terminates d a >].
- move/asboolP; by left.
- move/asboolP; by right.
Qed.
Lemma iff_not_Diverges_Terminates A (d : M A) : ~ Diverges d <-> (exists a, Terminates d a).
Proof.
split.
- by rewrite notE.
- by move => ? ?.
Qed.
Lemma Diverges_spinP A (d : M A) : Diverges d <-> d = @spin A.
Proof.
split.
- case: (TerminatesP d) => //= HD _.
  apply strongBisim_eq.
  move: d HD.
  cofix CIH.
  move => d HD.
  case: d HD => [a|d'] HD.
  + contradict HD.
    exists a.
    by apply TDNow.
  + rewrite -spinE.
    apply sBLater.
    apply CIH.
    move => [a Hd'].
    apply HD.
    exists a.
    by apply (TDLater Hd').
- move => HD.
  rewrite/Diverges HD/not;clear.
  move => [a /Terminates_steps [n Hs]].
  contradict Hs.
  elim: n => //=.
  by rewrite -spinE.
Qed.
CoInductive Oeq A : M A -> M A -> Prop :=
  |OTerminate d1 d2 a : Terminates d1 a -> Terminates d2 a -> Oeq d1 d2
  |OLater d1 d2 : Oeq d1 d2 -> Oeq (DLater d1) (DLater d2).
CoFixpoint Oeq_refl A (d : M A) : Oeq d d.
Proof.
case: d.
- move => a.
  have Ha: Terminates (DNow a) a.
    apply TDNow.
  apply (OTerminate Ha Ha).
- move => d.
  by apply OLater.
Qed.
Lemma Oeq_sym A (d1 d2 : M A) : Oeq d1 d2 -> Oeq d2 d1.
- move: d1 d2.
  cofix CIH.
  move => d1 d2 H12.
  case: d1 H12.
  + case: d2.
    + move => a b H12.
      inversion H12.
      apply (OTerminate H0 H).
    + move => d a H12.
      inversion H12.
      apply (OTerminate H0 H).
  + case: d2.
    + move => a d H12.
      inversion H12.
      apply (OTerminate H0 H).
      move => d1 d2 H12.
      inversion H12.
      apply (OTerminate H0 H).
      apply (OLater (CIH d2 d1 H1)).
Qed.
Lemma Terminates_Oeq A (d1 d2 : M A) (a : A) : Terminates d1 a -> Oeq d1 d2 -> Terminates d2 a.
Proof.
move => Ha.
elim: Ha d2.
- clear; move => a d2 Ho.
  inversion Ho.
  inversion H.
  by subst.
- clear; move => d a Ha IH d2 Ho.
  inversion Ho.
  + inversion H.
    subst.
    by rewrite (Terminates_func Ha H4).
  + apply TDLater.
    by apply IH.
Qed.
Lemma Diverges_Oeq A (d1 d2 : M A) : Diverges d1 -> Oeq d1 d2 -> Diverges d2.
Proof.
move => Hd1 /Oeq_sym Ho [a Ht].
apply: Hd1.
exists a.
by apply (Terminates_Oeq Ht Ho).
Qed.
CoFixpoint Oeq_trans A (d1 d2 d3 : M A) : Oeq d1 d2 -> Oeq d2 d3 -> Oeq d1 d3.
Proof.
move => Hd1 Hd2.
case: d1 d2/ Hd1 Hd2 => d1 d2.
- move => a Ht1 Ht2 Hd2.
  apply: (OTerminate Ht1).
  by apply: (Terminates_Oeq Ht2).
- move => Hd1 Hd2.
  inversion Hd2.
  + subst.
     have Hda: Terminates (DLater d1) a.
       apply TDLater.
       inversion H; subst.
       apply: (Terminates_Oeq  H2).
       by apply Oeq_sym.
     by apply: (OTerminate Hda).
  + apply OLater.
     by apply: (Oeq_trans _ _ _ _ Hd1).
Qed.
Add Parametric Relation A : (M A) (@Oeq A)
  reflexivity proved by (@Oeq_refl A)
  symmetry proved by (@Oeq_sym A)
  transitivity proved by (@Oeq_trans A)
  as Oeq_rel.
Hint Extern 0 (Oeq _ _) => setoid_reflexivity.
CoFixpoint Oeq_DLater A (d : M A) :  Oeq (DLater d) d.
Proof.
case: d => [a | d'].
- apply : OTerminate.
  + by apply/TDLater/TDNow.
  + by apply TDNow.
- apply : OLater.
  by apply Oeq_DLater.
Qed.
Lemma Oeq_steps A (d : M A) (n : nat) : Oeq (steps n d) d .
Proof.
elim: n d => [|n IH] d //=.
- case: d IH.
  + move => a _ //=.
  + move => d IH //=.
     by rewrite IH Oeq_DLater.
Qed.
Section wBisim.
Import boolp.
Definition wBisim (A : UU0) (d1 d2 : M A) : Prop :=
  exists n, steps n d1 = steps n d2.
Lemma wBisim_refl A (a : M A) : wBisim a a.
Proof. rewrite/wBisim. by exists 0. Qed.
Lemma wBisim_sym A (d1 d2 : M A) : wBisim d1 d2 -> wBisim d2 d1.
Proof. move => [n Hs]. by exists n. Qed.
Lemma wBisim_trans A (d1 d2 d3 : M A): wBisim d1 d2 -> wBisim d2 d3 -> wBisim d1 d3.
Proof.
move => [n Hs1] [m Hs2].
exists (n + m).
by rewrite stepsD Hs1 addnC stepsD -Hs2 -stepsD -stepsD addnC.
Qed.
Add Parametric Relation A : (M A) (@wBisim A)
  reflexivity proved by (@wBisim_refl A)
  symmetry proved by (@wBisim_sym A)
  transitivity proved by (@wBisim_trans A)
  as wBisim_rel.
Hint Extern 0 (wBisim _ _) => setoid_reflexivity.
Notation "a '≈' b" := (wBisim a b).
Lemma terminatesP A (a : M A) : decidable (exists c, exists m, steps m a = DNow c ).
Proof.
case/boolP: `[< exists c, exists m, steps m a = DNow c >].
- move/asboolP; by left.
- move/asboolP; by right.
Qed.
Lemma wBisim_DLater A (d : M A) : (DLater d) ≈ d.
Proof.
case: (TerminatesP d).
- move => [a /Terminates_steps [n Hs]].
  exists (n.+1).
  by rewrite (monotonicity_steps Hs (leqnSn n)).
- move => /Diverges_spinP Hs.
  by rewrite! Hs spinE.
Qed.
Lemma wBisim_steps A (d : M A) (n : nat) : steps n d ≈ d .
Proof.
elim: n d => [|n IH] d //=.
case: d IH.
  - move => a _ //=.
  - move => d IH //=.
    by rewrite IH wBisim_DLater.
Qed.
Lemma Terminates_wBisim A (d1 d2 : M A) (a : A) : Terminates d1 a -> d1 ≈ d2 -> Terminates d2 a.
Proof.
move => Ht1.
elim: Ht1 => [b|d b].
- move=> [n Hd].
  rewrite steps_Dnow in Hd.
  apply Terminates_steps.
  exists n.
  by symmetry.
- move => Ht1 IH.
  by rewrite wBisim_DLater.
Qed.
Corollary iff_Terminates_steps {A} (d : M A) (n : nat) (a : A) : Terminates d a <-> Terminates (steps n d) a.
Proof.
split => Ht.
- by apply (Terminates_wBisim Ht (wBisim_sym (wBisim_steps d n))).
- by apply (Terminates_wBisim Ht (wBisim_steps d n)).
Qed.
Lemma iff_Terminates_wBret {A} (d : M A) (a : A) : Terminates d a <-> (d ≈ Ret a).
Proof.
split.
- move => H.
  elim: H => //= d' a' _ H.
  by rewrite (wBisim_DLater d') H.
- move => [m H].
  apply/(iff_Terminates_steps d m a).
  rewrite H steps_Dnow.
  by apply TDNow.
Qed.
Corollary iff_Diverges_steps {A} (d : M A) (n : nat) : Diverges d <-> Diverges (steps n d).
Proof.
apply iff_not2.
split.
- move => [a Ht].
  exists a.
  by apply iff_Terminates_steps.
- move => [a Ht].
  exists a.
  by apply/(iff_Terminates_steps _ n _).
Qed.
Lemma iff_Diverges_Oeqspin {A} (d : M A) : Diverges d <-> Oeq d (@spin A).
Proof.
split.
- move => /Diverges_spinP HD.
  by rewrite HD.
- move => Ho [a Ht].
  have H : Diverges (@spin A).
    by apply/Diverges_spinP.
  apply H.
  exists a.
  by apply (Terminates_Oeq Ht Ho).
Qed.
Lemma iff_Diverges_wBisimspin {A} (d : M A) : Diverges d <-> d ≈ (@spin A).
Proof.
split.
- move => /Diverges_spinP HD.
  by rewrite HD.
- move => [n Hs].
  apply/(iff_Diverges_steps d n).
  rewrite Hs.
  by apply/(iff_Diverges_steps (@spin A) n)/(Diverges_spinP).
Qed.
Theorem iff_wBisim_Oeq A (d1 d2 : M A) : d1 ≈ d2 <-> Oeq d1 d2.
Proof.
split.
- case: (TerminatesP d1).
   + move => [a Ht] Hd.
     apply: OTerminate.
     * by apply Ht.
     * by apply (Terminates_wBisim Ht Hd).
   + move => /Diverges_spinP Hs.
    rewrite Hs;clear Hs.
    move =>/wBisim_sym/iff_Diverges_wBisimspin/Diverges_spinP Hs.
    by rewrite Hs.
- case: (TerminatesP d1).
  + move =>[a Ht].
    move/(Terminates_Oeq Ht).
    move: Ht => /Terminates_steps [n Ht1] /Terminates_steps [m Ht2].
    by rewrite -(wBisim_steps d1 n) -(wBisim_steps d2 m) Ht1 Ht2.
    + move => /Diverges_spinP Hs.
    rewrite Hs;clear Hs.
    move/Oeq_sym/iff_Diverges_Oeqspin/Diverges_spinP.
    move => Hs.
    by rewrite Hs.
Qed.
(*
Lemma steps_bind {A B} (n : nat) (m : M A) (f : A -> M B) : steps n (m >>= f) ≈  m >>= ((steps n) \o f).
Abort.
Lemma steps_ret {A} (n:nat) (a : A) : steps n (@ret M A a) ≈ @ret M A a.
Abort.
Lemma steps_monotonisity {A} (n : nat) (d : Delay A) : steps n d  ≈ d.
Abort.
*)
CoFixpoint while {A B} (body : A -> M (B + A)) : A -> M B :=
      fun a => (body a) >>= (fun ab => match ab with
                                      |inr a => DLater (while body a)
                                      |inl b => DNow b end).
Lemma whileE A B (f : A -> M (B + A)) (a : A) : while f a =  f a >>= (fun ab => match ab with
                                      |inr a => DLater (while f a)
                                      |inl b => DNow b end).
Proof.
rewrite [LHS](DelayE) //=.
by case: (f a) => [[b'|a'] | d]; rewrite [RHS](DelayE).
Qed.
Lemma bindDmf A B (m : M A) (f : A -> M B) : (DLater m) >>= f = DLater (m >>= f).
Proof. by rewrite [LHS]DelayE. Qed.
Lemma Diverges_bindspinf A B (f : A -> M B) : Diverges((@spin A) >>= f).
Proof.
apply/Diverges_spinP/strongBisim_eq.
cofix CIH.
rewrite -spinE -(spinE B) bindDmf.
by apply sBLater.
Qed.
Lemma Terminates_bindmf A B (d : M A) (a : A) (f : A -> M B) : Terminates d a -> d >>= f ≈ f a.
Proof.
move => Ht.
elim: Ht => [a'|d' a' Ht Hd'].
- by rewrite bindretf.
- by rewrite -Hd' bindDmf wBisim_DLater.
Qed.
Lemma bindmwB {A B} (f : A -> M B) (d1 d2 : M A) : d1 ≈ d2 -> d1 >>= f ≈ d2 >>= f.
Proof.
case: (TerminatesP d1).
- move => [a Ht1].
  move => /(Terminates_wBisim Ht1) Ht2.
  by rewrite (Terminates_bindmf f Ht1) (Terminates_bindmf f Ht2).
- move => /Diverges_spinP HD; subst.
  by move => /wBisim_sym/iff_Diverges_wBisimspin/Diverges_spinP Hd2; subst.
Qed.
Lemma bindfwB {A B} (f g : A -> M B) (d : M A) : (forall a, f a ≈ g a) -> d >>= f ≈ d >>= g.
Proof.
move => H.
apply/iff_wBisim_Oeq.
move: d.
cofix CIH => d.
case: d => [a|d].
- rewrite! bindretf.
  by apply iff_wBisim_Oeq.
- rewrite! bindDmf.
  by apply OLater.
Qed.
(* the next four laws derived from Complete Elgot monads *)
Lemma fixpointE {A B} (f : A -> M (B + A)) : forall (a : A), while f a ≈ (f a) >>= (sum_rect (fun => M B ) (@ret M B ) (while f)).
Proof.
move => a.
rewrite whileE.
apply bindfwB => ab.
case: ab => [b'|a'] //=.
by apply wBisim_DLater.
Qed.
CoFixpoint naturality' {A B C} (f : A -> M (B + A))(g : B -> M C)(d : M (B + A)) :
Oeq ((d >>= (fun ab : B + A => match ab with
                                   | inl b => DNow b
                                   | inr a => DLater (while f a)
                                   end)) >>= g)
    ((d >>= sum_rect (fun=> M (C + A)) (M # inl \o g) (M # inr \o (@ret M A))) >>=
     (fun ab : C + A => match ab with
                        | inl b => DNow b
                        | inr a => DLater (while (fun y : A => f y >>= sum_rect (fun=> M (C + A)) (M # inl \o g) (M # inr \o (@ret M A))) a)
                        end)).
Proof.
case: d => [[b|a]|d].
- apply iff_wBisim_Oeq.
  rewrite! bindretf /= fmapE bindA.
  case: (TerminatesP (g b)).
  + move => [c Ht].
    set h := fun x => (Ret \o inl) x >>= _.
    rewrite (Terminates_bindmf h Ht).
    subst h.
    rewrite /= bindretf.
    move: Ht => /Terminates_steps [n Ht].
    by rewrite -(wBisim_steps (g b) n) Ht.
  + move => /Diverges_spinP HD.
    rewrite HD.
    setoid_symmetry.
    apply/iff_Diverges_wBisimspin.
    by apply Diverges_bindspinf.
- rewrite! bindretf /= fmapE bindA bindretf /= bindretf /= bindDmf.
  apply OLater.
  rewrite whileE whileE.
  by apply naturality'.
- rewrite! bindDmf.
  apply OLater.
  by apply naturality'.
Qed.
Lemma naturalityE {A B C} (f : A -> M (B + A)) (g : B -> M C) (a : A) :
   (while f a) >>= g ≈ while (fun y => (f y) >>= (sum_rect (fun => M (C + A)) (M # inl \o g) (M # inr \o (@ret M A )))) a.
Proof. by apply iff_wBisim_Oeq; rewrite whileE whileE; apply naturality'. Qed.
CoFixpoint codiagonal' {A B} (f: A -> M ((B + A) + A))(d: M ((B + A) + A)) :
Oeq (( d >>= (Ret \o sum_rect (fun=> (B + A)%type) idfun inr)) >>=
  (fun ab : B + A => match ab with
                     | inl b => DNow b
                     | inr a => DLater (while (M # sum_rect (fun=> (B + A)%type) idfun inr \o f) a)
                     end))
  ((d >>= (fun ab : B + A + A => match ab with
                                    | inl b => DNow b
                                    | inr a => DLater (while f a)
                                    end)) >>= (fun ab : B + A => match ab with
                                                                 | inl b => DNow b
                                                                 | inr a => DLater (while (while f) a)
                                                                 end)).
Proof.
case: d => [baa|d'].
- case: baa => [[b|a]|a].
  + by rewrite bindretf bindretf bindretf //= bindretf.
  + rewrite bindretf bindretf bindretf //= bindretf whileE whileE whileE //= fmapE.
    apply OLater.
    by apply codiagonal'.
  + rewrite bindretf bindretf bindretf //= bindDmf whileE whileE //= fmapE.
    apply OLater.
    by apply codiagonal'.
- rewrite! bindDmf.
  apply OLater.
  by apply codiagonal'.
Qed.
Lemma codiagonalE {A B} (f : A -> M ((B + A) + A)) (a : A) : while ((Delay # ((sum_rect (fun => (B + A)%type) idfun inr)))  \o f ) a ≈ while (while f) a.
Proof. by apply iff_wBisim_Oeq; rewrite whileE whileE whileE //= fmapE; apply codiagonal'. Qed.
CoFixpoint whilewB1 {X A} (f g : X -> M(A + X)) :
  (forall x, wBisim (f x) (g x)) ->
  forall d1 d2: M (A + X),
    d1 ≈ d2 ->
    d1 >>= (fun ax : A + X => match ax with
                               | inl a => DNow a
                               | inr x => DLater (while f x)
                               end) = @spin A ->
    strongBisim (d2 >>= (fun ax : A + X => match ax with
                                    | inl a => DNow a
                                    | inr x => DLater (while g x) end))
          (@spin A).
Proof.
move => Hfg d1 d2 Hd.
case: d1 Hd => [[b|a]|d1'].
- move => _ contr.
  contradict contr.
  rewrite bindretf.
  by rewrite -spinE.
- case: d2 => [ba|d2'].
  + move => [n Hd].
    rewrite steps_Dnow steps_Dnow in Hd.
    rewrite -Hd bindretf bindretf -spinE => Hf.
    case: Hf.
    rewrite whileE whileE => Hf.
    apply sBLater.
    by apply (whilewB1 _ _ f g Hfg _ _ (Hfg a)).
  + move => Hd Hf.
    rewrite -spinE bindDmf.
    apply: sBLater.
    assert (Had : DNow (inr a) ≈ d2').
      by rewrite Hd wBisim_DLater.
    by apply (whilewB1 _ _ f g Hfg (DNow (inr a)) d2' Had Hf).
- case: d2 =>[[b|a]|d2'].
  + move => Hd.
    move/Diverges_spinP/iff_Diverges_wBisimspin.
    rewrite (bindmwB _ Hd) bindretf => /iff_Diverges_wBisimspin/Diverges_spinP contr.
    contradict contr.
    by rewrite -spinE.
  + move => Hd.
    set x := (x in DLater d1' >>= x).
    move => Hf.
    assert (Hs: (DLater d1' >>= x) ≈ (DNow (inr a) >>= x)).
      by rewrite (bindmwB _ Hd).
    move: Hs.
    subst x.
    rewrite Hf bindretf.
    move => Hs.
    rewrite bindretf -spinE whileE.
    apply sBLater.
    apply (whilewB1 _ _ _ _ Hfg _ _ (Hfg a)).
    rewrite -whileE.
    apply/Diverges_spinP/iff_Diverges_wBisimspin.
    by rewrite Hs wBisim_DLater.
  + move => Hd Hf.
    rewrite -spinE bindDmf.
    apply: sBLater.
    assert (Hd2 : DLater d1' ≈ d2').
      by rewrite Hd wBisim_DLater.
    by apply (whilewB1 _ _ f g Hfg (DLater d1') d2' Hd2 Hf).
Qed.
Lemma whilewB2 {A B} (d1 d2 : M (B + A)) (f g : A -> M (B + A)) (b : B) : (forall a, wBisim (f a) (g a)) -> wBisim d1 d2 -> wBisim (d1 >>= (fun ab : B + A => match ab with
                                   | inl b => DNow b
                                   | inr a => DLater (while f a)
                                   end)) (@ret M B b) -> wBisim (d2 >>= (fun ab : B + A => match ab with
                                   | inl b => DNow b
                                   | inr a => DLater (while g a)
                                   end)) (@ret M B b).
Proof.
move => Hfg Hd [n Hf].
move : d1 d2 Hd Hf.
rewrite steps_Dnow.
elim: n => [d1 d2|n IH d1 d2].
- case: d1 => [[b'|a']|d1'].
  + rewrite bindretf => /wBisim_sym Hd //= Hf.
    by rewrite (bindmwB _ Hd) bindretf Hf.
  + by rewrite bindretf /= => _ Hf.
  + by rewrite bindDmf /= => _ Hf.
- case: d1 => [[b'|a']|d1'] H.
  + rewrite bindretf steps_Dnow -(bindmwB _ H) bindretf => Hb.
    by rewrite Hb.
  + rewrite bindretf /= -(bindmwB _ H) bindretf wBisim_DLater whileE whileE.
    by apply (IH (f a') (g a') (Hfg a')).
  + move: H.
    rewrite bindDmf /= wBisim_DLater.
    by apply IH.
Qed.
Lemma whilewB {A B} (f g : A -> M (B + A)) (a : A) : (forall a, (f a) ≈ (g a)) -> while f a ≈ while g a.
Proof.
move => Hfg.
case: (TerminatesP (while f a)) => [[b /iff_Terminates_wBret HT]| /Diverges_spinP HD].
- rewrite HT.
  setoid_symmetry.
  move: HT.
  rewrite! whileE.
  by apply (whilewB2 Hfg (Hfg a)).
- rewrite HD.
  setoid_symmetry.
  apply/iff_Diverges_wBisimspin/Diverges_spinP/strongBisim_eq.
  move: HD.
  rewrite !whileE.
  by apply (whilewB1 Hfg (Hfg a)).
Qed.
(*
Lemma uniform {A B C} (f:A -> Delay(B + A)) (g: C -> Delay (B + C)) (h: C -> Delay A) :
  forall (z:C),(h z) >>= f  ≈ ( (g z) >>= (sum_functin ((Delay # inl) \o (fun (y:B) => DNow y)(*ret*)) ((Delay # inr) \o h ))) -> forall (z:C), (h z) >>= (while f)  ≈  while g z. Abort.*)
HB.instance Definition _ := @isMonadDelay.Build M
  (@while) wBisim wBisim_refl wBisim_sym wBisim_trans (@fixpointE) (@naturalityE) (@codiagonalE) (@bindmwB) (@bindfwB) (@whilewB).
End wBisim.
End delayops.
End DelayOps.
HB.export DelayOps.
