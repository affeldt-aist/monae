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
Let bind := fun A B (m: M A) (f: A -> M B) =>
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
CoInductive Bisim (A : UU0) : M A -> M A -> Prop :=
| BRefl (m : M A) : @Bisim A m m
| BLater (m m' : M A) :
  @Bisim A m m' -> @Bisim A (DLater m) (DLater m').
Arguments Bisim [A].
Arguments BLater [A].
Axiom Bisim_eq : forall A (m m' : M A), Bisim m m' -> m = m'.
CoFixpoint right_neutral_bisim A (m : M A) : Bisim (bind m (@ret A)) m.
case: m=> [a|m].
  rewrite [X in Bisim X]DelayE /=.
  exact: BRefl.
rewrite [X in Bisim X]DelayE /=.
apply: BLater.
exact: right_neutral_bisim.
Qed.
Lemma right_neutral : BindLaws.right_neutral bind ret.
Proof. by move=> *; exact/Bisim_eq/right_neutral_bisim. Qed.
CoFixpoint associative_bisim A B C (m : M A) (f : A -> M B) (g : B -> M C) :
  Bisim (bind (bind m f) g) (bind m (fun x => bind (f x) g)).
Proof.
case: m=> [a|m].
  rewrite [X in Bisim _ X]DelayE.
  rewrite [X in Bisim X]DelayE.
  simpl.
  exact: BRefl.
rewrite [X in Bisim _ X]DelayE.
rewrite [X in Bisim X]DelayE.
simpl.
apply: BLater.
exact: associative_bisim.
Qed.
Lemma associative : BindLaws.associative bind.
Proof. move=> *; exact/Bisim_eq/associative_bisim. Qed.
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
Lemma stepsD A n m (x: M A) : steps (m + n) x = steps n (steps m x).
Proof.
elim: m x => //=.
move => m IH [a | x].
- by elim: n {IH}.
- by apply IH.
Qed.
Lemma steps_Dnow A n (a: A): steps n (DNow a) = DNow a.
Proof. by elim: n => //=. Qed.
Lemma monotonicity_steps' A n  (a: A): forall (x: M A), steps n (DLater x) = DNow a -> steps n x = DNow a.
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
Lemma nmSleq (n:nat) (m:nat): n<= m.+1 -> n = m.+1 \/ n <= m.
Proof.
move=> H.
  case: (leqP n m) => [Hleq | Hnleq].
  - by right.
  - left. apply/eqP. by rewrite eqn_leq H Hnleq.
Qed.
Lemma monotonicity_steps A (x: M A) (a: A) (n: nat):  steps n x = DNow a -> forall m, n <= m -> steps m x = DNow a.
Proof.
move => Hn m.
elim: m => //=.
- rewrite leqn0.
  move => /eqP Hnm.
  rewrite Hnm in Hn.
  move: Hn => Hn //=.
- move => m IH Hnm.
  case: x Hn IH => a0 Ha Hm.
  + case: n Ha Hnm Hm => //=.
  + apply nmSleq in Hnm.
    case: Hnm => H.
    * by rewrite H in Ha.
    * apply Hm in H.
      by apply monotonicity_steps'.
Qed.
CoFixpoint spin A :M A  := DLater (spin A).
Lemma spinE A: DLater (@spin A) = (@spin A).
Proof.
apply Bisim_eq.
cofix IH.
rewrite [X in DLater X]DelayE [X in Bisim _ X]DelayE /=.
exact/BLater/IH.
Qed.
Inductive Terminates A: M A -> A -> Prop :=
  |TDNow a : Terminates (DNow a) a
  |TDLater d a: Terminates d a -> Terminates (DLater d) a.
Lemma Terminates_steps A (d: M A) (a: A): Terminates d a <-> (exists n, steps n d = DNow a).
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
Lemma Terminates_func A (d : M A) (a b: A): Terminates d a -> Terminates d b -> a = b.
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
Definition Diverges A (d: M A) :Prop := ~ (exists a, Terminates d a).
(*TerminatesPに直す*)
Lemma TerminatesP A (d:M A): decidable (exists a, Terminates d a).
Proof.
case/boolP: `[< exists a, Terminates d a >].
- move/asboolP; by left.
- move/asboolP; by right.
Qed.
Lemma iff_not_Diverges_Terminates A (d: M A): ~ Diverges d <-> (exists a, Terminates d a).
Proof.
split.
- by rewrite notE.
- by move => ? ?.
Qed.
(*Divergesはnot (exists a, Terminate d a)と定義すべき(一番自然)*)
Lemma Diverges_spinP A (d: M A): Diverges d <-> d = @spin A.
Proof.
split.
- case: (TerminatesP d) => //= HD _.
  apply Bisim_eq.
  move: d HD.
  cofix CIH.
  move => d HD.
  case: d HD => [a|d'] HD.
  + contradict HD.
    exists a.
    by apply TDNow.
  + rewrite -spinE.
    apply BLater.
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
CoInductive Oeq A: M A -> M A -> Prop :=
  |OTerminate d1 d2 a: Terminates d1 a -> Terminates d2 a -> Oeq d1 d2
  |OLater d1 d2: Oeq d1 d2 -> Oeq (DLater d1) (DLater d2).
CoFixpoint Oeq_refl A (d: M A):Oeq d d.
Proof.
case: d.
- move => a.
  have Ha: Terminates (DNow a) a.
    apply TDNow.
  apply (OTerminate Ha Ha).
- move => d.
  by apply OLater.
Qed.
Lemma Oeq_sym A (d1 d2: M A): Oeq d1 d2 -> Oeq d2 d1.
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
Lemma Terminates_Oeq A (d1 d2 : M A) (a: A): Terminates d1 a -> Oeq d1 d2 -> Terminates d2 a.
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
Lemma Diverges_Oeq A (d1 d2 : M A): Diverges d1 -> Oeq d1 d2 -> Diverges d2.
Proof.
move => Hd1 /Oeq_sym Ho [a Ht].
apply: Hd1.
exists a.
by apply (Terminates_Oeq Ht Ho).
Qed.
CoFixpoint Oeq_trans A (d1 d2 d3: M A): Oeq d1 d2 -> Oeq d2 d3 -> Oeq d1 d3.
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
case: d.
- move => a.
  apply : OTerminate.
  + by apply/TDLater/TDNow.
  + by apply/TDNow.
- move => d.
  apply OLater.
  by apply Oeq_DLater.
Qed.
Lemma Oeq_steps A (d : M A) (n:nat): Oeq (steps n d) d .
Proof.
elim: n d => [|n IH] d //=.
- case: d IH.
  + move => a _ //=.
  + move => d IH //=.
     by rewrite IH Oeq_DLater.
Qed.
Section wBisim.
Import boolp.
Definition wBisim (A: UU0)  (d1 d2: M A): Prop :=
  exists n, steps n d1 = steps n d2.
Lemma wBisim_refl A (a: M A): wBisim a a.
Proof. rewrite/wBisim. by exists 0. Qed.
Lemma wBisim_sym A (d1 d2: M A): wBisim d1 d2 -> wBisim d2 d1.
Proof. move => [n Hs]. by exists n. Qed.
Lemma wBisim_trans A (d1 d2 d3: M A): wBisim d1 d2 -> wBisim d2 d3 -> wBisim d1 d3.
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
Lemma terminatesP A (a:M A): decidable (exists c, exists m, steps m a = DNow c ).
Proof.
case/boolP: `[< exists c, exists m, steps m a = DNow c >].
- move/asboolP; by left.
- move/asboolP; by right.
Qed.
Lemma wBisim_DLater A (d : M A): (DLater d) ≈ d.
Proof.
case: (TerminatesP d).
- move => [a /Terminates_steps [n Hs]].
  exists (n.+1).
  by rewrite (monotonicity_steps Hs (leqnSn n)).
- move => /Diverges_spinP Hs.
  by rewrite! Hs spinE.
Qed.
Lemma wBisim_steps A (d : M A) (n:nat): steps n d ≈ d .
Proof.
elim: n d => [|n IH] d //=.
case: d IH.
  - move => a _ //=.
  - move => d IH //=.
    by rewrite IH wBisim_DLater.
Qed.
Lemma Terminates_wBisim A (d1 d2 : M A) (a: A): Terminates d1 a -> d1 ≈ d2 -> Terminates d2 a.
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
Corollary iff_Terminates_steps {A} (d: M A)(n: nat)(a: A): Terminates d a <-> Terminates (steps n d) a.
Proof.
split => Ht.
- by apply (Terminates_wBisim Ht (wBisim_sym (wBisim_steps d n))).
- by apply (Terminates_wBisim Ht (wBisim_steps d n)).
Qed.
Lemma iff_Terminates_wBret {A} (d: M A)(a: A): Terminates d a <-> (d ≈ Ret a).
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
Corollary iff_Diverges_steps {A} (d: M A)(n: nat): Diverges d <-> Diverges (steps n d).
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
Lemma iff_Diverges_Oeqspin {A} (d: M A): Diverges d <-> Oeq d (@spin A).
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
Lemma iff_Diverges_wBisimspin {A} (d: M A): Diverges d <-> d ≈ (@spin A).
Proof.
split.
- move => /Diverges_spinP HD.
  by rewrite HD.
- move => [n Hs].
  apply/(iff_Diverges_steps d n).
  rewrite Hs.
  by apply/(iff_Diverges_steps (@spin A) n)/(Diverges_spinP).
Qed.
Theorem iff_wBisim_Oeq A (d1 d2 : M A) :d1 ≈ d2 <-> Oeq d1 d2.
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
Lemma steps_bind {A B} (n:nat) (m: M A) (f: A -> M B) : steps n (m >>= f) ≈  m >>= ((steps n) \o f).
Abort.
Lemma steps_ret {A} (n:nat) (a: A) : steps n (@ret M A a) ≈ @ret M A a. 
Abort.
Lemma steps_monotonisity {A} (n: nat) (d: Delay A):steps n d  ≈ d.
Abort.
*)
CoFixpoint while {A B} (body: A -> M (B + A)) :A -> M B :=
      fun a => (body a) >>= (fun ab => match ab with
                                      |inr a => DLater (while body a)
                                      |inl b => DNow b end).
Lemma whileE A B (f: A -> M (B + A)) (a: A): while f a =  f a >>= (fun ab => match ab with
                                      |inr a => DLater (while f a)
                                      |inl b => DNow b end).
Proof.
rewrite [LHS](DelayE) //=.
case: (f a) => [[b'|a'] | d].
- by rewrite [RHS](DelayE).
- by rewrite [RHS](DelayE).
- by rewrite [RHS](DelayE).
Qed.
Lemma bindDmf A B (m : M A) (f: A -> M B):(DLater m) >>= f = DLater (m >>= f).
Proof. by rewrite [LHS]DelayE. Qed.
Lemma Diverges_bindspinf A B (f: A -> M B):Diverges((@spin A) >>= f).
Proof.
apply/Diverges_spinP/Bisim_eq.
cofix CIH.
rewrite -spinE -(spinE B) bindDmf.
by apply BLater.
Qed.
Lemma Terminates_bindmf A B (d: M A)(a: A)(f: A -> M B): Terminates d a -> d >>= f ≈ f a.
Proof.
move => Ht.
elim: Ht => [a'|d' a' Ht Hd'].
- by rewrite bindretf.
- by rewrite -Hd' bindDmf wBisim_DLater.
Qed.
Lemma bindmwB {A B} (f: A -> M B) (d1 d2: M A): d1 ≈ d2 -> d1 >>= f ≈ d2 >>= f.
Proof.
case: (TerminatesP d1).
- move => [a Ht1].
  move => /(Terminates_wBisim Ht1) Ht2.
  by rewrite (Terminates_bindmf f Ht1) (Terminates_bindmf f Ht2).
- move => /Diverges_spinP HD; subst.
  by move => /wBisim_sym/iff_Diverges_wBisimspin/Diverges_spinP Hd2; subst.
Qed.
Lemma bindfwB {A B} (f g: A -> M B) (d: M A): (forall a, f a ≈ g a) -> d >>= f ≈ d >>= g.
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
(* the next four conditions derived from Complete Elgot monads *)
Lemma fixpointE {A B} (f: A -> M (B + A)):forall (a:A), while f a ≈ (f a) >>= (sum_rect (fun => M B ) (@ret M B ) (while f)).
Proof.
move => a.
rewrite whileE.
apply bindfwB => ab.
case: ab => [b'|a'] //=.
by apply wBisim_DLater.
Qed.
(*hierarchy.v monad_lib. *)
CoFixpoint naturality' {A B C} (f: A -> M (B + A)) (g: B -> M C)(d: M (B + A)):
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
Lemma naturalityE {A B C} (f: A -> M (B + A)) (g: B -> M C)(a:A):
   (while f a) >>= g   ≈  while (fun y => (f y) >>= (sum_rect (fun => M (C + A)) (M # inl \o g) (M # inr \o (@ret M A )))) a.
Proof. by apply iff_wBisim_Oeq; rewrite whileE whileE; apply naturality'. Qed.
CoFixpoint codiagonal' {A B} (f: A -> M ((B + A) + A))(d: M ((B + A) + A)):
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
Lemma codiagonalE {A B} (f: A -> M ((B + A) + A))(a:A):
   while ((Delay # ((sum_rect (fun => (B + A)%type) idfun inr)))  \o f ) a  ≈ while (while f) a.
Proof. by apply iff_wBisim_Oeq; rewrite whileE whileE whileE //= fmapE; apply codiagonal'. Qed.
CoFixpoint whilewB1 {A B} (f g: A -> M(B + A)):
  (forall a, wBisim (f a) (g a)) -> forall (d1 d2: M (B + A)) , ( d1 ≈ d2) ->  ((d1 >>= (fun ab : B + A => match ab with
                                   | inl b => DNow b
                                   | inr a => DLater (while f a)
                                                end)
                                   = (@spin B))) ->  Bisim (d2 >>= (fun ab : B + A => match ab with
                                   | inl b => DNow b
                                   | inr a => DLater (while g a)
                                   end)) (@spin B).
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
    apply BLater.
    by apply (whilewB1 _ _ f g Hfg _ _ (Hfg a)).
  + move => Hd Hf.
    rewrite -spinE bindDmf.
    apply BLater.
    assert (Had: DNow (inr a) ≈ d2').
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
    apply BLater.
    apply (whilewB1 _ _ _ _ Hfg _ _ (Hfg a)).
    rewrite -whileE.
    apply/Diverges_spinP/iff_Diverges_wBisimspin.
    by rewrite Hs wBisim_DLater.
  + move => Hd Hf.
    rewrite -spinE bindDmf.
    apply BLater.
    assert (Hd2 : DLater d1' ≈ d2').
      by rewrite Hd wBisim_DLater.
    by apply (whilewB1 _ _ f g Hfg (DLater d1') d2' Hd2 Hf).
Qed.
Lemma whilewB2 {A B} (d1 d2: M(B + A))(f g: A -> M(B + A))(b: B): (forall a, wBisim (f a) (g a)) -> wBisim d1 d2 -> wBisim (d1 >>= (fun ab : B + A => match ab with
                                   | inl b => DNow b
                                   | inr a => DLater (while f a)
                                   end)) (@ret M B b) -> wBisim(d2 >>= (fun ab : B + A => match ab with
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
(*名前のprefixのwBisim_は混乱を生じない場合はいらない*)
Lemma whilewB {A B} (f g: A -> M(B + A)) (a: A) : (forall a, (f a) ≈ (g a)) -> while f a ≈ while g a.
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
  apply/iff_Diverges_wBisimspin/Diverges_spinP/Bisim_eq.
  move: HD.
  rewrite! whileE.
  by apply (whilewB1 Hfg (Hfg a)).
Qed.
(*
Lemma uniform {A B C} (f:A -> Delay(B + A)) (g: C -> Delay (B + C)) (h: C -> Delay A) :
  forall (z:C),(h z) >>= f  ≈ ( (g z) >>= (sum_functin ((Delay # inl) \o (fun (y:B) => DNow y)(*ret*)) ((Delay # inr) \o h ))) -> forall (z:C), (h z) >>= (while f)  ≈  while g z. Abort.*)
HB.instance Definition _ := @isMonadDelay.Build M
  (@while) wBisim wBisim_refl wBisim_sym wBisim_trans (@fixpointE) (@naturalityE) (@codiagonalE) (@bindmwB) (@bindfwB) (@whilewB).
End wBisim.
End delayops.
(*
Section delayops_examples.
Hint Extern 0 (wBisim _ _) => setoid_reflexivity.
Notation "a '≈' b" := (wBisim a b).
Local Notation M := Delay.
Fixpoint fact (n:nat) :nat := match n with
                          |O => 1
                          |S n' => n * fact n'
                          end.
Definition fact_body: nat * nat -> M (nat + nat*nat) := fun (a: nat * nat) =>
                                            match a with
                                            |(O, a2) => @ret M (nat + nat*nat)%type (inl a2)
                                            |(S n', a2) => (@ret M (nat + nat*nat)%type) (inr (n', a2 * (S n') ))
                                            end .
Definition factdelay := fun (nm: nat*nat) => while fact_body nm.
Fixpoint steps' A n (x : M A) : M A :=
  if n is m.+1 then
    match x with
    | DNow a => DNow a
    | DLater da => DLater (steps' m da)
    end
  else x.
Compute steps' 5 (factdelay (5, 1)).
Lemma eq_fact_factdelay :forall n m, (factdelay (n, m)) ≈ (@ret M nat (m * fact n)).
move => n.
rewrite  /factdelay.
elim: n.
- move => m.
   apply: wBisim_trans.
  apply: fixpointE.
  simpl.
  by rewrite bindretf muln1 //=.
- move => n IH m.
  eapply wBisim_trans.
  apply fixpointE.
  simpl.
  rewrite bindretf //=.
  eapply wBisim_trans.
  apply IH.
  by rewrite mulnA.
Qed.
Definition collatzm_body (m:nat) (n:nat) :=
  if n == 1 then @ret M _ (inl m)
  else if (n %%2 == 0) then @ret M _ (inr (n./2))
       else @ret M _ (inr (3*n + 1)).
Definition collatzm (m:nat) := while (collatzm_body m).
Definition delaymul (m:nat) (d: M nat) :M nat := d >>= (fun n => @ret _ _ (m * n)).
Lemma collatzm_mul : forall (m n p: nat), wBisim  (delaymul p (collatzm m n)) (collatzm (p * m ) n ). Abort.
(*
Definition minus1_body (nm: nat*nat)  :M ((nat + nat*nat) + nat*nat):= match nm with
                                                                |(O, m) => match m with
                                                                         |O => @ret _ _ (inl (inl O))
                                                                         |S m' => @ret _ _ (inl (inr (m', m')))
                                                                         end
                                                                |(S n', m) => @ret _ _ (inr (n', m ))
                                                                end.
Definition minus1 := while (while minus1_body).
Definition minus2_body (nm: nat*nat) :  (nat + nat*nat) := match nm with
                                                      |(O,m) => match m with
                                                                |O => ret (inl O)
                                                                |S m' => ret (inr (m', m'))
                                                                end
                                                      |(S n', m) => ret (inr (n',m))
                                                      end.
Definition minus2 := while minus2_body.
Lemma eq_minus : forall (nm: nat*nat), wBisim (minus1 nm) (minus2 nm). Abort.
*)
Definition collatzs1_body (nml: nat*nat*nat) : M ((nat*nat + nat*nat*nat) + nat*nat*nat)%type :=
match nml with (n,m,l) => 
if n==1 then if (l %% 4 == 1) then @ret _ _ (inl(inl (m,l))) else @ret _ _ (inl(inr (m+1, m+1, 0)))
         else if (n %% 2 == 0) then @ret _ _ (inr (n./2,m,l+1))
                               else @ret _ _ (inr (3*n + 1, m, l+1))
end.
Definition collatzs1 (n: nat) := while (while collatzs1_body) (n,n,0).
Compute steps 50 (collatzs1 4).
Definition collatzs2_body (nml: nat*nat*nat) : M ((nat*nat + nat*nat*nat))%type :=
match nml with (n,m,l) =>
if (l %% 4 == 1) && (n == 1) then @ret _ _ (inl (m,l))
else if (n == 1) then @ret _ _ (inr (m+1,m+1,0))
                 else if (n %% 2) == 0 then @ret _ _ (inr (n./2,m,l+1))
                               else @ret _ _(inr (3*n + 1, m, l+1))
end.
Definition collatzs2 (n:nat):= while collatzs2_body (n,n,0).
Compute steps 50 (collatzs2 4).
Lemma collatzstepE (n:nat): collatzs1 n ≈ collatzs2 n.
Proof.
rewrite/collatzs1/collatzs2.
rewrite -codiagonalE.
apply whilewB.
move => [[n' m] l].
rewrite/collatzs1_body/collatzs2_body.
case/boolP: (l %% 4 == 1) => Hl //=.
- case/boolP: (n' == 1) => Hn' //=.
  + by rewrite Hl fmapE bindretf //=.
  + case/boolP: (n' %% 2 == 0) => He //=.
    * by rewrite fmapE bindretf //=.
    * by rewrite fmapE bindretf //=.
- case/boolP: (n' == 1) => Hn' //=.
  + by rewrite ifN //= fmapE bindretf //=.
  + case/boolP: (n' %% 2 == 0) => He //=.
    * by rewrite fmapE bindretf //=.
    * by rewrite fmapE bindretf //=.
Qed.
Definition fastexp_body (nmk: nat*nat*nat) :M (nat + nat*nat*nat)%type := match  nmk with (n,m,k) => if n == 0 then ret _ (inl m) else   (if n %% 2 == 1 then ret _ (inr (n - 1 , m*k, k)) else ret _ (inr (n./2, m, k*k) )) end.

Definition fastexp3 (n: nat) := while fastexp_body (n,1,3).

Compute steps 300 (fastexp3 7).

Fixpoint exp3 (n: nat) := match n with |O => 1 | S n' => 3*exp3 n' end.

(*nが再帰の回数、mが再帰する値を表す*)
Definition mc91_body (nm: nat*nat):M (nat + nat*nat) :=
  match nm with (n, m) => if n==0 then ret _ (inl m)
                          else if m > 100 then ret _ (inr (n.-1,m - 10))
                                          else ret _ (inr (n.+1,m + 11))
end.

Definition mc91 (n m: nat):= while mc91_body (n.+1,m).
Compute steps 1000 (mc91 3 50).

Lemma mc91succE (n m: nat): 90 <= m < 101 -> mc91 n m ≈ mc91 n (m.+1).
Proof.
- move => /andP [Hmin Hmax].
  rewrite/mc91/mc91_body fixpointE /=.
  move: Hmax.
  rewrite ltnNge.
  case:ifP => //= Hf _.
  rewrite bindretf /= fixpointE /=.
  have H100 : 100 = 89 + 11. by [].
  rewrite H100 ltn_add2r Hmin bindretf fixpointE /= fixpointE /=.
  have ->: m + 11 - 10 = m.+1.
    rewrite -addnBA // /=.
    have -> : 11 - 10 = 1. by [].
    by rewrite addn1.
  by [].
Qed.

Lemma eq_sub (n m: nat) : n <= m -> m - n = 0 -> m = n.
Proof.
move => Hleq Hmn.
rewrite -(addn0 n).
rewrite -Hmn.
rewrite -addnCB.
by rewrite addnBl_leq //.
Qed.

Lemma leq_exists (n m: nat): n < m -> exists k, n + k = m.
Proof.
elim: m.
- by rewrite ltn0.
- move => m IH.
  move/nmSleq => [Hn|Hn].
  + exists 1.
    by rewrite addn1.
  + move: Hn.
    move/IH => [k Hn].
    exists (k + 1).
    by rewrite addnA Hn addn1.
Qed.
Lemma mc91E_aux (m n : nat):90 <= m <= 101 -> mc91 n m ≈ mc91 n 101.
Proof.
move => /andP [Hmin Hmax].
case/boolP: (m < 101).
- move/leq_exists => [k Hn].
  move: m Hmin Hmax Hn.
  elim: k.
  + move => m Hmin Hmax.
    rewrite addn0 => Hm.
    by rewrite Hm.
  + move => l IH m Hmin.
    move/nmSleq => [H101 | Hm].
    * by rewrite H101 => _.
    * rewrite -addn1.
      rewrite (addnC l 1) addnA.
      rewrite mc91succE //.
      ** rewrite addn1.
         apply IH => //.
         rewrite -(addn1 m).
         by apply ltn_addr.
      ** apply/andP.
         by split => //.
- rewrite -leqNgt => H100.
  have -> : m = 101.
    apply anti_leq => //.
    apply/andP.
    by split => //= .
  by [].
Qed.

Lemma mc91_101E (n: nat): mc91 n 101 ≈ ret _ 91.
Proof.
elim: n => [|n IH].
- rewrite/mc91/mc91_body fixpointE/= bindretf/= fixpointE/= bindretf/=.
  have ->: 101 - 10 = 91. by [].
  done.
- rewrite/mc91/mc91_body fixpointE/= bindretf/=.
  rewrite -/mc91_body //.
  have ->: while mc91_body (n.+1, 101 - 10) = mc91 n 91.
    have -> : 101 - 10 = 91. by [].
      by rewrite/mc91.
  by rewrite mc91E_aux // IH.
Qed.

Lemma mc91E (n m : nat): m <= 101 -> mc91 n m ≈ ret _ 91.
Proof.
case/boolP: (90 <= m).
- move => H89 H101.
  move: (conj H89 H101) => /andP Hm.
  by rewrite mc91E_aux // mc91_101E.
- rewrite -leqNgt.
  rewrite -ltnS.
  move/leq_exists => [k Hm] _.
  move: n m Hm.
  elim: k {-2}k (leqnn k) => k.
  + rewrite leqn0 => /eqP H0 n m.
    rewrite H0 (addn0 m) => Hm.
    rewrite Hm.
    have H90: 90 <= 90 <= 101.
      by apply/andP; split => //.
    rewrite mc91E_aux //.
    by rewrite mc91_101E.
  + move =>IH k' Hk n m Hm.
    have -> : m = 90 - k'.
      rewrite -Hm.
      rewrite -addnBA //.
      by rewrite subnn addn0.
    rewrite/mc91/mc91_body fixpointE //=.
    have -> : (100 < 90 - k') = false.
      apply/negP/negP.
      rewrite -leqNgt.
      rewrite leq_subLR addnC.
      have H89:89 < 100. by [].
      apply (leq_trans H89).
      apply leq_addr.
    rewrite bindretf /=.
    rewrite-/mc91_body-/mc91.
    have -> : while mc91_body (n.+2, 90 - k' + 11) = mc91 (n.+1) (90 - k' + 11). by rewrite/mc91.
    have Hk'90: k' <= 90.
      rewrite -Hm addnC.
      by apply leq_addr.
    case/boolP : (k' <= 11) => Hk'.
      * have H: 90 <= 90 - k' + 11 <= 101.
          rewrite -addnABC //.
          apply/andP; split.
            ** by apply leq_addr.
            ** rewrite addnBA //.
               have -> :90 + 11 = 101. by [].
               by apply leq_subr.
        by rewrite (mc91E_aux _ H) mc91_101E.

      * move: Hk'.
        rewrite -ltnNge => Hk'11.
        rewrite (IH (k' - 11)) //.
        ** rewrite leq_subLR.
           apply: (leq_trans Hk).
           have -> :11 + k = (k.+1) + 10.
             by rewrite addnC -(addn1 k) -addnA (addnC 1 10) (addn1 10).
           by apply leq_addr.
        ** rewrite -addnA.
           rewrite subnKC //.
           *** rewrite subnK //.
           *** apply: (ltn_trans (ltnSn 10) Hk'11).
Qed.

End delayops_examples.
*)
End DelayOps.
HB.export DelayOps.
