(* monae: Monadic equational reasoning in Rocq                                *)
(* Copyright (C) 2025 monae authors, license: LGPL-2.1-or-later               *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require boolp.
From HB Require Import structures.
Require Import hierarchy monad_lib fail_lib state_lib trace_lib.
Require Import monad_transformer monad_model.

(**md**************************************************************************)
(* # Models of the Elgot monad                                                *)
(*                                                                            *)
(* The content of this file are also documented in the following paper:       *)
(* [1] Ryuji Kawakami, Jacques Garrigue, Takafumi Saikawa, Reynald Affeldt.   *)
(*     Monadic equational reasoning for while loops. Computer Software, 2026  *)
(*                                                                            *)
(* ## Combination of the Elgot monad with the state monad transformer         *)
(*                                                                            *)
(* ## Combination of the Elgot monad with the exception monad transformer     *)
(*                                                                            *)
(* ## Model for elgotAssertMonad                                              *)
(*                                                                            *)
(* This monad is an Elgot monad satisfying equalities to prove partial        *)
(* correctness. It is the transformed Elgot monad using exception monad       *)
(* transformer.                                                               *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.

Local Notation writer := WriterFunctor.acto.
Local Notation reader := ReaderMonad.acto.

(* TODO: move? *)
Lemma reader_map {S A B} (f : A -> B) (m : S -> A) : (reader S # f) m = f \o m.
Proof. by []. Qed.

Lemma writer_map {S A B} (f : A -> B) (m : writer S A) :
  (writer S # f) m = let (a, s) := m in (f a, s).
Proof. by []. Qed.

Definition dist1 {S X Y} (s : writer S (Y + X)) : writer S Y + writer S X :=
  let (yx, s) := s in
  match yx with inl y => inl (y, s) | inr x => inr (x, s) end.

(* NB: not used *)
Definition dist2 {S X Y} (xy : writer S Y + writer S X) : writer S (Y + X) :=
  match xy with inl (y, s) => (inl y, s) | inr (x, s) => (inr x, s) end.

Hint Extern 0 (wBisim _ _) => setoid_reflexivity : core.

Module ElgotS.
Section elgotS.
Variables (S : UU0) (M : elgotMonad).

(* was DS in [1] *)
Local Notation elgotS := (MS S M).

Lemma elgotSE {X} : elgotS X = (reader S \o M \o writer S) X.
Proof. by []. Qed.

Lemma elgotS_map {X Y} (f : X -> Y) : elgotS # f = (reader S \o M \o writer S) # f.
Proof.
apply: boolp.funext => x.
rewrite -compA FCompE FCompE//= reader_map.
apply: boolp.funext => s //=.
rewrite !fmapE//=.
congr bind.
by apply: boolp.funext => -[].
Qed.

(* was wBisimDS in [1] (now it is ElgotS.wB) *)
Definition wB A (a b : elgotS A) := forall s, a s ≈ b s.
Local Notation "a '≈' b" := (wB a b).

Section elgotS_wB.
Context {A : UU0}.
Implicit Type d : elgotS A.

Lemma refl d : d ≈ d. Proof. by move=> s; exact: wBisim_refl. Qed.

Lemma sym d1 d2 : d1 ≈ d2 -> d2 ≈ d1.
Proof. by move=> ? ?; exact: wBisim_sym. Qed.

Lemma trans d1 d2 d3 : d1 ≈ d2 -> d2 ≈ d3 -> d1 ≈ d3.
Proof. by move=> ? H ?; exact/wBisim_trans/H. Qed.

End elgotS_wB.

Section elgotS_lang.
Context {A B : UU0}.
Implicit Type d : elgotS A.

Lemma bindl (f : A -> elgotS B) d1 d2 : d1 ≈ d2 -> (d1 >>= f) ≈ (d2 >>= f).
Proof. by rewrite /wB => Hd s /=; rewrite !MS_bindE; exact: bindmwB. Qed.

Lemma bindr (f g : A -> elgotS B) d :
  (forall a, f a ≈ g a) -> (d >>= f) ≈ (d >>= g).
Proof. by move=> Hfg s /=; rewrite !MS_bindE /=; apply: bindfwB => -[]. Qed.

(* was whileDS in [1] (now it is ElgotS.while) *)
Definition while (body : A -> elgotS (B + A)) :=
  curry (while (M # dist1 \o uncurry body)).

Lemma whilel (f g : A -> elgotS (B + A)) (a : A) :
  (forall a, f a ≈ g a) -> while f a ≈ while g a.
Proof.
rewrite /wB /while /uncurry /curry => Hfg s.
apply: whilewB => -[a' s'] /=.
rewrite !fmapE /=.
exact: bindmwB.
Qed.

Lemma fixpoint (f : A -> elgotS (B + A)) (a : A) :
  while f a ≈ (f a >>= sum_rect (fun=> elgotS B) Ret (while f)).
Proof.
move=> s.
rewrite /while /curry /dist1/= MS_bindE /uncurry/= fixpointwB/= fmapE !bindA.
by apply: bindfwB=> -[[b'|a'] s'] /=; rewrite bindretf.
Qed.

End elgotS_lang.

Lemma naturality {A B C} (f : A -> elgotS (B + A)%type) (g : B -> elgotS C) (a : A) :
  bindS (while f a) g ≈
  while (fun y => f y >>= sum_rect (fun => elgotS (C + A))
                           (elgotS # inl \o g)
                           (elgotS # inr \o Ret)) a.
Proof.
rewrite /bindS /while /curry /uncurry => s //=.
rewrite naturalitywB /=.
apply: whilewB => -[] s' a' /=.
rewrite fmapE fmapE /=MS_bindE !bindA.
apply: bindfwB => sba //=.
rewrite /dist1 /uncurry bindretf.
case: sba => [[b''|a''] s''] /=.
- rewrite elgotS_map -compA FCompE FCompE reader_map/= fmapE fmapE bindA.
  apply: bindfwB => cs /=.
  rewrite bindretf /= writer_map /=.
  by case: cs.
- rewrite elgotS_map -compA FCompE FCompE reader_map/= fmapE fmapE bindA.
  apply: bindfwB => cs/=.
  rewrite bindretf /= writer_map /=.
  by case: cs.
Qed.

Lemma codiagonal {A B} (f : A -> elgotS ((B + A) + A)) (a : A) :
  while ((elgotS # ((sum_rect (fun => (B + A)%type) idfun inr))) \o f) a
  ≈
  while (while f) a.
Proof.
rewrite /while /curry /wB => s.
setoid_symmetry.
apply: wBisim_trans.
  apply whilewB => -[] s' a' /=.
  by rewrite /uncurry fmapE naturalitywB.
rewrite -codiagonalwB elgotS_map.
apply: whilewB => -[] a'' s'' //=.
rewrite //= !fmapE.
have -> : ((reader S \o M) \o writer S) # sum_rect (fun=> (B + A)%type) idfun inr =
          reader S # (M # (writer S # sum_rect (fun=> (B + A)%type) idfun inr)).
  by rewrite -compA FCompE.
rewrite reader_map /= fmapE !bindA.
by apply: bindfwB => -[[[bl|al']|al] sl]; rewrite !bindretf /= fmapE !bindretf.
Qed.

Lemma uniform {A B C} (f : A -> elgotS (B + A)) (g : C -> elgotS (B + C))
    (h : C -> A) :
  (forall c, f (h c) ≈
             g c >>= sum_rect (fun => elgotS (B + A))
                                       ((elgotS # inl) \o Ret)
                                       ((elgotS # inr) \o Ret \o h)) ->
  forall c, while f (h c) ≈ while g c.
Proof.
move=> H c s.
rewrite /while /curry /=.
set h' := fun cs : C * S => let (c, s) := cs in (h c, s).
have -> : (h c, s) = h' (c, s) by [].
apply: (uniformwB _ _ _ _ _ h') => -[c' s'].
rewrite {}/h' /= fmapE (H c') fmapE /= !bindA.
by apply: bindfwB => -[[?|?] ?];
  rewrite /=bindretf fmapE !bindretf/= fmapE bindretf.
Qed.

HB.instance Definition _ := @hasWBisim.Build elgotS wB
  (@refl) (@sym) (@trans) (@bindl) (@bindr).

HB.instance Definition _ := @isMonadElgot.Build elgotS (@while)
  (@whilel) (@fixpoint) (@naturality) (@codiagonal) (@uniform).

End elgotS.
End ElgotS.
(*HB.export ElgotS.*)

Module ElgotX.
Section elgotX.
Variable M : elgotMonad.

(* was DE in [1] *)
Notation elgotX := (MX unit M).

(* was DEA in [1] *)
Definition elgotXA {A B} : elgotX (A + B) -> M ((unit + A) + B )%type :=
  M # (fun uab => match uab with
                 | inl u => inl (inl u)
                 | inr ab => match ab with
                            |inl a => inl (inr a)
                            |inr b => inr b
                            end
                 end).

(* was whileDE in [1] (now it is ElgotX.while) *)
Definition while {A B} (body : A -> elgotX (B + A)) (x : A) : elgotX B :=
  while (elgotXA \o body) x.

Definition wB {A} (d1 d2 : elgotX A) := wBisim d1 d2.
Local Notation "a '≈' b" := (wB a b).
Hint Extern 0 (wB _ _) => setoid_reflexivity : core.

Lemma refl A (a : elgotX A) : a ≈ a. Proof. exact: wBisim_refl. Qed.

Lemma sym A (d1 d2 : elgotX A) : d1 ≈ d2 -> d2 ≈ d1.
Proof. exact: wBisim_sym. Qed.

Lemma trans A (d1 d2 d3 : elgotX A) : d1 ≈ d2 -> d2 ≈ d3 -> d1 ≈ d3.
Proof. exact: wBisim_trans. Qed.

Lemma bindXE {A B} (f : A -> elgotX B) (d : elgotX A) :
  d >>= f =
  @bind M _ _ d (fun (c : unit + A) => match c with inl z => Ret (inl z) | inr x => f x end).
Proof. by rewrite{1}/bind/=/bindX. Qed.

Lemma bindl {A B} (f : A -> elgotX B) (d1 d2 : elgotX A) :
  d1 ≈ d2 -> d1 >>= f ≈ d2 >>= f.
Proof. by move => Hd12; rewrite bindXE (bindmwB _ _ _ _ _ Hd12). Qed.

Lemma bindr {A B} (f g : A -> elgotX B) (d : elgotX A) :
  (forall a, f a ≈ g a) -> d >>= f ≈ d >>= g.
Proof.
move => H.
rewrite! bindXE.
set f' := fun c => _.
set g' := fun c => _.
rewrite (bindfwB _ _ f' g') // => a.
subst f' g'.
by case: a.
Qed.

Lemma fixpoint {A B} (f : A -> elgotX (B + A)) (a : A) :
  while f a ≈ f a >>= sum_rect (fun => elgotX B ) Ret (while f).
Proof.
rewrite /while /elgotXA fixpointwB /= fmapE /= bindA.
apply (bindfwB _ _ _ _ (f a)) => uba.
by case: uba => [u|[b'|a']] /=; rewrite bindretf.
Qed.

Lemma naturality {A B C} (f : A -> elgotX (B + A)) (g : B -> elgotX C) (a : A) :
  while f a >>= g ≈
  while (fun y => f y >>= sum_rect (fun => elgotX (C + A))
                                     (elgotX # inl \o g)
                                     (elgotX # inr \o Ret)) a.
Proof.
rewrite /while /elgotXA bindXE naturalitywB.
apply: whilewB => a' /=.
rewrite fmapE fmapE !bindA.
apply: (bindfwB _ _ _ _ (f a')).
move=> [u|[b''|a'']] /=.
- by rewrite !bindretf /= fmapE bindretf.
- rewrite !bindretf /= fmapE /= fmapE bindA.
  by apply: bindfwB => -[u|c]; rewrite bindretf.
- by rewrite bindretf /= !fmapE !bindretf.
Qed.

Lemma codiagonal {A B} (f : A -> elgotX ((B + A) + A)) (a : A) :
  while ((elgotX # (sum_rect (fun => (B + A)%type) idfun inr)) \o f ) a
  ≈
  while (while f) a.
Proof.
rewrite /while /elgotXA/=.
set g := {2} (fun uab => _).
setoid_symmetry.
apply: wBisim_trans.
  apply whilewB => a' /=.
  set m := {1}(hierarchy.while _ ).
  by rewrite (fmapE g (m a')) naturalitywB.
rewrite -codiagonalwB.
apply whilewB => a' /=.
rewrite !fmapE !bindA.
apply: bindfwB.
by move=> [u|[[b|a1]|a2]] /=; rewrite !bindretf /= fmapE bindretf /= bindretf.
Qed.

Lemma whilel {A B} (f g : A -> elgotX (B + A)) (a : A) :
  (forall a, f a ≈ g a) -> while f a ≈ while g a.
Proof.
move=> Hfg.
rewrite /while /elgotXA.
apply: whilewB => a' /=.
rewrite !fmapE.
apply: bindmwB.
exact: Hfg.
Qed.

Lemma uniform {A B C} (f : A -> elgotX (B + A)) (g : C -> elgotX (B + C)) (h : C -> A) :
  (forall c, f (h c) ≈ (g c >>= sum_rect (fun => elgotX (B + A))
                                 ((elgotX # inl) \o Ret)
                                 ((elgotX # inr) \o Ret \o h))) ->
  forall c, while f (h c) ≈ while g c.
Proof.
move=> H c.
rewrite /while.
apply: (uniformwB _ _ _ (elgotXA \o f)) => c' /=.
rewrite /elgotXA/= !fmapE (H c') !bindA.
apply: bindfwB.
by move=> [x|[b''|c'']]; rewrite /= !bindretf /= fmapE !bindretf // fmapE bindretf.
Qed.

HB.instance Definition _ := MonadExcept.on elgotX.

HB.instance Definition _ := @hasWBisim.Build elgotX (@wB)
  refl sym trans (@bindl) (@bindr).

HB.instance Definition _ := @isMonadElgot.Build elgotX (@while)
  (@whilel) (@fixpoint) (@naturality) (@codiagonal) (@uniform).

Lemma catchl A (d1 d2 h : elgotX A) :
  d1 ≈ d2 -> catch d1 h ≈ catch d2 h.
Proof. by move=> Hd12; apply/bindmwB. Qed.

Lemma catchr A (d h1 h2 : elgotX A) :
  h1 ≈ h2 -> catch d h1 ≈ catch d h2.
Proof. by move=> h12; apply/bindfwB => -[]. Qed.

HB.instance Definition _ := @isMonadElgotExcept.Build elgotX catchl catchr.

End elgotX.
End ElgotX.
(*HB.export ElgotX.*)

Require Import delay_model.

Section elgot_assert.

Local Open Scope monae_scope.
Local Open Scope do_notation.

Notation M := (MX unit Delay).

Notation "a '≈e' b" := (ElgotX.wB a b) (at level 70).
Hint Extern 0 (ElgotX.wB _ _) => setoid_reflexivity : core.

Lemma ElgotXwhileE A B (body : A -> M (B + A)) x :
  ElgotX.while body x = DelayOps.while (@ElgotX.elgotXA Delay _ _ \o body) x.
Proof. by []. Qed.

Lemma assertE X x (p : pred X) : @assert M _ p x ≈e Ret x <-> (p x) = true.
Proof.
split.
  rewrite /assert; case: (p x) => //.
  rewrite guardF bindfailf /ElgotX.wB.
  move/wBisims_wBisim/Stop_wBisimsRet.
  by inversion 1.
rewrite /assert => ->.
by rewrite guardT bindskipf.
Qed.

HB.export ElgotX.

Lemma pcorrect X A x (p : pred (A + X)) (f : X -> M (A + X)) :
   p (inr x)  ->
   (forall x, p (inr x) ->
      f x >>= sum_rect (fun => M (A + X))
                  ((assert p) \o inl)
                  (assert p \o inr)
      ≈e
      f x >>= sum_rect (fun => M (A + X)) (Ret \o inl) (Ret \o inr)) ->
   bassert p (ElgotX.while f x >>= (Ret \o inl)) ≈e ElgotX.while f x >>= (Ret \o inl).
Proof.
move => Hx HInv.
case: (StopP (ElgotX.while f x)) =>
  [[[u' /Stop_wBisimsRet/wBisims_wBisim Hs
    |x' /Stop_wBisimsRet [n Hs]]]|/Diverge_wBisim_spinP Hs].
- by rewrite /bassert ElgotX.bindXE Hs !bindretf bindXE !bindretf.
- rewrite steps_Now in Hs.
  move: x x' Hx Hs.
  elim: n => [/=|n IH] x x' Hx;
             rewrite ElgotXwhileE whileE /ElgotX.elgotXA functions.compE fmapE.
  + case Hb: (f x) => [uxx|d].
    * case: uxx Hb => [u//|[y/=|y/=]] Hb;
                      rewrite bindretf/=bindretf.
      - by rewrite/bassert bindXE bindretf.
      - rewrite/bassert bindXE bindretf => _.
        move: (HInv x Hx).
        by rewrite Hb !bindretf.
      - by [].
    * by rewrite !bind_Later.
  + set d := f x.
    have : d ≈ f x by [].
    move: d.
    cofix CIH => d.
    case Hb: d => [uxx|d'].
      case: uxx Hb => [u//|[y/= Hd|y/= Hd]] Hb;
                      rewrite bindretf/=bindretf.
        rewrite/bassert bindXE bindretf => _.
        move: (HInv x Hx).
        by rewrite -Hb !bindretf /=.
      move: (HInv x Hx).
      rewrite !bindXE -Hb !bindretf/= => HH.
      move/IH => IH'.
      rewrite -!ElgotXwhileE.
      rewrite /bassert !bind_Later.
      rewrite wBisim_Later -bindXE.
      rewrite -{2}IH' /bassert.
        by [].
      by move/assertE: HH.
    rewrite/bassert !bindXE !bindA !bind_Later /= => Hd' Hs.
    apply wBLater.
    rewrite -!bindA -bindXE -/(bassert p _).
    apply: CIH.
      by rewrite -Hd' wBisim_Later.
    apply: monotonicity_steps'.
    by rewrite /= /bassert bindA Hs.
- rewrite !bindXE /bassert Hs.
  apply: wBisim_trans.
  + apply Diverge_wBisim_spinP.
    rewrite bindA.
    exact: Diverge_bindspinf.
  + apply: wBisim_sym.
    apply Diverge_wBisim_spinP.
    exact: Diverge_bindspinf.
Qed.

HB.instance Definition _ := @isMonadElgotAssert.Build M (@pcorrect).

End elgot_assert.
