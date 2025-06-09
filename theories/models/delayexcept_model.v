(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2025 monae authors, license: LGPL-2.1-or-later               *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require boolp.
From HB Require Import structures.
Require Import monad_transformer hierarchy.

(**md**************************************************************************)
(* # Combination of the Delay monad with the exception monad transformer      *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.

Module exceptTdelay.
Section exceptTdelay.
Variable M : delayMonad.
Notation DE := (MX unit M).

Definition DEA {A B} : DE (A + B) -> M ((unit + A) + B )%type :=
  M # (fun uab => match uab with
                 | inl u => inl (inl u)
                 | inr ab => match ab with
                            |inl a => inl (inr a)
                            |inr b => inr b
                            end
                 end).

Definition whileDE {A B} (body : A -> DE (B + A)) (x : A) : DE B :=
  while (DEA \o body) x.

Definition wBisimDE {A} (d1 d2 : DE A) := wBisim d1 d2.

Local Notation "a '≈' b" := (wBisimDE a b).

Lemma wBisimDE_refl A (a : DE A) : a ≈ a.
Proof. exact: wBisim_refl. Qed.

Lemma wBisimDE_sym A (d1 d2 : DE A) : d1 ≈ d2 -> d2 ≈ d1.
Proof. exact: wBisim_sym. Qed.

Lemma wBisimDE_trans A (d1 d2 d3 : DE A) :
  d1 ≈ d2 -> d2 ≈ d3 -> d1 ≈ d3.
Proof. exact: wBisim_trans. Qed.

Hint Extern 0 (wBisimDE _ _) => setoid_reflexivity.
Hint Extern 0 (wBisim _ _) => setoid_reflexivity.

Lemma bindXE {A B} (f : A -> DE B) (d : DE A) :
  d >>= f = (@bind M _ _ d (fun (c : unit + A) => match c with inl z => Ret (inl z) | inr x => f x end)).
Proof. by rewrite{1}/bind/=/bindX. Qed.

Lemma bindmwBDE {A B} (f : A -> DE B) (d1 d2 : DE A) :
  d1 ≈ d2 -> d1 >>= f ≈ d2 >>= f.
Proof. by move => Hd12; rewrite bindXE (bindmwB _ _ _ _ _ Hd12). Qed.

Lemma bindfwBDE {A B} (f g : A -> DE B) (d : DE A) :
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

Lemma fixpointDEE {A B} (f : A -> DE (B + A)) (a : A) :
  whileDE f a ≈ f a >>= sum_rect (fun => DE B ) (@ret DE B ) (whileDE f).
Proof.
rewrite /whileDE /DEA fixpointE /= fmapE /= bindA.
apply (bindfwB _ _ _ _ (f a)) => uba.
by case: uba => [u|[b'|a']] /=; rewrite bindretf.
Qed.

Lemma naturalityDEE {A B C} (f : A -> DE (B + A)) (g : B -> DE C) (a : A) :
  whileDE f a >>= g ≈
  whileDE (fun y => f y >>= sum_rect (fun => DE (C + A))
                                     (DE # inl \o g)
                                     (DE # inr \o (@ret DE A))) a.
Proof.
rewrite /whileDE /DEA bindXE naturalityE.
apply: whilewB => a' /=.
rewrite fmapE fmapE !bindA.
apply: (bindfwB _ _ _ _ (f a')).
move=> [u|[b''|a'']] /=.
- by rewrite !bindretf /= fmapE bindretf.
- rewrite !bindretf /= fmapE /= fmapE bindA.
  by apply: bindfwB => -[u|c]; rewrite bindretf.
- by rewrite bindretf /= !fmapE !bindretf.
Qed.

Lemma codiagonalDEE {A B} (f : A -> DE ((B + A) + A)) (a : A) :
  whileDE ((DE # (sum_rect (fun => (B + A)%type) idfun inr)) \o f ) a
  ≈
  whileDE (whileDE f) a.
Proof.
rewrite /whileDE /DEA/=.
set g := {2} (fun uab => _).
setoid_symmetry.
apply: wBisim_trans.
  apply whilewB => a' /=.
  set m := {1}(while _ ).
  by rewrite (fmapE g (m a')) naturalityE.
rewrite -codiagonalE.
apply whilewB => a' /=.
rewrite !fmapE !bindA.
apply: bindfwB.
by move=> [u|[[b|a1]|a2]] /= ; by rewrite  !bindretf /= fmapE bindretf /= bindretf.
Qed.

Lemma whilewBDE {A B} (f g : A -> DE (B + A)) (a : A) :
  (forall a, (f a) ≈ (g a)) -> whileDE f a ≈ whileDE g a.
Proof.
move=> Hfg.
rewrite /whileDE /DEA.
apply whilewB => a' /=.
rewrite !fmapE.
apply: bindmwB.
exact: Hfg.
Qed.

Lemma uniformDEE {A B C} (f : A -> DE (B + A)) (g : C -> DE (B + C)) (h : C -> A) :
  (forall c, f (h c) =
             (g c >>= sum_rect (fun => DE (B + A))
                               ((DE # inl) \o Ret)
                               ((DE # inr) \o Ret \o h))) ->
  forall c, whileDE f (h c) ≈ whileDE g c.
Proof.
move=> H c.
rewrite /whileDE.
apply: (uniformE _ _ _ (DEA \o f)) => c' /=.
rewrite /DEA/= !fmapE (H c') !bindA.
apply: eq_bind.
by move=> [x|[b''|c'']]; rewrite /= !bindretf /= fmapE !bindretf // fmapE bindretf.
Qed.

HB.instance Definition _ := MonadExcept.on DE.

HB.instance Definition _ := @hasWBisim.Build DE (@wBisimDE)
  wBisimDE_refl wBisimDE_sym wBisimDE_trans (@bindmwBDE) (@bindfwBDE).

HB.instance Definition _ := @isMonadDelay.Build DE (@whileDE)
  (@whilewBDE) (@fixpointDEE) (@naturalityDEE) (@codiagonalDEE) (@uniformDEE).

Lemma catchmwBDE A (d1 d2 h : DE A) :
  d1 ≈ d2 -> catch d1 h ≈ catch d2 h.
Proof. by move=> Hd12; apply/bindmwB. Qed.

Lemma catchhwBDE A (d h1 h2 : DE A) :
  h1 ≈ h2 -> catch d h1 ≈ catch d h2.
Proof. by move=> h12; apply/bindfwB => -[]. Qed.

HB.instance Definition _ := @isMonadDelayExcept.Build DE catchmwBDE catchhwBDE.

End exceptTdelay.
End exceptTdelay.
HB.export exceptTdelay.
