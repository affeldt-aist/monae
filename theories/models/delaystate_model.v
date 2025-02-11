Require Import JMeq.
From mathcomp Require Import all_ssreflect.
From mathcomp Require boolp.
From HB Require Import structures.
Require Import hierarchy monad_lib fail_lib state_lib trace_lib.
Require Import monad_transformer.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.

Module TensorS.
Section tensors.
Variable S:UU0.

Definition tensorS := fun (A : UU0) => (A * S)%type.
Definition actmt (X Y : UU0) : (X -> Y) -> tensorS X -> tensorS Y := (fun f : X -> Y =>  (fun xs : X * S => match xs with (x, s) => (f x, s) end)).
Let tensor_id : FunctorLaws.id actmt.
Proof.
rewrite/actmt/FunctorLaws.id => B.
apply boolp.funext => x.
by case: x.
Qed.
Let tensor_o : FunctorLaws.comp actmt.
Proof.
rewrite/actmt/FunctorLaws.comp => X Y Z g h.
apply boolp.funext => x.
by case: x.
Qed.

HB.instance Definition _:= isFunctor.Build tensorS tensor_id tensor_o.
End tensors.
End TensorS.
HB.export TensorS.

Module HomS.
Section homs.
Variable S : UU0.

Definition homS := fun (A : UU0) => (S -> A).
Definition actmh (X Y : UU0) : (X -> Y) -> homS X -> homS Y := fun (f: X -> Y) => fun (m: S ->X) => f \o m.
Let hom_id : FunctorLaws.id actmh.
Proof.
rewrite/actmh/FunctorLaws.id => B.
by apply boolp.funext => x.
Qed.
Let hom_o : FunctorLaws.comp actmh.
Proof.
rewrite/actmh/FunctorLaws.comp => X Y Z g h.
by apply boolp.funext => x.
Qed.

HB.instance Definition _:= isFunctor.Build homS hom_id hom_o.
End homs.
End HomS.
HB.export HomS.

Module StateTdelay.
Section stateTdelay.
Variable S : UU0.
Variable M : delayMonad.

Hint Extern 0 (wBisim _ _) => setoid_reflexivity.

Notation "a '≈' b" := (wBisim a b).
Notation DS := (MS S M).

Lemma DSE {X}: DS X  = (homS S \o M \o tensorS S) X.
Proof. by rewrite/DS/MS/homS/tensorS => //=. Qed.
Lemma homSmap {A B} (f : A -> B) (m : S -> A) : (homS S # f) m = f \o m.
Proof. by []. Qed.
Lemma tensorSmap {A B} (f : A -> B) (m : tensorS S A) : (tensorS S # f) m = let (a, s) := m in (f a, s).
Proof. by []. Qed.
Lemma DSmapE {X Y} (f : X -> Y) : DS # f = (homS S \o M \o tensorS S) # f.
Proof.
apply boolp.funext => x.
rewrite -compA FCompE FCompE //= homSmap.
apply boolp.funext => s //=.
rewrite fmapE//=/bindS/retS//=/uncurry/curry fmapE/=.
congr bind.
apply boolp.funext => xs.
by case: xs => x' s' //=.
Qed.
Definition dist1 {X Y} (s : tensorS S (Y + X)) : (tensorS S Y) + (tensorS S X) :=
  let (yx, s) := s in match yx with |inl y => inl (y, s) | inr x => inr (x, s) end.
Definition dist2 {X Y} (xy : (tensorS S Y) + (tensorS  S X)) : tensorS S (Y + X) :=
  match xy with | inl (y, s) => (inl y, s) | inr (x, s) => (inr x, s) end.

Definition whileDS {X Y} (body : X -> DS (Y + X)) := curry (while (M # dist1 \o uncurry body)).
Definition wBisimDS A (a b : DS A) := forall s, wBisim (a s) (b s).

Section wBisimDS.
Notation "a '≈' b" := (wBisimDS a b).
Lemma wBisimDS_refl A (a : DS A) : a ≈ a.
Proof. move => s. apply wBisim_refl. Qed.
Lemma wBisimDS_sym A (d1 d2 : DS A) : d1 ≈ d2 -> d2 ≈ d1.
Proof. move => Hs s. exact: wBisim_sym. Qed.
Lemma wBisimDS_trans A (d1 d2 d3 : DS A) : d1 ≈ d2 -> d2 ≈ d3 -> d1 ≈ d3.
Proof. move => H1 H2 s. exact/wBisim_trans/H2. Qed.
End wBisimDS.

Lemma fixpointDSE {A B} (f : A -> DS (B + A)%type) :
forall (a : A), wBisimDS (whileDS f a) ( f a >>= (sum_rect (fun => DS B ) Ret (whileDS f))).
Proof.
move => a s.
rewrite/whileDS/curry/dist1/= MS_bindE/uncurry/= fixpointE/= fmapE !bindA.
apply bindfwB => bas.
case: bas => [[b'|a'] s'] /=; by rewrite bindretf.
Qed.
Lemma naturalityDSE {A B C} (f : A -> DS (B + A)%type) (g : B -> DS C) (a : A) :
   wBisimDS (bindS (whileDS f a) g) (whileDS (fun y => (f y) >>= (sum_rect (fun => DS (C + A)) (DS # inl \o g) (DS # inr \o (@ret DS A )))) a).
Proof.
rewrite/bindS/whileDS/curry/uncurry => s //=.
rewrite naturalityE /=.
apply whilewB => sa.
case: sa => s' a' /=.
rewrite fmapE fmapE /=MS_bindE !bindA.
apply bindfwB => sba //=.
rewrite/dist1/uncurry bindretf.
case: sba => [[b''|a''] s''] /=.
- rewrite DSmapE -compA FCompE FCompE homSmap/= fmapE fmapE bindA.
  apply bindfwB => cs /=.
  rewrite bindretf /= tensorSmap /=.
  by case: cs => c cs /=.
- rewrite DSmapE -compA FCompE FCompE homSmap/= fmapE fmapE bindA.
  apply bindfwB => cs/=.
  rewrite bindretf /= tensorSmap /=.
  by case: cs => c cs.
Qed.
Lemma codiagonalDSE {A B} (f : A -> DS ((B + A) + A)) (a : A) :
   wBisimDS (whileDS ((DS # ((sum_rect (fun => (B + A)%type) idfun inr)))  \o f ) a) (whileDS (whileDS f) a).
Proof.
rewrite/whileDS/curry/wBisimDS => s.
setoid_symmetry.
apply: wBisim_trans.
  apply whilewB => sa /=.
  case: sa => s' a' /=.
  by rewrite /uncurry fmapE naturalityE /=.
rewrite -codiagonalE DSmapE.
apply whilewB => sa /=.
case: sa => a'' s'' //=.
rewrite //=!fmapE.
have -> : ((homS S \o M) \o tensorS S) # sum_rect (fun=> (B + A)%type) idfun inr = homS S # (M # (tensorS S # sum_rect (fun=> (B + A)%type) idfun inr)).
  by rewrite -compA FCompE.
rewrite homSmap /= fmapE !bindA.
apply bindfwB => sbaa.
case: sbaa => [[[bl|al']|al] sl]; by rewrite !bindretf /= fmapE bindretf /= bindretf.
Qed.
Lemma whilewBDS {A B} (f g : A -> DS (B + A)) (a : A) : (forall a, wBisimDS (f a) (g a)) -> wBisimDS (whileDS f a) (whileDS g a).
Proof.
rewrite/wBisimDS/whileDS/uncurry/curry => Hfg s.
apply whilewB => sa /=.
rewrite! fmapE /=.
case: sa => a'' s'' /=.
by apply bindmwB.
Qed.
Lemma bindmwBDS {A B} (f : A -> DS B) (d1 d2 : DS A) : wBisimDS d1 d2 -> wBisimDS (d1 >>= f) (d2 >>= f).
Proof. by rewrite /wBisimDS => Hd s /=;rewrite !MS_bindE;apply bindmwB. Qed.
Lemma bindfwBDS {A B} (f g : A -> DS B) (d : DS A) : (forall a, wBisimDS (f a) (g a)) -> wBisimDS (d >>= f) (d >>= g).
Proof. by rewrite /wBisimDS => Hfg s /=; rewrite !MS_bindE /=; apply bindfwB => a's'; case: a's'. Qed.

Lemma uniformEDS {A B C} (f : A -> DS (B + A)) (g : C -> DS (B + C)) (h : C -> A) :
  (forall c, f (h c) = g c >>= sum_rect (fun => DS (B + A)) ((DS # inl) \o Ret) ((DS # inr) \o Ret \o h)) ->
  forall c, wBisimDS ((whileDS f) (h c)) (whileDS g c).
Proof.
move => H c s.
rewrite/whileDS/curry /=.
set h' := fun (cs : C * S) => let (c, s) := cs in (h c, s).
have -> : (h c, s) = h' (c, s). by [].
apply: (uniformE _ _ _ _ _ h') => cs.
case: cs => [c' s'].
subst h'.
rewrite /= fmapE (H c') fmapE /= !bindA.
apply eq_bind => bcs.
by case: bcs =>  [[?|?] ?]; rewrite /=bindretf fmapE !bindretf/= fmapE bindretf/=.
Qed.

HB.instance Definition _ := MonadState.on DS.
HB.instance Definition _ := @isMonadDelay.Build DS
  (@whileDS) (@wBisimDS) wBisimDS_refl wBisimDS_sym wBisimDS_trans (@fixpointDSE) (@naturalityDSE) (@codiagonalDSE)  (@bindmwBDS) (@bindfwBDS) (@whilewBDS) (@uniformEDS).

End stateTdelay.
End StateTdelay.
HB.export StateTdelay.
