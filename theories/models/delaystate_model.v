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
Definition tensorS := fun (A: UU0) => (A * S)%type.
Definition actmt (X Y: UU0):(X -> Y) -> tensorS X -> tensorS Y:=(fun f: X -> Y =>  (fun xs:X * S => match xs with (x, s) => (f x, s) end)).
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
Variable S:UU0.
Definition homS := fun (A:UU0) => (S -> A).
Definition actmh (X Y: UU0):(X -> Y) -> homS X -> homS Y := fun (f: X -> Y) => fun (m: S ->X) => f \o m.
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
Variable S: UU0.
Variable M: delayMonad.
Hint Extern 0 (wBisim _ _) => setoid_reflexivity.
Notation "a '≈' b" := (wBisim a b).
Notation DS := (MS S M).
Lemma DSE {X}: DS X  = (homS S \o M \o tensorS S) X.
Proof. by rewrite/DS/MS/homS/tensorS => //=. Qed.
Lemma homSmap {A B} (f: A -> B) (m:S -> A) : (homS S # f) m = f \o m.
Proof. by []. Qed.
Lemma tensorSmap {A B} (f: A -> B) (m: tensorS S A) : (tensorS S # f) m = let (a, s) := m in (f a, s).
Proof. by []. Qed.
Lemma DSmapE {X Y} (f: X -> Y): DS # f = (homS S \o M \o tensorS S) # f.
Proof.
apply boolp.funext => x.
rewrite -compA FCompE FCompE //= homSmap.
apply boolp.funext => s //=.
rewrite fmapE//=/bindS/retS//=/uncurry/curry fmapE/=.
congr bind.
apply boolp.funext => xs.
by case: xs => x' s' //=.
Qed.
Definition dist1 {X Y} (s:tensorS S (Y + X)) :(tensorS S Y) + (tensorS S X) :=
  let (yx, s) := s in match yx with |inl y => inl (y,s) | inr x => inr (x,s) end.
Definition dist2 {X Y} (xy: (tensorS S Y) + (tensorS  S X)): tensorS S (Y + X) :=
  match xy with | inl (y, s) => (inl y,s) | inr (x, s) => (inr x,s) end.

Definition whileDS {X Y} (body: X -> DS (Y + X)) := curry (while (M # dist1 \o uncurry body)).
(*
Definition unitS {X}: X -> homS S (tensorS S X) := fun (x: X) => fun (s: S) => (x, s).
Definition counitS {X}: tensorS S (homS S X) -> X:= fun fs => let (f,s) := fs in f s.*)
(*
(*curry*)
Definition adjlr {X Y}:((tensorS S X) -> Y) -> (X -> (homS S Y)) := fun f => homS S # f \o unitS.
(*uncurry*)
Definition adjrl {X Y}:(X -> (homS S Y)) -> ((tensorS S X) -> Y) := fun f => counitS \o tensorS S # f.
Lemma adjE1 {X Y} : (@adjlr X Y) \o (@adjrl X Y) = idfun.
Proof. by apply boolp.funext => f //=. Qed.
Lemma adjE2 {X Y} : (@adjrl X Y) \o (@adjlr X Y) = idfun.
Proof. by apply boolp.funext => f /=; apply boolp.funext => sx; case: sx. Qed.
*)

Definition wBisimDS A (a b: DS A) := forall s, wBisim (a s) (b s).
Section wBisimDS.
Notation "a '≈' b" := (wBisimDS a b).
Lemma wBisimDS_refl A (a: DS A): a ≈ a.
Proof. move => s. apply wBisim_refl. Qed.
Lemma wBisimDS_sym A (d1 d2: DS A): d1 ≈ d2 -> d2 ≈ d1.
Proof. move => Hs s. exact: wBisim_sym. Qed.
Lemma wBisimDS_trans A (d1 d2 d3: DS A): d1 ≈ d2 -> d2 ≈ d3 -> d1 ≈ d3.
Proof. move => H1 H2 s. exact/wBisim_trans/H2. Qed.
End wBisimDS.
(*
Lemma adjlr_preserve {A B} (f g: tensorS S A -> M (tensorS S B)): (forall s a, wBisim (f (s, a)) (g(s, a))) -> forall a, wBisimDS (adjlr f a) (adjlr g a).
Proof. by rewrite/wBisimDS/adjlr => H a s //=; rewrite //=homSmap homSmap//=/unitS. Qed.*)
(*
Lemma joinE {A}: (@join DS) A  = (homS S # ((@join Delay) (tensorS S A) ) ) \o ((homS S \o Delay) # counitS ) .
Proof.
apply boolp.funext => m.
apply boolp.funext => s.
rewrite FCompE //= homSmap homSmap //= actm_bind.
have -> : (cofix bind_ (u : Delay (Delay (tensorS S A))) : Delay (tensorS S A) := match u with
                                                                                             | DNow x => x
                                                                                             | DLater m' => DLater (bind_ m')
                                                                                             end) (m s >>= (DNow (A:=Delay (tensorS S A)) \o counitS ))
= (m s >>= (@ret Delay _ \o counitS)) >>= idfun.
  by [].
rewrite bindA //=.
congr bind.
apply boolp.funext => xs.
by rewrite bindretf //= /counitS/uncurry //=.
Qed.
Lemma sumrectDSE' {A X}(f: X -> DS (A + X)%type) :
  (homS S \o Delay) # counitS \o  DS # sum_rect (fun =>  DS A) Ret (homS S # while ((Delay # dist1 \o adjrl f)) \o unitS )
= (homS S \o Delay) # (counitS \o tensorS S # (sum_rect (fun =>  DS A) Ret (homS S # while ((Delay # dist1 \o adjrl f)) \o unitS))).
Proof.
by rewrite DSmapE functor_o.
Qed.
Lemma sumrectDSE'' {A X}(f: X -> DS (A + X)%type):
counitS \o (tensorS S # (sum_rect (fun => DS A) Ret (homS S # (while ((Delay # dist1 \o adjrl f))) \o unitS))) =
 sum_rect (fun => (Delay \o tensorS S) A) Ret (while (Delay # dist1 \o adjrl f)) \o dist1.
Proof. apply boolp.funext => ts; case: ts => ax s //=; case: ax => [a|x] //=. Qed.
Lemma sumrectDSE {A X}  (f: X -> DS (A + X)%type) :
  (homS S \o Delay) # counitS \o  DS # sum_rect (fun =>  DS A) Ret (homS S # while ((Delay # dist1 \o adjrl f)) \o unitS )  =
(homS S \o Delay) # sum_rect (fun => (Delay \o tensorS S) A) Ret (while ((Delay # dist1 \o adjrl f))) \o  (homS S \o Delay) # dist1.
Proof.
by rewrite sumrectDSE' -functor_o sumrectDSE''. Qed.
Lemma tunitl  {A X}  (f: X -> DS (A + X)%type) :
 ((homS S \o Delay) # dist1) \o f = ((homS S \o Delay) # dist1) \o (homS S # adjrl f) \o unitS.
Proof. apply boolp.funext => x; rewrite/unitS //= testhomS => //=. Qed.
Lemma tildaf {A X} (f: X -> DS (A + X)%type) :
 ((homS S \o Delay) # dist1) \o (homS S # adjrl f) = homS S # ((Delay # dist1) \o adjrl f).
Proof. by apply boolp.funext => x //= homSmap homSmap FCompE homSmap homSmap. Qed.
Lemma fixpointDSE' {A X} (f: X -> DS (A + X)) (sx: tensorS S X): wBisim (((@join Delay) _ \o (Delay # (sum_rect (fun => (Delay \o tensorS S) A) Ret (while (Delay # dist1 \o adjrl f)))) \o (Delay # dist1 \o adjrl f)) sx) (while ((Delay # dist1 \o adjrl f)) sx).
Proof.
rewrite! compE.
set g := Delay # _ \o _ _. 
rewrite -bindE //= wBisim_sym.
by apply fixpointE.
Qed.
Lemma fixpointDSE'' {A X} (f: X -> DS (A + X)) (x: X): ( f x >>= (sum_rect (fun => DS A ) Ret (whileDS f))) = 
adjlr(((Join \o Delay # sum_rect (fun=> (Delay \o tensorS S) A) Ret (while (Delay # dist1 \o adjrl f))) \o (Delay # dist1 \o adjrl f))) x.
Proof.
rewrite bindE joinE -[LHS]compE.
set g := homS S # Join.
rewrite -(compA g ((homS S \o Delay) # counitS)  (DS # sum_rect (fun=> DS A) Ret (whileDS f))) sumrectDSE -[LHS]compE.
set h := (homS S \o Delay ) # _ .
set k := (homS S \o Delay ) # _ .
rewrite -(compA g (h \o k) f) -(compA h k f).
subst k.
rewrite tunitl tildaf.
subst g h.
rewrite FCompE.
set p := DelayMonad_Delay__canonical__hierarchy_Functor #  _.
set q := Delay # dist1 \o _.
by rewrite compA compA -functor_o -functor_o /adjlr.
Qed.
*)
Lemma fixpointDSE {A B} (f: A -> DS (B + A)%type):
forall (a:A), wBisimDS (whileDS f a) ( f a >>= (sum_rect (fun => DS B ) Ret (whileDS f))).
Proof.
move => a s.
rewrite/whileDS/curry/dist1/= MS_bindE/uncurry/= fixpointE/= fmapE !bindA.
apply bindfwB => bas.
case: bas => [[b'|a'] s'] /=.
- by rewrite bindretf.
- by rewrite bindretf.
Qed.
Lemma naturalityDSE {A B C} (f: A -> DS (B + A)%type) (g: B -> DS C)(a:A):
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
Lemma codiagonalDSE {A B} (f: A -> DS ((B + A) + A))(a:A):
   wBisimDS (whileDS ((DS # ((sum_rect (fun => (B + A)%type) idfun inr)))  \o f ) a) (whileDS (whileDS f) a).
Proof.
rewrite/whileDS/curry/wBisimDS => s.
setoid_symmetry.
apply: wBisim_trans.
- apply whilewB => sa /=.
  case: sa => s' a' /=.
  by rewrite /uncurry fmapE naturalityE /=.
- rewrite -codiagonalE DSmapE.
  apply whilewB => sa /=.
  case: sa => a'' s'' //=.
  rewrite //=!fmapE.
  have -> : ((homS S \o M) \o tensorS S) # sum_rect (fun=> (B + A)%type) idfun inr = homS S # (M # (tensorS S # sum_rect (fun=> (B + A)%type) idfun inr)).
    by rewrite -compA FCompE.
  rewrite homSmap /= fmapE !bindA.
  apply bindfwB => sbaa.
  case: sbaa => [[[bl|al']|al] sl]; by rewrite !bindretf /= fmapE bindretf /= bindretf.
Qed.
Lemma whilewBDS {A B} (f g: A -> DS (B + A)) (a: A) : (forall a, wBisimDS (f a) (g a)) -> wBisimDS (whileDS f a) (whileDS g a).
Proof.
rewrite/wBisimDS/whileDS/uncurry/curry => Hfg s.
apply whilewB => sa /=.
rewrite! fmapE /=.
case: sa => a'' s'' /=.
by apply bindmwB.
Qed.
Lemma bindmwBDS {A B} (f: A -> DS B) (d1 d2: DS A): wBisimDS d1 d2 -> wBisimDS (d1 >>= f) (d2 >>= f).
Proof. by rewrite /wBisimDS => Hd s /=;rewrite !MS_bindE;apply bindmwB. Qed.
Lemma bindfwBDS {A B} (f g: A -> DS B) (d: DS A): (forall a, wBisimDS (f a) (g a)) -> wBisimDS (d >>= f) (d >>= g).
Proof. by rewrite /wBisimDS => Hfg s /=;rewrite ! MS_bindE /=;apply bindfwB => a's';case: a's'. Qed.
HB.instance Definition _ := MonadState.on DS.
HB.instance Definition _ := @isMonadDelay.Build DS
  (@whileDS) (@wBisimDS) wBisimDS_refl wBisimDS_sym wBisimDS_trans (@fixpointDSE) (@naturalityDSE) (@codiagonalDSE)  (@bindmwBDS) (@bindfwBDS) (@whilewBDS).
(*mathcompで例を探す ex. ssr_num realdomaintype *)

End stateTdelay.
Section stateTdelayExample.
Require Import delay_monad_model.
Local Open Scope do_notation.
Print Delay.
Let DSD := MS (seq nat) Delay.
HB.instance Definition _ := MonadState.on DSD.
About DSD.
Check (DSD: stateMonad (seq nat)).
Let stepsds {A S} (n: nat) (ds: MS S Delay A) (s: S):= steps n (ds s).
Definition factds_body: nat -> MS nat Delay (unit + nat)%type :=
fun (m:nat) => ((do s <- (@get nat (MS nat Delay)) ;
              match m with
             |O => do _ <- (@put nat (MS nat Delay) s) ;
                 (@ret (MS nat Delay) _ (inl tt))
           |m'.+1 => do _<- (@put nat (MS nat Delay) (m * s )) ; (@ret (MS nat Delay) _ (inr m'))
         end)).

Definition factds := whileDS factds_body.
Compute (stepsds 20 (factds 5) 1).
Definition bubblesortd_body1 (i: nat)(j: nat): DSD (unit + nat)%type :=
  do s <- get;
  if i < j then let sj := nth 0 s j in let sjp := nth 0 s (j-1) in
                                       if sj < sjp then do _ <- put (set_nth 0 s (j-1) sj);
                                                        do s' <- get;
                                                        do _ <- put (set_nth 0 s' j (sjp)); (@ret DSD _ (inr (j-1)))
                                       else (@ret DSD _ (inr (j-1)))
  else (@ret DSD _ (inl tt)).
Definition bubblesortd_body2 (i: nat): DSD (unit + nat)%type :=
do s <- get;
let len := length s in if i == len
                       then (@ret DSD _ (inl tt))
                       else (@bind DSD _ _ )((whileDS (bubblesortd_body1 i)) (len - 1))(fun _ =>  (@ret DSD _ (inr (i.+1)))).
Definition bubblesortd := whileDS bubblesortd_body2.
Let testseq2 := 8::4::3::7::6::5::2::1::nil.
Compute (stepsds 100 (bubblesortd 0) testseq2).
Local Notation sorted := (sorted <=%O).
(*runSTがいる？*)

Lemma bubblesort_sorted (s: seq nat)(x: nat): exists (s': seq  nat), (forall i, i.+1 < size s' -> (nth x s' i) <= (nth x s' i.+1)) /\ wBisimDS (put s') ((@bind DSD _ _ )(put s) (fun _ => (bubblesortd 0))).
Abort.
End stateTdelayExample.
End StateTdelay.
HB.export StateTdelay.
