(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2020 monae authors, license: LGPL-2.1-or-later               *)
From HB Require Import structures.
Require Import Reals Lra.
From mathcomp Require Import all_ssreflect.
From mathcomp Require boolp Rstruct.
From infotheo Require Import ssrR Reals_ext proba.
From infotheo Require Import convex.
From infotheo Require necset.
Require Import monae_lib hierarchy monad_lib fail_lib.

(******************************************************************************)
(*             Definitions and lemmas for probability monads                  *)
(*                                                                            *)
(* uniform s == uniform choice from a sequence s with a probMonad             *)
(* mpair_uniform ==                                                           *)
(*   uniform choices are independent, in the sense that choosing              *)
(*   consecutively from two uniform distributions is equivalent to choosing   *)
(*   simultaneously from their cartesian product                              *)
(* bcoin p == a biased coin with probability p                                *)
(* Sample programs:                                                           *)
(*   arbcoin == arbitrary choice followed by probabilistic choice             *)
(*   coinarb == probabilistic choice followed by arbitrary choice             *)
(*                                                                            *)
(******************************************************************************)

Declare Scope proba_monad_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.
Local Open Scope reals_ext_scope.
Local Open Scope proba_monad_scope.

Require Import fdist.

Section convex.
Variable M : probMonad.
Variable A : Type.
Local Open Scope proba_scope.
Let choiceA : forall (p q : prob) (a b c : M A),
  let conv := (fun p (a b : choice_of_Type (M A)) => choice p A a b) in
   conv p a (conv q b c) = conv [s_of p, q] (conv [r_of p, q] a b) c.
Proof.
move=> p q a b c; apply: (choiceA p q).
by rewrite -fdist.p_is_rs fdist.s_of_pqE onemK.
Qed.

HB.instance Definition _ := @isConvexSpace.Build (M A)
  (Choice.class (choice_of_Type (M A)))
(fun p  => choice p A)
(choice1 _)
choicemm
choiceC
choiceA.

Lemma choice_conv p (x y : M A) : choice p A x y = conv p x y.
Proof. reflexivity. Qed.

End convex.

Lemma choiceACA {M : probMonad} T q p :
  @interchange (M T) (fun a b => a <|p|> b) (fun a b => a <|q|> b).
Proof. by move=> *; exact: convACA. Qed.

(* NB: the parameter def is because Coq functions are total *)
Fixpoint uniform {M : probMonad} {A : Type} (def : A) (s : seq A) : M A :=
  match s with
    | [::] => Ret def
    | [:: x] => Ret x
    | x :: xs => Ret x <| (/ IZR (Z_of_nat (size (x :: xs))))%:pr |> uniform def xs
  end.

Lemma uniform_nil (M : probMonad) (A : Type) (def : A) :
  uniform def [::] = Ret def :> M A.
Proof. by []. Qed.

Lemma choice_ext (q p : prob) (M : probMonad) A (m1 m2 : M A) :
  p = q :> R -> m1 <| p |> m2 = m1 <| q |> m2.
Proof. by move/val_inj => ->. Qed.

Lemma uniform_cons (M : probMonad) (A : Type) (def : A) h s :
  uniform def (h :: s) =
  Ret h <| (/ IZR (Z_of_nat (size (h :: s))))%:pr |> uniform def s :> M A.
Proof.
by case: s => //=; rewrite (@choice_ext 1%:pr) // ?choice1 //= Rinv_1.
Qed.

Lemma uniform_singl (M : probMonad) (A : Type) (def : A) h : size h = 1%nat ->
  uniform def h = Ret (head def h) :> M A.
Proof.
case: h => // h [|//] _.
by rewrite uniform_cons uniform_nil (@choice_ext 1%:pr) ?choice1 //= invR1.
Qed.

Lemma uniform_nseq (M : probMonad) (A : Type) (def : A) h n :
  uniform def (nseq n.+1 h) = Ret h :> M A.
Proof.
elim: n => // n IH.
by rewrite (_ : nseq _ _ = h :: nseq n.+1 h) // uniform_cons IH choicemm.
Qed.

Lemma uniform_cat (M : probMonad) (A : Type) (a : A) s t :
  let m := size s in let n := size t in
  uniform a (s ++ t) = uniform a s <| (divRnnm m n)%:pr |> uniform a t :> M _.
Proof.
elim: s t => [t m n|s1 s2 IH t m n].
  rewrite cat0s uniform_nil /= [X in _ <| X |> _](_ : _ = 0%:pr) ?choice0 //.
  by apply val_inj; rewrite /= /divRnnm div0R.
case/boolP : (m.-1 + n == 0)%nat => [{IH}|] m1n0.
  have s20 : s2 = [::] by move: m1n0; rewrite {}/m /=; case: s2.
  have t0 : t = [::] by move: m1n0; rewrite {}/n /= addnC; case: t.
  subst s2 t.
  rewrite cats0 (_ : Prob.mk _ = 1%:pr) ?choice1 //.
  by apply val_inj; rewrite /= /divRnnm div1R invR1.
rewrite cat_cons uniform_cons uniform_cons.
set pv := ((/ _)%R).
set v : prob := @Prob.mk pv _.
set u := @Prob.mk (INR (size s2) / INR (size s2 + size t))%R (prob_divRnnm _ _).
rewrite -[RHS](choiceA v u).
  by rewrite IH.
split.
  rewrite 3!probpK -INR_IZR_INZ.
  rewrite (_ : INR _ = INR m) // mulRA mulVR; last by rewrite INR_eq0'.
  by rewrite mul1R /pv -INR_IZR_INZ [size _]/= size_cat -addSn.
rewrite 3!probpK.
transitivity ( (1 - 1 / INR (m + n)) * (1 - INR (m.-1) / INR (m.-1 + n)))%R; last first.
  congr (_ .~ * _)%R.
  by rewrite /v /pv probpK INR_IZR_INZ [size _]/= size_cat -addSn div1R.
transitivity (INR n / INR (m + n))%R.
  rewrite {1}/onem -{1}(Rinv_r (INR (m + n))); last exact/not_0_INR.
  rewrite -mulRBl -minus_INR; last by apply/leP; rewrite leq_addr.
  by rewrite minusE addnC addnK.
rewrite {1}/Rdiv mulRC.
rewrite {1}/Rdiv -[in LHS](mul1R (INR n)).
rewrite -{1}(mulRV (INR (m.-1 + n))); last by rewrite INR_eq0'.
rewrite 2!mulRA -(mulRA (_ * _)%R); congr Rmult.
  rewrite mulRC -subn1.
  rewrite addnC addnBA // minus_INR; last by apply/leP; rewrite addn_gt0 orbT.
  rewrite -/(_ / INR (m + n))%R.
  rewrite Rdiv_minus_distr {1}/Rdiv addnC Rinv_r //; exact/not_0_INR.
rewrite -{1}(Rinv_r (INR (m.-1 + n))); last exact/not_0_INR/eqP.
rewrite -Rdiv_minus_distr mulRC; congr (_ * _)%R.
rewrite -minus_INR; last by apply/leP; rewrite leq_addr.
by rewrite addnC minusE -subnBA // subnn subn0.
Qed.

Lemma uniform2 (M : probMonad) (A : Type) (def : A) a b :
  uniform def [:: a; b] = uniform def [:: b; a] :> M _.
Proof.
rewrite uniform_cons uniform_singl // uniform_cons uniform_singl //.
set pa := Prob.mk _.
rewrite choiceC /= (@choice_ext pa) //=.
rewrite /onem; field.
Qed.

Lemma uniform_inde (M : probMonad) (A : Type) a (x : seq A) {B} (m : M B) :
  uniform a x >> m = m.
Proof.
elim: x m => [/= m|x xs IH m]; first by rewrite bindretf.
by rewrite uniform_cons choice_bindDl IH bindretf choicemm.
Qed.

Lemma uniform_naturality (M : probMonad) (A B : Type) (a : A) (b : B) (f : A -> B) :
  forall x, (0 < size x)%nat ->
  ((@uniform M _ b) \o map f) x = ((M # f) \o uniform a) x.
Proof.
elim=> // x [_ _|x' xs]; first by rewrite [in RHS]compE fmapE bindretf.
move/(_ isT) => IH _.
rewrite compE [in RHS]compE [in LHS]uniform_cons [in RHS]uniform_cons.
set p := (@Prob.mk (/ IZR (Z.of_nat (size _)))%R _ in X in _ = X).
rewrite (_ : @Prob.mk (/ _)%R _ = p); last first.
  by apply val_inj; rewrite /= size_map.
move: IH; rewrite 2!compE => ->.
by rewrite [in RHS]fmapE choice_bindDl bindretf fmapE.
Qed.
Arguments uniform_naturality {M A B}.

Lemma mpair_uniform_base_case (M : probMonad) (A : Type) a x (y : seq A) :
  (0 < size y)%nat ->
  uniform (a, a) (cp [:: x] y) = mpair (uniform a [:: x], uniform a y) :> M _.
Proof.
move=> y0; rewrite cp1.
transitivity (@uniform M _ a y >>= (fun y' => Ret (x, y'))).
  by rewrite -(compE (uniform _)) (uniform_naturality a) // compE fmapE.
transitivity (do z <- Ret x; do y' <- uniform a y; Ret (z, y') : M _)%Do.
  by rewrite bindretf.
by [].
Qed.

Lemma mpair_uniform (M : probMonad) (A : Type) a (x y : seq A) :
  (0 < size x)%nat -> (0 < size y)%nat ->
  mpair (uniform a x, uniform a y) = uniform (a, a) (cp x y) :> M (A * A)%type.
Proof.
elim: x y => // x; case=> [_ y _ size_y|x' xs IH y _ size_y]; apply/esym.
  exact/mpair_uniform_base_case.
set xxs := x' :: xs.
rewrite /cp -cat1s allpairs_cat -/(cp _ _) cp1 uniform_cat.
pose n := size y.
pose l := size (cp xxs y).
rewrite (_ : size _ = n); last by rewrite size_map.
rewrite (_ : Prob.mk _ = probdivRnnm n l); last first.
  by rewrite -/(cp _ _) -/l; exact/val_inj.
pose m := size xxs.
have lmn : (l = m * n)%nat by rewrite /l /m /n size_allpairs.
rewrite (_ : probdivRnnm _ _ = @Prob.mk (/ (1 + m)%:R) (prob_invn _))%R; last first.
  apply val_inj => /=.
  rewrite lmn /divRnnm -mulSn mult_INR {1}/Rdiv Rinv_mult_distr; last 2 first.
    by rewrite INR_eq0.
    by rewrite INR_eq0; apply/eqP; rewrite -lt0n.
  rewrite mulRC -mulRA mulVR; last by rewrite INR_eq0' -lt0n.
  by rewrite mulR1 -addn1 addnC.
rewrite -IH //.
rewrite -/xxs.
move: (@mpair_uniform_base_case M _ a x _ size_y).
rewrite {1}/cp [in X in uniform _ X]/= cats0 => ->.
rewrite -choice_bindDl.
rewrite [in RHS]/mpair uniform_cat.
rewrite [in RHS](_ : Prob.mk _ = probinvn m) //.
by apply val_inj; rewrite /= /divRnnm div1R.
Qed.

(* FIXME
Section altprob_semilattconvtype.
Variable M : altProbMonad.
Variable T : Type.

HB.instance Definition _ := isSemiLattConv.Build

Definition altProb_semiLattConvMixin : @mixin_of (altCI_semiLattType M T)
  (fun p (x y : choice_of_Type (M T)) => x <| p |> y).
Proof. by refine (Mixin _); exact: choiceDr. Defined.

Definition altProb_semiLattConvClass := @Class (M T)
  (altCI_semiLattClass M T) (prob_convMixin M T) altProb_semiLattConvMixin.

Canonical altProb_semiLattConvType := Pack altProb_semiLattConvClass.

End altprob_semilattconvtype.
*)

(* TODO(rei): incipit of section 5 of gibbonsUTP2012 on the model of MonadAltProb *)

Section convexity_property.

Variables (M : altProbMonad) (A : Type) (p q : M A).

Lemma convexity w : p [~] q =
  (p <| w |> p) [~] (q <| w |> p) [~] (p <| w |> q) [~] (q <| w |> q).
Proof.
rewrite -[LHS](choicemm (probcplt w)).
rewrite choiceDr.
rewrite -[in RHS]altA altACA.
rewrite -2![in RHS]choiceDr.
by rewrite -2!choiceC.
Qed.

End convexity_property.

Definition bcoin {M : probMonad} (p : prob) : M bool :=
  Ret true <| p |> Ret false.
Arguments bcoin : simpl never.

Section prob_only.
Variable M : probMonad.
Variable p q : prob.

Definition two_coins : M (bool * bool)%type :=
  (do a <- bcoin p; (do b <- bcoin q; Ret (a, b) : M _))%Do.

Definition two_coins' : M (bool * bool)%type :=
  (do a <- bcoin q; (do b <- bcoin p; Ret (b, a) : M _))%Do.

Lemma two_coinsE : two_coins = two_coins'.
Proof.
rewrite /two_coins /two_coins' /bcoin.
rewrite ![in LHS](choice_bindDl,bindretf).
rewrite -choiceACA.
by rewrite ![in RHS](choice_bindDl,bindretf).
Qed.
End prob_only.

Section mixing_choices.

Variable M : altProbMonad.

Definition arbcoin p : M bool :=
  (do a <- arb ; (do c <- bcoin p; Ret (a == c) : M _))%Do.
Definition coinarb p : M bool :=
  (do c <- bcoin p ; (do a <- arb; Ret (a == c) : M _))%Do.

Lemma arbcoin_spec p :
  arbcoin p = (bcoin p : M _) [~] bcoin p.~%:pr.
Proof.
rewrite /arbcoin /arb alt_bindDl 2!bindretf bindmret; congr (_ [~] _).
by rewrite /bcoin choiceC choice_bindDl 2!bindretf eqxx.
Qed.

Section arbcoin_spec_convexity.
Import Rstruct convex necset ScaledConvex.
Local Open Scope latt_scope.
Local Open Scope convex_scope.
Local Open Scope R_scope.

(* TODO? : move magnified_weight to infotheo.convex *)
Lemma magnified_weight_proof (p q r : prob) :
  p < q < r -> 0 <= (r - q) / (r - p) <= 1.
Proof.
case => pq qr.
have rp : 0 < r - p by rewrite subR_gt0; apply (ltR_trans pq).
have rp' : r - p != 0 by apply/gtR_eqF.
have rq : 0 < r - q by rewrite subR_gt0.
split; first by apply divR_ge0 => //; apply ltRW.
rewrite divRE -(leR_pmul2r rp).
by rewrite mulRAC -mulRA mulRV // mulR1 mul1R leR_add2l leR_oppl oppRK; exact/ltRW.
Qed.

Definition magnified_weight (p q r : prob) (H : p < q < r) : prob :=
  Eval hnf in Prob.mk_ (magnified_weight_proof H).

Local Notation m := magnified_weight.
Local Notation "x +' y" := (addpt x y) (at level 50).
Local Notation "a *' x" := (scalept a x) (at level 40).

Lemma magnify_conv (T : convType) (p q r : prob) (x y : T) (H : p < q < r) :
  (x <|p|> y) <|magnified_weight H|> (x <|r|> y) = x <|q|> y.
Proof.
case: (H) => pq qr.
have rp : 0 < r - p by rewrite subR_gt0; apply (ltR_trans pq).
have rp' : r - p != 0 by apply/gtR_eqF.
apply: S1_inj; rewrite ![in LHS]S1_conv !convptE.
rewrite !scalept_addpt !scalept_comp //.
rewrite [in X in X +' (_ +' _)]addptC addptA addptC !addptA -scalept_addR //.
rewrite -!addptA -scalept_addR //.
have-> : (m H).~ * r.~ + m H * p.~ = (m H * p + (m H).~ * r).~ by rewrite /onem; ring.
suff-> : m H * p + (m H).~ * r = q by rewrite S1_conv convptE addptC.
rewrite /m /= /onem.
rewrite mulRDl mul1R addRCA -Rmult_opp_opp -mulRDr (addRC (- p)) addR_opp.
by rewrite mulNR mulRAC -mulRA mulRV // mulR1; ring.
Qed.

Lemma arbcoin_spec_convexity (p q : prob) :
  p < q < p.~%:pr ->
  arbcoin p = (bcoin p : M _) [~] bcoin p.~%:pr [~] bcoin q.
Proof.
move=> H.
rewrite arbcoin_spec !alt_lub.
(*by rewrite {1}(lub_absorbs_conv _ _ (magnified_weight H)) magnify_conv. FIXME
Qed.*) Abort.
End arbcoin_spec_convexity.

Lemma coinarb_spec p : coinarb p = arb.
Proof.
rewrite /coinarb /bcoin.
rewrite choice_bindDl.
rewrite !bindretf.
rewrite /arb !alt_bindDl !bindretf eqxx.
by rewrite eq_sym altC choicemm.
Qed.

Lemma alt_absorbs_choice T (x y : M T) p : x [~] y = x [~] y [~] x <|p|> y.
Proof.
have H: x [~] y = (x [~] y [~] x <|p|> y) [~] y <|p|> x by
      rewrite -[in LHS](choicemm p (x [~] y)) choiceDl 2!choiceDr 2!choicemm altCA altC (altAC x).
rewrite {1}H.
have {2}<-: x [~] y [~] (x [~] y [~] x <|p|> y) = x [~] y [~] x <|p|> y
    by rewrite altA altmm.
rewrite [in RHS]altC.
have <-: x [~] y [~] x <|p|> y [~] (x [~] y [~] x <|p|> y [~] y <|p|> x) =
         (x [~] y [~] x <|p|> y [~] y <|p|> x)
  by rewrite altA altmm.
by rewrite -H.
Qed.

Corollary arb_spec_convexity p : arb = (arb : M _) [~] bcoin p.
Proof. exact: alt_absorbs_choice. Qed.

Lemma coinarb_spec_convexity' p w : coinarb p =
  (Ret false : M _) [~] (Ret true : M _) [~] (bcoin w : M _).
Proof. by rewrite coinarb_spec /arb /bcoin choiceC -(alt_absorbs_choice) altC. Qed.

Lemma coinarb_spec_convexity p w : coinarb p =
  (bcoin w : M _) [~] (Ret false : M _) [~] (Ret true : M _) [~] bcoin w.~%:pr.
Proof.
rewrite coinarb_spec [in LHS]/arb [in LHS](convexity _ _ w) 2!choicemm.
rewrite -/(bcoin w) -altA altCA -!altA; congr (_ [~] _).
rewrite altA altC; congr (_ [~] (_ [~] _)).
by rewrite choiceC.
Qed.

End mixing_choices.

Definition coins23 {M : exceptProbMonad} : M bool :=
  Ret true <| (/ 2)%:pr |> (Ret false <| (/ 2)%:pr |> fail).

(* NB: notation for ltac:(split; fourier?)*)
Lemma choiceA_compute {N : probMonad} (T F : bool) (f : bool -> N bool) :
  f T <|(/ 9)%:pr|> (f F <|(/ 8)%:pr|> (f F <|(/ 7)%:pr|> (f F <|(/ 6)%:pr|>
 (f T <|(/ 5)%:pr|> (f F <|(/ 4)%:pr|> (f F <|(/ 3)%:pr|> (f F <|(/ 2)%:pr|>
  f T))))))) = f F <|(/ 3)%:pr|> (f F <|(/ 2)%:pr|> f T) :> N _.
Proof.
have H27 : (0 <b= 2/7 <b= 1)%R by apply/leR2P; split; lra.
have H721 : (0 <b= 7/21 <b= 1)%R by apply/leR2P; split; lra.
have H2156 : (0 <b= 21/56 <b= 1)%R by apply/leR2P; split; lra.
have H25 : (0 <b= 2/5 <b= 1)%R by apply/leR2P; split; lra.
rewrite [in RHS](choiceA _ _ (/ 2)%:pr (/ 3).~%:pr); last first.
  by rewrite 3!probpK /= /onem; split; field.

rewrite choicemm.
rewrite [in LHS](choiceA (/ 3)%:pr (/ 2)%:pr (/ 2)%:pr (/ 3).~%:pr); last first.
  by rewrite 3!probpK /= /onem; split; field.
rewrite choicemm.
rewrite [in LHS](choiceA (/ 4)%:pr (/ 3).~%:pr (/ 3)%:pr (/ 4).~%:pr); last first.
  by rewrite 4!probpK /= /onem; split; field.
rewrite choicemm.
rewrite [in LHS](choiceA (/ 7)%:pr (/ 6)%:pr (/ 2)%:pr (@Prob.mk (2/7) H27)); last first.
  by rewrite 4!probpK /= /onem; split; field.
rewrite choicemm.
rewrite [in LHS](choiceA (/ 8)%:pr (@Prob.mk (2/7) H27) (@Prob.mk (7/21) H721) (@Prob.mk (21/56) H2156)); last first.
  by rewrite probpK /= /onem; split; field.
rewrite (choiceC (/ 4).~%:pr).
rewrite [in LHS](choiceA (/ 5)%:pr (probcplt (/ 4).~%:pr) (/ 2)%:pr (@Prob.mk (2/5) H25)); last first.
  by rewrite 3!probpK /= /onem; split; field.
rewrite 2!choicemm.
rewrite (choiceC (@Prob.mk (2/5) H25)).
rewrite [in LHS](choiceA (@Prob.mk (21/56) H2156) (probcplt (Prob.mk H25)) (/ 2)%:pr (/ 4).~%:pr); last first.
  by rewrite 3!probpK /= /onem; split; field.
rewrite choicemm.
rewrite (choiceC (/ 4).~%:pr).
rewrite [in LHS](choiceA (/ 9)%:pr (probcplt (/ 4).~%:pr) (/ 3)%:pr (/ 3)%:pr); last first.
  by rewrite 3!probpK /= /onem; split; field.
by rewrite choicemm choiceC.
Qed.

Definition uFFT {M : probMonad} : M bool :=
  uniform true [:: false; false; true].

Lemma uFFTE (M : probMonad) : uFFT = bcoin (/ 3)%:pr :> M _.
Proof.
rewrite /uFFT /bcoin uniform_cons.
rewrite (_ : _%:pr = (/ 3)%:pr)%R; last exact/val_inj.
rewrite uniform_cons.
rewrite [in X in _ <| _ |> X](_ : _%:pr = (/ 2)%:pr)%R; last exact/val_inj.
rewrite uniform_singl //=.
rewrite (choiceA _ _ (/ 2)%:pr (/ 3).~%:pr); last first.
  by rewrite /= /onem; split; field.
rewrite choicemm choiceC; congr (Ret true <| _ |> Ret false).
by apply val_inj; rewrite /= onemK.
Qed.

Definition uTTF {M : probMonad} : M bool :=
  uniform true [:: true; true; false].

Lemma uTTFE (M : probMonad) : uTTF = bcoin (/ 3).~%:pr :> M _.
Proof.
rewrite /uTTF /bcoin uniform_cons.
rewrite (_ : _%:pr = (/ 3)%:pr)%R; last exact/val_inj.
rewrite uniform_cons.
rewrite [in X in _ <| _ |> X](_ : _%:pr = (/ 2)%:pr)%R; last exact/val_inj.
rewrite uniform_singl //=.
rewrite (choiceA _ _ (/ 2)%:pr (/ 3).~%:pr) ?choicemm //.
by rewrite /= /onem; split; field.
Qed.

Lemma uniform_notin (M : probMonad) (A : eqType) (def : A) (s : seq A) B
  (ma mb : A -> M B) (p : pred A) :
  s != [::] ->
  (forall x, x \in s -> ~~ p x) ->
  uniform def s >>= (fun t => if p t then ma t else mb t) =
  uniform def s >>= mb.
Proof.
elim: s => [//|h t IH _ H].
rewrite uniform_cons.
case/boolP : (t == [::]) => [/eqP -> {IH}|t0].
  rewrite uniform_nil.
  rewrite (_ : _%:pr = 1%:pr); last by apply val_inj; rewrite /= Rinv_1.
  rewrite choice1.
  rewrite 2!bindretf ifF //; apply/negbTE/H; by rewrite mem_head.
rewrite 2!choice_bindDl; congr (_ <| _ |> _).
  rewrite 2!bindretf ifF //; apply/negbTE/H; by rewrite mem_head.
by rewrite IH // => a ta; rewrite H // in_cons ta orbT.
Qed.

Lemma choice_halfC A (M : probMonad) (a b : M A) :
  a <| (/ 2)%:pr |> b = b <| (/ 2)%:pr |> a.
Proof.
rewrite choiceC (_ : (_.~)%:pr = (/ 2)%:pr) //.
by apply val_inj; rewrite /= /onem; lra.
Qed.

(*Lemma choice_halfACA A (M : probMonad) (a b c d : M A) :
  (a <| (/ 2)%:pr |> b) <| (/ 2)%:pr |> (c <| (/ 2)%:pr |> d) =
  (a <| (/ 2)%:pr |> c) <| (/ 2)%:pr |> (b <| (/ 2)%:pr |> d).
Proof. exact: (@convex.convACA probConvex). Qed.*)

Section keimel_plotkin_instance.
Variables (M : altProbMonad) (A : Type).
Variables (p q : M A).

Lemma keimel_plotkin_instance :
  (forall T p, right_distributive (fun a b : M T => a [~] b) (fun a b => a <| p |> b)) ->
  p <| (/ 2)%:pr |> q = (p <| (/ 2)%:pr |> q) <| (/ 2)%:pr |> (p [~] q).
Proof.
move=> altDr.
have altDl : forall T p, left_distributive (fun a b : M T => a [~] b) (fun a b => a <| p |> b).
  by move=> T r a b c; rewrite altC altDr (altC a) (altC b).
rewrite -[LHS](altmm (p <| (/ 2)%:pr |> q)).
transitivity (
  ((p [~] p) <| (/ 2)%:pr|> (q [~] p)) <| (/ 2)%:pr |> ((p [~] q) <| (/ 2)%:pr |> (q [~] q))
).
  by rewrite altDr altDl altDl.
rewrite 2!altmm (altC q).
rewrite (choice_halfC (p [~] q)).
rewrite choiceACA.
by rewrite choicemm.
Qed.

End keimel_plotkin_instance.
