(* monae: Monadic equational reasoning in Rocq                                *)
(* Copyright (C) 2025 monae authors, license: LGPL-2.1-or-later               *)
From infotheo Require realType_ext.  (* Remove this line when requiring Rocq >= 9.2 *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum lra ring.
From mathcomp Require boolp.
From mathcomp Require Import reals unstable mathcomp_extra.
From infotheo Require Import realType_ext.
From infotheo Require Import proba convex necset.
From infotheo Require Import fdist.
Require Import preamble hierarchy monad_lib alt_lib fail_lib.

(**md**************************************************************************)
(* # Definitions and lemmas for probability monads                            *)
(*                                                                            *)
(* ```                                                                        *)
(* uniform s == uniform choice from a sequence s with a probMonad             *)
(* mpair_uniform ==                                                           *)
(*   uniform choices are independent, in the sense that choosing              *)
(*   consecutively from two uniform distributions is equivalent to choosing   *)
(*   simultaneously from their cartesian product                              *)
(* bcoin p == a biased coin with probability p                                *)
(* Sample programs:                                                           *)
(*   arbcoin == arbitrary choice followed by probabilistic choice             *)
(*   coinarb == probabilistic choice followed by arbitrary choice             *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Declare Scope proba_monad_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.
Local Open Scope reals_ext_scope.
Local Open Scope proba_monad_scope.

Import GRing.Theory Num.Theory Order.Theory.

Section convex.
Variable R : realType.
Variable M : probMonad R.
Variable A : Type.
Local Open Scope proba_scope.

Definition choiceA_real_realType (p q : {prob R}) (a b c : M A) :
  let conv := (fun p (a b : M A) => choice p A a b) in
  conv p a (conv q b c) = conv [s_of p, q] (conv [r_of p, q] a b) c.
Proof. exact: (choiceA p q). Qed.

Definition prob_convType := M A.

HB.instance Definition _ := boolp.gen_eqMixin prob_convType.

HB.instance Definition _ := boolp.gen_choiceMixin prob_convType.

HB.instance Definition _ := @infotheo.probability.convex.isConvexSpace.Build R
  prob_convType
  (fun p => choice p A)
  (choice1 _)
  choicemm
  choiceC
  choiceA_real_realType.

Lemma choice_conv p (x y : prob_convType) : x <|p|> y = conv p x y.
Proof. by []. Qed.

End convex.

Lemma choiceACA {R : realType} {M : probMonad R} T q p :
  @interchange (prob_convType M T) (fun a b => a <|p|> b) (fun a b => a <|q|> b).
Proof. by move=> *; exact: convACA. Qed.

Section uniform.
Variable R : realType.
Local Open Scope ring_scope.

(* NB: the parameter def is because Rocq functions are total *)
Fixpoint uniform {M : probMonad R} {A : Type} (def : A) (s : seq A) : M A :=
  match s with
    | [::] => Ret def
    | [:: x] => Ret x
    | x :: xs => Ret x <| (((size (x :: xs))%:R)^-1)%:pr |> uniform def xs
  end.

Lemma uniform_nil (M : probMonad R) (A : Type) (def : A) :
  uniform def [::] = Ret def :> M A.
Proof. by []. Qed.

Lemma choice_ext (q p : {prob R}) (M : probMonad R) A (m1 m2 : M A) :
  Prob.p p = Prob.p q :> R -> m1 <| p |> m2 = m1 <| q |> m2.
Proof. by move/val_inj => ->. Qed.

Lemma uniform_cons (M : probMonad R) (A : Type) (def : A) h s :
  uniform def (h :: s) =
  Ret h <| ((((size s).+1)%:R)^-1)%:pr |> uniform def s :> M A.
Proof.
by case: s => //=; rewrite (@choice_ext 1%:pr) // ?choice1 //= invr1.
Qed.

Lemma uniform_singl (M : probMonad R) (A : Type) (def : A) h : size h = 1%nat ->
  uniform def h = Ret (head def h) :> M A.
Proof.
case: h => // h [|//] _.
by rewrite uniform_cons uniform_nil (@choice_ext 1%:pr) ?choice1 //= invr1.
Qed.

Lemma uniform_nseq (M : probMonad R) (A : Type) (def : A) h n :
  uniform def (nseq n.+1 h) = Ret h :> M A.
Proof.
elim: n => // n IH.
by rewrite (_ : nseq _ _ = h :: nseq n.+1 h) // uniform_cons IH choicemm.
Qed.

Lemma uniform_cat (M : probMonad R) (A : Type) (a : A) s t :
  let m := size s in let n := size t in
  uniform a (s ++ t) = uniform a s <| (divrnnm R m n)%:pr |> uniform a t :> M _.
Proof.
elim: s t => [t m n|s1 s2 IH t m n].
  rewrite cat0s uniform_nil /= [X in _ <| X |> _](_ : _ = 0%:pr) ?choice0 //.
  by apply val_inj; rewrite /= /divrnnm mul0r.
case/boolP : (m.-1 + n == 0)%nat => [{IH}|] m1n0.
  have s20 : s2 = [::] by move: m1n0; rewrite {}/m /=; case: s2.
  have t0 : t = [::] by move: m1n0; rewrite {}/n /= addnC; case: t.
  subst s2 t.
  rewrite cats0 (_ : Prob.mk _ = 1%:pr) ?choice1 //.
  by apply val_inj; rewrite /= /divrnnm mul1r invr1.
rewrite cat_cons.
rewrite uniform_cons.
rewrite uniform_cons.
set pv := _^-1.
set v : {prob R} := @Prob.mk _ pv _.
set u := @Prob.mk_ _ ((size s2)%:R / (size s2 + size t)%:R) (prob_divrnnm_subproof R _ _).
rewrite -[RHS](@choiceA_alternative _ _ _ v u).
  by rewrite IH.
split.
  rewrite 2!probpK.
  rewrite mulrA mulVf//; last by rewrite (eqr_nat _ _ 0).
  by rewrite mul1r /m /= addSn -size_cat.
rewrite 3!probpK.
transitivity ( (1 - 1 / (m + n)%:R) * (1 - m.-1%:R / (m.-1 + n)%:R : R)); last first.
  by congr (_ .~ * _); rewrite /v /pv/= mul1r size_cat.
rewrite /onem.
have mn0: (m + n)%:R != 0 :> R by rewrite (eqr_nat _ _ 0).
rewrite -[X in X - _](divff mn0).
rewrite -[X in (X - _) * _](divff mn0).
rewrite -!mulrBl natrD addrAC subrr add0r.
rewrite addrAC -(@natrB _ _ 1)// subn1 -!natrD.
have mn1: (m.-1 + n)%:R != 0 :> R by rewrite (eqr_nat _ _ 0).
rewrite -[X in _ * (X - _)](divff mn1).
rewrite -mulrBl !natrD addrAC subrr add0r.
rewrite -!natrD [in RHS](mulrC n%:R).
by rewrite mulrACA divff// mul1r mulrC.
Qed.

Lemma uniform2 (M : probMonad R) (A : Type) (def : A) a b :
  uniform def [:: a; b] = uniform def [:: b; a] :> M _.
Proof.
rewrite uniform_cons uniform_singl // uniform_cons uniform_singl //.
set pa := Prob.mk _.
rewrite choiceC /= (@choice_ext pa) //=.
by rewrite /onem; lra.
Qed.

Lemma uniform_inde (M : probMonad R) (A : Type) a (x : seq A) {B} (m : M B) :
  uniform a x >> m = m.
Proof.
elim: x m => [/= m|x xs IH m]; first by rewrite bindretf.
by rewrite uniform_cons choice_bindDl IH bindretf choicemm.
Qed.

Lemma uniform_naturality (M : probMonad R) (A B : Type) (a : A) (b : B) (f : A -> B) :
  forall x, (0 < size x)%nat ->
  ((@uniform M _ b) \o map f) x = ((M # f) \o uniform a) x.
Proof.
elim=> // x [_ _|x' xs]; first by rewrite [in RHS]compE fmapE bindretf.
move/(_ isT) => IH _.
rewrite compE [in RHS]compE.
rewrite [x' :: xs]lock [in LHS]uniform_cons -/(map _ _) [in LHS]/= -lock.
rewrite [x' :: xs]lock [in RHS]uniform_cons -/(map _ _) [in RHS]/= -lock.
set p := (X in _ <| X |> _ = _).
rewrite (_ : @Prob.mk _ (_^-1) _ = p); last first.
  by apply val_inj; rewrite /= size_map.
move: IH; rewrite 2!compE => ->.
by rewrite [in RHS]fmapE choice_bindDl bindretf fmapE.
Qed.
Arguments uniform_naturality {M A B}.

Lemma mpair_uniform_base_case (M : probMonad R) (A : Type) a x (y : seq A) :
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

Lemma mpair_uniform (M : probMonad R) (A : Type) a (x y : seq A) :
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
rewrite (_ : Prob.mk _ = probdivrnnm _ n l); last first.
  by rewrite -/(cp _ _) -/l; exact/val_inj.
pose m := size xxs.
have lmn : (l = m * n)%nat by rewrite /l /m /n size_allpairs.
rewrite (_ : probdivrnnm _ _ _ = @Prob.mk _ ((1 + m)%:R)^-1 (prob_invn _)); last first.
  apply val_inj => /=.
  rewrite lmn /divrnnm -mulSn natrM invfM mulrCA divff ?mulr1 ?add1n//.
  by rewrite (eqr_nat _ _ 0) gt_eqF.
rewrite -IH //.
rewrite -/xxs.
move: (@mpair_uniform_base_case M _ a x _ size_y).
rewrite {1}/cp [in X in uniform _ X]/= cats0 => ->.
rewrite -choice_bindDl.
rewrite [in RHS]/mpair uniform_cat.
congr bind.
congr (choice _ _ (uniform a [:: x]) (uniform a xxs)).
apply: val_inj.
by rewrite /= /divrnnm div1r.
Qed.

End uniform.

Section altprob_semilattconvtype.
Variable R : realType.
Variable M : altProbMonad R.
Variable T : Type.
(*Import convex necset SemiLattice.*)

Local Open Scope ring_scope.

Definition altProb_semiLattConvType := M T.

Let axiom (p : {prob R}) (x y z : altProb_semiLattConvType) :
  x <| p |> (y [~] z) = (x <| p |> y) [~] (x <| p |> z).
Proof. by rewrite choiceDr. Qed.

HB.instance Definition _ := boolp.gen_eqMixin altProb_semiLattConvType.
HB.instance Definition _ := boolp.gen_choiceMixin altProb_semiLattConvType.

HB.instance Definition _ := @isSemiLattice.Build altProb_semiLattConvType
  (fun x y => x [~] y)
  (@altC M T) (@altA M T) (@altmm M T).

HB.instance Definition _ :=
  @probability.convex.isConvexSpace.Build
    R
    altProb_semiLattConvType
    (fun p : {prob R} => choice p T)
    (choice1 _) choicemm choiceC (@choiceA_real_realType _ M T).

HB.instance Definition _ :=
  @isSemiLattConv.Build
    R
    altProb_semiLattConvType
    axiom.

End altprob_semilattconvtype.

(* TODO(rei): incipit of section 5 of gibbonsUTP2012 on the model of MonadAltProb *)

Section convexity_property.
Variables (R : realType) (M : altProbMonad R) (A : Type) (p q : M A).
Local Open Scope ring_scope.

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

Definition bcoin {R : realType} {M : probMonad R} (p : {prob R}) : M bool :=
  Ret true <| p |> Ret false.
Arguments bcoin : simpl never.

Section prob_only.
Variables (R : realType) (M : probMonad R).
Variable p q : {prob R}.

Local Open Scope ring_scope.

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
Variables (R : realType) (M : altProbMonad R).

Local Open Scope ring_scope.

Definition arbcoin p : M bool :=
  (do a <- arb ; (do c <- bcoin p; Ret (a == c) : M _))%Do.
Definition coinarb p : M bool :=
  (do c <- bcoin p ; (do a <- arb; Ret (a == c) : M _))%Do.

Lemma arbcoin_spec p :
  arbcoin p = (bcoin p : M _) [~] bcoin (Prob.p p).~%:pr.
Proof.
rewrite /arbcoin /arb alt_bindDl 2!bindretf bindmret; congr (_ [~] _).
by rewrite /bcoin choiceC choice_bindDl 2!bindretf eqxx.
Qed.

Section arbcoin_spec_convexity.
Local Open Scope latt_scope.
Local Open Scope convex_scope.

(* TODO? : move magnified_weight to infotheo.convex *)
Lemma magnified_weight_proof (p q r : {prob R}) :
  Prob.p p < Prob.p q < Prob.p r -> (0 <= (Prob.p r - Prob.p q) / (Prob.p r - Prob.p p) <= 1)%R.
Proof.
case/andP => pq qr.
have rp : (0 < Prob.p r - Prob.p p)%R by rewrite subr_gt0 (lt_trans pq).
have rp' : (Prob.p r - Prob.p p != 0)%R by rewrite subr_eq0 gt_eqF// -subr_gt0.
have rq : (0 < Prob.p r - Prob.p q)%R by rewrite subr_gt0.
apply/andP; split; first by rewrite divr_ge0// ltW.
by rewrite -(ler_pM2r rp) -mulrA mulVf// mulr1 mul1r lerD2l lerNl opprK ltW.
Qed.

Definition magnified_weight (p q r : {prob R})
    (H : Prob.p p < Prob.p q < Prob.p r) : {prob R} :=
  Eval hnf in Prob.mk_ (magnified_weight_proof H).

Local Notation m := magnified_weight.
Local Notation "x +' y" := (addpt x y) (at level 50).
Local Notation "a *' x" := (scalept a x) (at level 40).

Lemma magnify_conv (T : convType R)
    (p q r : {prob R}) (x y : T) (H : Prob.p p < Prob.p q < Prob.p r) :
  (x <|p|> y) <| magnified_weight H |> (x <|r|> y) = x <|q|> y.
Proof.
case/andP: (H) => pq qr.
have rp : 0 < Prob.p r - Prob.p p by rewrite subr_gt0; apply (lt_trans pq).
have rp' : Prob.p r - Prob.p p != 0 by apply/negbT/gt_eqF.
apply: (S1_inj R); rewrite ![in LHS]affine_conv/= !convptE.
rewrite !scaleptDr !scaleptA // (addptC ((Prob.p (m H) * Prob.p p) *' S1 x)) addptA.
rewrite addptC !addptA -scaleptDl//.
rewrite -!addptA -scaleptDl//.
have -> : ((Prob.p (m H)).~ * (Prob.p r).~ + Prob.p (m H) * (Prob.p p).~ = (Prob.p (m H) * Prob.p p + (Prob.p (m H)).~ * Prob.p r).~).
  rewrite /onem.
  ring.
pose tmp := (Prob.p (m H) * Prob.p p + (Prob.p (m H)).~ * Prob.p r).
rewrite -[X in X.~ *' _ +' _]/tmp.
rewrite -/tmp.
suff -> : tmp = Prob.p q.
  by rewrite affine_conv convptE addptC.
rewrite /tmp /m /= /onem.
by field.
Qed.

Lemma arbcoin_spec_convexity (p q : {prob R}) :
  Prob.p p < Prob.p q < (Prob.p p).~ ->
  arbcoin p = (bcoin p : M _) [~] bcoin (Prob.p p).~%:pr [~] bcoin q.
Proof.
move=> H.
rewrite arbcoin_spec !alt_lub.
rewrite {1}(@lub_absorbs_conv _
  [the semiLattConvType _ of altProb_semiLattConvType M bool](*NB: FIXME*) _ _
  (magnified_weight H)).
by rewrite magnify_conv.
Qed.
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
have H : x [~] y = (x [~] y [~] x <|p|> y) [~] y <|p|> x.
  rewrite -[in LHS](choicemm p (x [~] y)) choiceDl 2!choiceDr 2!choicemm altCA.
  by rewrite altC (altAC x).
rewrite {1}H.
have {2}<- : x [~] y [~] (x [~] y [~] x <|p|> y) = x [~] y [~] x <|p|> y
  by rewrite altA altmm.
rewrite [in RHS]altC.
have <- : x [~] y [~] x <|p|> y [~] (x [~] y [~] x <|p|> y [~] y <|p|> x) =
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
  (bcoin w : M _) [~] (Ret false : M _) [~] (Ret true : M _) [~] bcoin (Prob.p w).~%:pr.
Proof.
rewrite coinarb_spec [in LHS]/arb [in LHS](convexity _ _ w) 2!choicemm.
rewrite -/(bcoin w) -altA altCA -!altA; congr (_ [~] _).
rewrite altA altC; congr (_ [~] (_ [~] _)).
by rewrite choiceC.
Qed.

End mixing_choices.

(* not used anywhere? *)
Definition coins23 {R : realType} {M : exceptProbMonad R} : M bool :=
  Ret true <| 2^-1%:pr |> (Ret false <| 2^-1%:pr |> fail).

(* TODO: check if we PRed this notation to mathcomp *)
Reserved Notation "x <= y <= z :> T" (at level 70, y, z at next level).
Notation "x <= y <= z :> T" := ((x <= y :> T)%R && (y <= z :> T)%R).

Section for_example_monty.

(* NB: notation for ltac:(split; fourier?)*)
Lemma choiceA_compute {R : realType} {N : probMonad R} (T F : bool) (f : bool -> N bool) :
  f T <|9^-1%:pr|> (f F <|8^-1%:pr|> (f F <|7^-1%:pr|> (f F <|6^-1%:pr|>
 (f T <|5^-1%:pr|> (f F <|4^-1%:pr|> (f F <|3^-1%:pr|> (f F <|2^-1%:pr|>
  f T))))))) = f F <|3^-1%:pr|> (f F <|2^-1%:pr|> f T) :> N _.
Proof.
have H27 : 0 <= 2/7 <= 1 :> R by lra.
have H721 : 0 <= 7/21 <= 1 :> R by lra.
have H2156 : 0 <= 21/56 <= 1 :> R by lra.
have H25 : 0 <= 2/5 <= 1 :> R by lra.
pose choiceA_alt := @choiceA_alternative R N bool.
rewrite [in RHS](choiceA_alt _ _ 2^-1%:pr (3^-1).~%:pr); last first.
  by rewrite 3!probpK /= /onem; split; field.
rewrite choicemm.
rewrite [in LHS](choiceA_alt 3^-1%:pr 2^-1%:pr 2^-1%:pr (3^-1).~%:pr); last first.
  by rewrite 3!probpK /= /onem; split; field.
rewrite choicemm.
rewrite [in LHS](choiceA_alt 4^-1%:pr (3^-1).~%:pr 3^-1%:pr (4^-1).~%:pr); last first.
  by rewrite 4!probpK /= /onem; split; field.
rewrite choicemm.
rewrite [in LHS](choiceA_alt 7^-1%:pr 6^-1%:pr 2^-1%:pr (Prob.mk H27)); last first.
  by rewrite 4!probpK /= /onem; split; field.
rewrite choicemm.
rewrite [in LHS](choiceA_alt 8^-1%:pr (Prob.mk H27) (Prob.mk H721) (Prob.mk H2156)); last first.
  by rewrite probpK /= /onem; split; field.
rewrite (choiceC (4^-1).~%:pr).
rewrite [in LHS](choiceA_alt 5^-1%:pr (probcplt (4^-1).~%:pr) 2^-1%:pr (Prob.mk H25)); last first.
  by rewrite 3!probpK /= /onem; split; field.
rewrite 2!choicemm.
rewrite (choiceC (Prob.mk H25)).
rewrite [in LHS](choiceA_alt (Prob.mk H2156) (probcplt (Prob.mk H25)) 2^-1%:pr (4^-1).~%:pr); last first.
  by rewrite 3!probpK /= /onem; split; field.
rewrite choicemm.
rewrite (choiceC (4^-1).~%:pr).
rewrite [in LHS](choiceA_alt 9^-1%:pr (probcplt (4^-1).~%:pr) 3^-1%:pr 3^-1%:pr); last first.
  by rewrite 3!probpK /= /onem; split; field.
by rewrite choicemm choiceC.
Qed.

Definition uFFT {R : realType} {M : probMonad R} : M bool :=
  uniform true [:: false; false; true].

Lemma uFFTE {R : realType} (M : probMonad R) : uFFT = bcoin 3^-1%:pr :> M _.
Proof.
rewrite /uFFT /bcoin uniform_cons.
rewrite (_ : _%:pr = 3^-1%:pr)%R; last exact/val_inj.
rewrite uniform_cons.
rewrite [in X in _ <| _ |> X](_ : _%:pr = 2^-1%:pr)%R; last exact/val_inj.
rewrite uniform_singl //=.
rewrite (@choiceA_alternative _ _ _ _ _ 2^-1%:pr (3^-1).~%:pr); last first.
  by rewrite /= /onem; split; field.
rewrite choicemm choiceC; congr (Ret true <| _ |> Ret false).
by apply val_inj; rewrite /= onemK.
Qed.

Definition uTTF {R : realType} {M : probMonad R} : M bool :=
  uniform true [:: true; true; false].

Lemma uTTFE {R : realType} (M : probMonad R) : uTTF = bcoin (3^-1).~%:pr :> M _.
Proof.
rewrite /uTTF /bcoin uniform_cons.
rewrite (_ : _%:pr = 3^-1%:pr)%R; last exact/val_inj.
rewrite uniform_cons.
rewrite [in X in _ <| _ |> X](_ : _%:pr = 2^-1%:pr)%R; last exact/val_inj.
rewrite uniform_singl //=.
rewrite (@choiceA_alternative _ _ _ _ _ 2^-1%:pr (3^-1).~%:pr) ?choicemm //.
by rewrite /= /onem; split; field.
Qed.

Lemma uniform_notin {R : realType} (M : probMonad R) (A : eqType) (def : A) (s : seq A) B
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
  rewrite (_ : _%:pr = 1%:pr); last first.
    by apply: val_inj; rewrite /= addn0 invr1.
  rewrite choice1.
  rewrite 2!bindretf ifF //; apply/negbTE/H; by rewrite mem_head.
rewrite 2!choice_bindDl; congr (_ <| _ |> _).
  rewrite 2!bindretf ifF //; apply/negbTE/H; by rewrite mem_head.
by rewrite IH // => a ta; rewrite H // in_cons ta orbT.
Qed.

End for_example_monty.

Section choice_half.

Lemma choice_halfC {R : realType} (M : probMonad R) A (a b : M A) :
  a <| 2^-1%:pr |> b = b <| 2^-1%:pr |> a.
Proof.
rewrite choiceC (_ : (_.~)%:pr = 2^-1%:pr) //.
apply: val_inj; rewrite /= /onem.
lra.
Qed.

Lemma choice_halfACA {R : realType} (M : probMonad R) A (a b c d : M A) :
  (a <| 2^-1%:pr |> b) <| 2^-1%:pr |> (c <| 2^-1%:pr |> d) =
  (a <| 2^-1%:pr |> c) <| 2^-1%:pr |> (b <| 2^-1%:pr |> d).
Proof.
rewrite choice_conv.
rewrite -convex.convACA.
by rewrite -choice_conv.
Qed.

End choice_half.

Section keimel_plotkin_instance.
Variables (R : realType) (M : altProbMonad R) (A : Type).
Variables (p q : M A).

Lemma keimel_plotkin_instance :
  (forall T p, right_distributive (fun a b : M T => a [~] b) (fun a b => a <| p |> b)) ->
  p <| 2^-1%:pr |> q = (p <| 2^-1%:pr |> q) <| 2^-1%:pr |> (p [~] q).
Proof.
move=> altDr.
have altDl T r : left_distributive (fun a b : M T => a [~] b) (fun a b => a <| r |> b).
  by move=> a b c; rewrite altC altDr (altC a) (altC b).
rewrite -[LHS](altmm (p <| 2^-1%:pr |> q)).
transitivity (((p [~] p) <| 2^-1%:pr|> (q [~] p)) <| 2^-1%:pr |> ((p [~] q) <| 2^-1%:pr |> (q [~] q))).
  by rewrite altDr altDl altDl.
rewrite 2!altmm (altC q).
rewrite (choice_halfC (p [~] q)).
rewrite choiceACA.
by rewrite choicemm.
Qed.

End keimel_plotkin_instance.
