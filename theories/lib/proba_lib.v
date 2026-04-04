(* monae: Monadic equational reasoning in Rocq                                *)
(* Copyright (C) 2025 monae authors, license: LGPL-2.1-or-later               *)
From infotheo Require realType_ext.  (* Remove this line when requiring Rocq >= 9.2 *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum lra ring.
From mathcomp Require Import interval_inference.
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
Variable M : convexMonad R.
Variable A : Type.
Local Open Scope proba_scope.
Local Open Scope ring_scope.
Local Open Scope proba_monad_scope.

Lemma choice_conv p (x y : M A) : x <|p|> y = conv p x y.
Proof. by []. Qed.

Lemma choiceACA q p :
  @interchange (M A) (fun a b => a <|p|> b) (fun a b => a <|q|> b).
Proof. by move=> *; exact: convACA. Qed.

Lemma magnify_choice (p q r : {prob R}) (x y : M A) (pr : p%:num < r%:num)
  (pqr : p%:num <= q%:num <= r%:num) :
(x <|p|> y) <|magnified_prob pr pqr|> (x <|r|> y) = x <|q|> y.
Proof. exact: magnify_conv. Qed.

End convex.

Section uniform.
Variable R : realType.
Local Open Scope ring_scope.

(* NB: the parameter def is because Rocq functions are total *)
Fixpoint uniform {M : probMonad R} {A : Type} (def : A) (s : seq A) : M A :=
  match s with
    | [::] => Ret def
    | [:: x] => Ret x
    | x :: xs => Ret x <| probinvn (size xs) |> uniform def xs
  end.
(* FIXTHEM:
   `probinvn (size xs)` was `(size (x :: xs))%:R^-1%:pr`.
   The latter worked before infotheo 0.9.7, and now it fails even if we change %:pr to %:i01.
   As of 0.9.7, {prob R} is an alias to {i01 R}, and
   the canonical declaration for probinvn in realType_ext is silently failing due to the
   alrealy existent instance for GRing.inv (Instance.inv_inum in interval_inference).
   Instance.inv_inum is not clever enough to derive that "1/(1+n) <= 1".
   We will need to augment inv_inum to recover the original code
   (`(size (x :: xs))%:R^-1%:i01).
 *)

Lemma uniform_nil (M : probMonad R) (A : Type) (def : A) :
  uniform def [::] = Ret def :> M A.
Proof. by []. Qed.

Lemma choice_ext (q p : {prob R}) (M : probMonad R) A (m1 m2 : M A) :
  p%:num = q%:num :> R -> m1 <| p |> m2 = m1 <| q |> m2.
Proof. by move/val_inj => ->. Qed.

Lemma uniform_cons (M : probMonad R) (A : Type) (def : A) h s :
  uniform def (h :: s) =
  Ret h <| probinvn (size s) |> uniform def s :> M A.
Proof.
by case: s => //=; rewrite (@choice_ext 1%:i01) // ?choice1 //= invr1.
Qed.
(* TODO (fix inference):  probinvn (size s) was (size s).+1%:R^-1%:pr *)

Lemma uniform_singl (M : probMonad R) (A : Type) (def : A) h : size h = 1%nat ->
  uniform def h = Ret (head def h) :> M A.
Proof.
case: h => // h [|//] _.
by rewrite uniform_cons uniform_nil (@choice_ext 1%:i01) ?choice1 //= invr1.
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
  rewrite cat0s uniform_nil /= [X in _ <| X |> _](_ : _ = 0%:i01) ?choice0 //.
  by apply val_inj; rewrite /= /divrnnm mul0r.
case/boolP : (m.-1 + n == 0)%nat => [{IH}|] m1n0.
  have s20 : s2 = [::] by move: m1n0; rewrite {}/m /=; case: s2.
  have t0 : t = [::] by move: m1n0; rewrite {}/n /= addnC; case: t.
  subst s2 t.
  rewrite cats0 (_ : Prob.mk _ = 1%:i01) ?choice1 //.
  by apply val_inj; rewrite /= /divrnnm mul1r invr1.
rewrite cat_cons.
rewrite uniform_cons.
rewrite uniform_cons.
set v : {prob R} := probinvn _.
(*set u := @Prob.mk _ ((size s2)%:R / (size s2 + size t)%:R) (prob_divrnnm_subproof R _ _).*)
set u : {prob R} := (divrnnm R (size s2) (size t))%:pr.
rewrite -[RHS](@choiceA_alternative _ _ _ v u).
  by rewrite IH.
split.
  rewrite mulrA mulVf//=.
  by rewrite mul1r add1n /m /= addSn size_cat.
transitivity ( (1 - 1 / (m + n)%:R) * (1 - m.-1%:R / (m.-1 + n)%:R : R)); last first.
  by congr (_ .~ * _); rewrite /v mul1r size_cat.
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
set pa := probinvn _.
rewrite choiceC /= (@choice_ext pa) //=.
by rewrite /onem/= !natrD natr1; lra.
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
rewrite (_ : probinvn _ = p); last first.
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

Local Open Scope ring_scope.

HB.instance Definition _ := @isSemiLattice.Build ((M : convexMonad _) T)
  (fun x y => x [~] y)
  (@altC M T) (@altA M T) (@altmm M T).

Let axiom (p : {prob R}) (x y z : M T) :
  x <| p |> (y [~] z) = (x <| p |> y) [~] (x <| p |> z).
Proof. by rewrite choiceDr. Qed.

HB.instance Definition _ :=
  @isSemiLattConv.Build R((M : convexMonad _) T) axiom.

End altprob_semilattconvtype.

(* TODO(rei): incipit of section 5 of gibbonsUTP2012 on the model of MonadAltProb *)

Section convexity_property.
Variables (R : realType) (M : altProbMonad R) (A : Type) (p q : M A).
Local Open Scope ring_scope.

Lemma convexity w : p [~] q =
  (p <| w |> p) [~] (q <| w |> p) [~] (p <| w |> q) [~] (q <| w |> q).
Proof.
rewrite -[LHS](choicemm w%:num.~%:i01).
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
  arbcoin p = (bcoin p : M _) [~] bcoin p%:num.~%:i01.
Proof.
rewrite /arbcoin /arb alt_bindDl 2!bindretf bindmret; congr (_ [~] _).
by rewrite /bcoin choiceC choice_bindDl 2!bindretf eqxx/=.
Qed.

Lemma alt_absorbs_choice T (p : {prob R}) (x y : M T) :
  x [~] y = (x [~] y) [~] (x <|p|> y).
Proof. exact: (@lub_absorbs_conv _ ((M : convexMonad _) T)). Qed.

Lemma arbcoin_spec_convexity (p q : {prob R}) :
  p%:num < q%:num < p%:num.~ ->
  arbcoin p = bcoin p [~] bcoin p%:num.~%:i01 [~] bcoin q :> M bool.
Proof.
case/andP => pq q1p.
have p1p := lt_trans pq q1p.
have pq1p : p%:num <= q%:num <= p%:num.~ by apply/andP; split; apply/ltW.
rewrite arbcoin_spec [LHS](alt_absorbs_choice (magnified_prob p1p pq1p)).
congr alt; rewrite /bcoin -[RHS](magnify_choice _ _  p1p pq1p).
congr choice; congr (choice _ bool).
exact/val_inj.
Qed.

Lemma coinarb_spec p : coinarb p = arb.
Proof.
rewrite /coinarb /bcoin.
rewrite choice_bindDl.
rewrite !bindretf.
rewrite /arb !alt_bindDl !bindretf eqxx.
by rewrite eq_sym altC choicemm.
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
rewrite choiceC; congr (choice _ bool).
exact/val_inj.
Qed.

End mixing_choices.

Local Open Scope ring_scope.

(* FIXME! (kludge) *)
Notation "x '^-1%:i01'" := (Itv01 (andP (prob_invn x.-1)).1 (andP (prob_invn x.-1)).2).

(* not used anywhere? *)
Definition coins23 {R : realType} {M : exceptProbMonad R} : M bool :=
  Ret true <| 2^-1%:i01 |> (Ret false <| 2^-1%:i01 |> fail).

(* TODO: check if we PRed this notation to mathcomp *)
Reserved Notation "x <= y <= z :> T" (at level 70, y, z at next level).
Notation "x <= y <= z :> T" := ((x <= y :> T)%R && (y <= z :> T)%R).

Section for_example_monty.

(* NB: notation for ltac:(split; fourier?)*)
Lemma choiceA_compute {R : realType} {N : probMonad R} (T F : bool) (f : bool -> N bool) :
  f T <|9^-1%:i01|> (f F <|8^-1%:i01|> (f F <|7^-1%:i01|> (f F <|6^-1%:i01|>
 (f T <|5^-1%:i01|> (f F <|4^-1%:i01|> (f F <|3^-1%:i01|> (f F <|2^-1%:i01|>
  f T))))))) = f F <|3^-1%:i01|> (f F <|2^-1%:i01|> f T) :> N _.
Proof.
have H27 : 0 <= 2/7 <= 1 :> R by lra.
have H721 : 0 <= 7/21 <= 1 :> R by lra.
have H2156 : 0 <= 21/56 <= 1 :> R by lra.
have H25 : 0 <= 2/5 <= 1 :> R by lra.
pose choiceA_alt := @choiceA_alternative R N bool.
Locate "%:i01".
rewrite [in RHS](choiceA_alt _ _ 2^-1%:i01 (3^-1%:i01)%:num.~%:i01); last first.
  by rewrite /= /onem; split; field.
rewrite choicemm.
rewrite [in LHS](choiceA_alt 3^-1%:i01 2^-1%:i01 2^-1%:i01 (3^-1%:i01)%:num.~%:i01); last first.
  by rewrite /= /onem; split; field.
rewrite choicemm.
rewrite [in LHS](choiceA_alt 4^-1%:i01 (3^-1%:i01)%:num.~%:i01 3^-1%:i01 (4^-1%:i01)%:num.~%:i01); last first.
  by rewrite /= /onem; split; field.
rewrite choicemm.
rewrite [in LHS](choiceA_alt 7^-1%:i01 6^-1%:i01 2^-1%:i01 (Prob.mk H27)); last first.
  by rewrite /= /onem; split; field.
rewrite choicemm.
rewrite [in LHS](choiceA_alt 8^-1%:i01 (Prob.mk H27) (Prob.mk H721) (Prob.mk H2156)); last first.
  by rewrite /= /onem; split; field.
rewrite (choiceC (4^-1%:i01)%:num.~%:i01).
rewrite [X in _ <| _ |> (_ <| _ |> X)](choiceA_alt _ _ 2^-1%:i01 (Prob.mk H25)); last first.
  by rewrite /= /onem; split; field.
rewrite 2!choicemm.
rewrite (choiceC (Prob.mk H25)).
rewrite [in X in _ <| _ |> X](choiceA_alt _ _ 2^-1%:i01 (4^-1%:i01)%:num.~%:i01); last first.
  by rewrite /= /onem/=; split; field.
rewrite choicemm.
rewrite (choiceC (4^-1%:i01)%:num.~%:i01).
rewrite [in LHS](choiceA_alt _ _ 3^-1%:i01 3^-1%:i01); last first.
  by rewrite /= /onem; split; field.
by rewrite choicemm choiceC.
Qed.

Definition uFFT {R : realType} {M : probMonad R} : M bool :=
  uniform true [:: false; false; true].

Lemma uFFTE {R : realType} (M : probMonad R) : uFFT = bcoin 3^-1%:i01 :> M _.
Proof.
rewrite /uFFT /bcoin uniform_cons.
rewrite uniform_cons.
rewrite uniform_singl //=.
rewrite (@choiceA_alternative _ _ _ _ _ 2^-1%:i01 (3^-1%:i01)%:num.~%:pr); last first.
  by rewrite /= /onem; split; field.
rewrite choicemm choiceC; congr (Ret true <| _ |> Ret false).
by apply val_inj; rewrite /= onemK.
Qed.

Definition uTTF {R : realType} {M : probMonad R} : M bool :=
  uniform true [:: true; true; false].

Lemma uTTFE {R : realType} (M : probMonad R) : uTTF = bcoin (3^-1%:i01)%:num.~%:i01 :> M _.
Proof.
rewrite /uTTF /bcoin uniform_cons.
rewrite uniform_cons.
rewrite uniform_singl //=.
rewrite (@choiceA_alternative _ _ _ _ _ 2^-1%:i01 (3^-1%:i01)%:num.~%:i01) ?choicemm //.
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
  rewrite [X in _ <| X |> _](_ : _ = 1%:i01); last first.
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
  a <| 2^-1%:i01 |> b = b <| 2^-1%:i01 |> a.
Proof.
rewrite choiceC/= [X in _ <| X |> _](_ : _ = 2^-1%:i01) //.
apply: val_inj; rewrite /= /onem.
by field.
Qed.

Lemma choice_halfACA {R : realType} (M : probMonad R) A (a b c d : M A) :
  (a <| 2^-1%:i01 |> b) <| 2^-1%:i01 |> (c <| 2^-1%:i01 |> d) =
  (a <| 2^-1%:i01 |> c) <| 2^-1%:i01 |> (b <| 2^-1%:i01 |> d).
Proof.
rewrite choice_conv.
rewrite -convex.convACA.
by rewrite -choice_conv.
Qed.

End choice_half.

Section keimel_plotkin_instance.
Variables (R : realType) (M : altProbMonad R) (A : Type).
Variables (p q : M A).

(* TODO: merge https://github.com/affeldt-aist/monae/pull/55 to generalize this *)
Lemma keimel_plotkin_instance :
  (forall T p, right_distributive (fun a b : M T => a [~] b) (fun a b => a <| p |> b)) ->
  p <| 2^-1%:i01 |> q = (p <| 2^-1%:i01 |> q) <| 2^-1%:i01 |> (p [~] q).
Proof.
move=> altDr.
have altDl T r : left_distributive (fun a b : M T => a [~] b) (fun a b => a <| r |> b).
  by move=> a b c; rewrite altC altDr (altC a) (altC b).
rewrite -[LHS](altmm (p <| 2^-1%:i01 |> q)).
transitivity (((p [~] p) <| 2^-1%:i01|> (q [~] p)) <| 2^-1%:i01 |> ((p [~] q) <| 2^-1%:i01 |> (q [~] q))).
  by rewrite altDr altDl altDl.
rewrite 2!altmm (altC q).
rewrite (choice_halfC (p [~] q)).
rewrite choiceACA.
by rewrite choicemm.
Qed.

End keimel_plotkin_instance.
