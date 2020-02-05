Require Import Reals Lra.
From mathcomp Require Import all_ssreflect.
From mathcomp Require boolp.
From infotheo Require Import ssrR Reals_ext proba.
From infotheo Require convex_choice.
Require Import monae_lib monad fail_monad.

(*
Contents:
- Definition of probabilities
- Module MonadProb.
    probabilistic choice
    example of the function that perfoms a uniform choice
- Module MonadProbDr.
    probabilistic choice + bind right-distributes other choice
- Module MonadAltProb.
    Module MonadAltProb + non-deterministic choice
- Section mixing_choices.
    example illustrating the combined use of probabilistic and non-deterministic choice
- Module MonadExceptProb.
    probabilistic choice + exception
*)

Reserved Notation "mx <| p |> my" (format "mx  <| p |>  my", at level 50).

Declare Scope proba_monad_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.
Local Open Scope reals_ext_scope.

Module MonadProb.
Record mixin_of (M : monad) : Type := Mixin {
  choice : forall (p : prob) T, M T -> M T -> M T
           where "a <| p |> b" := (choice p a b) ;
  (* identity axioms *)
  _ : forall T (a b : M T), a <| 0%:pr |> b = b ;
  _ : forall T (a b : M T), a <| 1%:pr |> b = a ;
  (* skewed commutativity *)
  _ : forall T p (a b : M T), a <| p |> b = b <| p.~%:pr |> a ;
  _ : forall T p, idempotent (@choice p T) ;
  (* quasi associativity *)
  _ : forall T (p q r s : prob) (a b c : M T),
    (p = r * s :> R /\ s.~ = p.~ * q.~)%R ->
    a <| p |> (b <| q |> c) = (a <| r |> b) <| s |> c ;
  (* composition distributes leftwards over [probabilistic] choice *)
  _ : forall p, BindLaws.left_distributive (@Bind M) (choice p) }.
Record class_of (m : Type -> Type) := Class {
  base : Monad.class_of m ; mixin : mixin_of (Monad.Pack base) }.
Structure t := Pack { m : Type -> Type ; class : class_of m }.
Definition baseType (M : t) := Monad.Pack (MonadProb.base (class M)).
Module Exports.
Definition Choice (M : t) : forall p T, m M T -> m M T -> m M T :=
  let: Pack _ (Class _ (Mixin x _ _ _ _ _ _ )) := M return
    forall p T, m M T -> m M T -> m M T in x.
Arguments Choice {M} : simpl never.
Notation "a <| p |> b" := (Choice p _ a b) : proba_monad_scope.
Notation probMonad := t.
Coercion baseType : probMonad >-> monad.
Canonical baseType.
End Exports.
End MonadProb.
Export MonadProb.Exports.

Local Open Scope proba_monad_scope.

Section prob_lemmas.
Variable (M : probMonad).
Lemma choicemm : forall A p, idempotent (@Choice M p A).
Proof. by case: M => m [? []]. Qed.
Lemma choice0 : forall A (mx my : M A), mx <| 0%:pr |> my = my.
Proof. by case: M => m [? []]. Qed.
Lemma choice1 : forall A (mx my : M A), mx <| 1%:pr |> my = mx.
Proof. by case: M => m [? []]. Qed.
Lemma choiceA A : forall (p q r s : prob) (mx my mz : M A),
    (p = r * s :> R /\ s.~ = p.~ * q.~)%R ->
    mx <| p |> (my <| q |> mz) = (mx <| r |> my) <| s |> mz.
Proof. by case: M A => m [? []]. Qed.
Lemma choiceC : forall A (p : prob) (mx my : M A), mx <| p |> my = my <| p.~%:pr |> mx.
Proof. by case: M => m [? []]. Qed.
Lemma prob_bindDl p : BindLaws.left_distributive (@Bind M) (Choice p).
Proof. by case: M => m [? []]. Qed.
End prob_lemmas.
Arguments choiceA {M} {A} _ _ _ _ {mx} {my} {mz}.
Arguments choiceC {M} {A} _ {mx} {my}.

Section convex.
Variable M : probMonad.
Variable A : Type.

Import fdist convex_choice ConvexSpace.

Definition prob_mixin : mixin_of (choice_of_Type (M A)).
apply (@Class _ (fun p (a b : choice_of_Type (M A)) => Choice p A a b)).
- apply choice1.
- apply choicemm.
- apply choiceC.
- move=> p q a b c.
  apply (choiceA p q).
  by rewrite -p_is_rs s_of_pqE onemK.
Defined.

Definition probConvex := Pack prob_mixin.
End convex.

Arguments probConvex {M} {A}.

Fixpoint uniform {M : probMonad} {A} (def(*NB: Coq functions are total*) : A) (s : seq A) : M A :=
  match s with
    | [::] => Ret def
    | [:: x] => Ret x
    | x :: xs => Ret x <| (/ IZR (Z_of_nat (size (x :: xs))))%:pr |> uniform def xs
  end.

Lemma uniform_nil (M : probMonad) A (def : A) :
  uniform def [::] = Ret def :> M A.
Proof. by []. Qed.

Lemma choice_ext (q p : prob) (M : probMonad) A (m1 m2 : M A) :
  p = q :> R -> m1 <| p |> m2 = m1 <| q |> m2.
Proof. by move/prob_ext => ->. Qed.

Lemma uniform_cons (M : probMonad) A (def : A) h s :
  uniform def (h :: s) = Ret h <| (/ IZR (Z_of_nat (size (h :: s))))%:pr |> uniform def s :> M A.
Proof.
case: s => //.
rewrite (@choice_ext 1%:pr) // ?choice1 //.
by rewrite /= Rinv_1.
Qed.

Lemma uniform_singl (M : probMonad) A (def : A) h : size h = 1%nat ->
  uniform def h = Ret (head def h) :> M A.
Proof.
case: h => // h [|//] _.
by rewrite uniform_cons uniform_nil (@choice_ext 1%:pr) ?choice1 //= invR1.
Qed.

Lemma uniform_nseq (M : probMonad) A (def : A) h n :
  uniform def (nseq n.+1 h) = Ret h :> M A.
Proof.
elim: n => // n IH.
by rewrite (_ : nseq _ _ = h :: nseq n.+1 h) // uniform_cons IH choicemm.
Qed.

Lemma uniform_cat (M : probMonad) A (a : A) s t :
  let m := size s in let n := size t in
  uniform a (s ++ t) = uniform a s <| (divRnnm m n)%:pr |> uniform a t :> M _.
Proof.
elim: s t => [t m n|s1 s2 IH t m n].
  rewrite cat0s uniform_nil /= [X in _ <| X |> _](_ : _ = 0%:pr) ?choice0 //.
  by apply prob_ext => /=; rewrite /divRnnm div0R.
case/boolP : (m.-1 + n == 0)%nat => [{IH}|] m1n0.
  have s20 : s2 = [::] by move: m1n0; rewrite {}/m /=; case: s2.
  have t0 : t = [::] by move: m1n0; rewrite {}/n /= addnC; case: t.
  subst s2 t.
  rewrite cats0 (_ : Prob.mk _ = 1%:pr) ?choice1 //.
  by apply prob_ext => /=; rewrite /divRnnm div1R invR1.
rewrite cat_cons uniform_cons uniform_cons.
set pv := ((/ _)%R).
set v : prob := @Prob.mk pv _.
set u := @Prob.mk (INR (size s2) / INR (size s2 + size t))%R (prob_divRnnm _ _).
rewrite -[RHS](choiceA v u).
  by rewrite -IH.
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

Lemma uniform2 (M : probMonad) A (def : A) a b :
  uniform def [:: a; b] = uniform def [:: b; a] :> M _.
Proof.
rewrite uniform_cons uniform_singl // uniform_cons uniform_singl //.
set pa := Prob.mk _.
rewrite choiceC /= (@choice_ext pa) //=.
rewrite /onem; field.
Qed.

Module MonadProbDr.
Record mixin_of (M : probMonad) : Type := Mixin {
  (* composition distributes rightwards over [probabilistic] choice *)
  (* WARNING: this should not be asserted as an axiom in conjunction with distributivity of <||> over [] *)
  prob_bindDr : forall p, BindLaws.right_distributive (@Bind M) (Choice p) (* NB: not used *)
} .
Record class_of (m : Type -> Type) := Class {
  base : MonadProb.class_of m ;
  mixin : mixin_of (MonadProb.Pack base) }.
Structure t := Pack { m : Type -> Type; class : class_of m }.
Definition baseType (M : t) := MonadProb.Pack (base (class M)).
Module Exports.
Notation probDrMonad := t.
Coercion baseType : probDrMonad >-> probMonad.
Canonical baseType.
End Exports.
End MonadProbDr.
Export MonadProbDr.Exports.

Lemma uniform_inde (M : probMonad) A a (x : seq A) {B} (m : M B) :
  uniform a x >> m = m.
Proof.
elim: x m => [/= m|x xs IH m]; first by rewrite bindretf.
by rewrite uniform_cons prob_bindDl IH bindretf choicemm.
Qed.

Lemma uniform_naturality (M : probMonad) A B (a : A) (b : B) (f : A -> B) :
  forall x, (0 < size x)%nat ->
  ((@uniform M _ b) \o map f) x = ((M # f) \o uniform a) x.
Proof.
elim=> // x [_ _|x' xs]; first by rewrite [in RHS]compE fmapE bindretf.
move/(_ isT) => IH _.
rewrite compE [in RHS]compE [in LHS]uniform_cons [in RHS]uniform_cons.
set p := (@Prob.mk (/ IZR (Z.of_nat (size _)))%R _ in X in _ = X).
rewrite (_ : @Prob.mk (/ _)%R _ = p); last first.
  by apply prob_ext => /=; rewrite size_map.
move: IH; rewrite 2!compE => ->.
by rewrite [in RHS]fmapE prob_bindDl bindretf fmapE; congr Choice.
Qed.
Arguments uniform_naturality {M A B}.

Lemma mpair_uniform_base_case (M : probMonad) A a x (y : seq A) :
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

(* uniform choices are independent, in the sense that choosing consecutively
from two uniform distributions is equivalent to choosing simultaneously from
their cartesian product *)
Lemma mpair_uniform (M : probMonad) A a (x y : seq A) :
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
  rewrite -/(cp _ _) -/l.
  by apply prob_ext => /=.
pose m := size xxs.
have lmn : (l = m * n)%nat by rewrite /l /m /n size_allpairs.
rewrite (_ : probdivRnnm _ _ = @Prob.mk (/ (INR (1 + m))) (prob_invn _))%R; last first.
  apply prob_ext => /=.
  rewrite lmn /divRnnm -mulSn mult_INR {1}/Rdiv Rinv_mult_distr; last 2 first.
    by rewrite INR_eq0.
    by rewrite INR_eq0; apply/eqP; rewrite -lt0n.
  rewrite mulRC -mulRA mulVR; last by rewrite INR_eq0' -lt0n.
  by rewrite mulR1 -addn1 addnC.
rewrite -IH //.
rewrite -/xxs.
move: (@mpair_uniform_base_case M _ a x _ size_y).
rewrite {1}/cp [in X in uniform _ X]/= cats0 => ->.
rewrite -prob_bindDl.
rewrite [in RHS]/mpair uniform_cat.
rewrite [in RHS](_ : Prob.mk _ = probinvn m) //.
by apply prob_ext => /=; rewrite /divRnnm div1R.
Qed.

Module MonadAltProb.
Record mixin_of (M : altCIMonad) (f : prob -> forall T, M T -> M T -> M T) := Mixin {
  _ : forall T p, right_distributive (f p T) (fun a b => a [~] b) }.
Record class_of (m : Type -> Type) := Class {
  base : MonadAltCI.class_of m ;
  base2 : MonadProb.mixin_of (Monad.Pack (MonadAlt.base (MonadAltCI.base base))) ;
  mixin : @mixin_of (MonadAltCI.Pack base) (@MonadProb.choice _ base2)
}.
Structure t : Type := Pack { m : Type -> Type ; class : class_of m }.
Definition baseType (M : t) : altCIMonad := MonadAltCI.Pack (base (class M)).
Definition altType (M : t) : altMonad := MonadAlt.Pack (MonadAltCI.base (base (class M))).
Module Exports.
Notation altProbMonad := t.
Coercion baseType : altProbMonad >-> altCIMonad.
Canonical baseType.
Definition altprob_is_prob M :=
  MonadProb.Pack (MonadProb.Class (base2 (class M))).
Canonical altprob_is_prob.
Canonical altType.
End Exports.
End MonadAltProb.
Export MonadAltProb.Exports.

Section altprob_lemmas.
Variable (M : altProbMonad).
Lemma choiceDr : forall A p,
  right_distributive (fun x y : M A => x <| p |> y) (fun x y => x [~] y).
Proof. by case: M => m [? ? []]. Qed.
End altprob_lemmas.

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

(* biased coin *)
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

(* TODO: move to Reals_ext.v? *)
(* Not needed here anymore *)
Lemma prob_invp : (0 <= 1 / (1+p) <= 1)%R.
Proof.
split.
- apply divR_ge0 => //; exact: addR_gt0wl.
- rewrite leR_pdivr_mulr ?mul1R; last exact: addR_gt0wl.
  by rewrite addRC -leR_subl_addr subRR.
Qed.
Definition Prob_invp := Prob.mk prob_invp.

Lemma two_coinsE : two_coins = two_coins'.
Proof.
rewrite /two_coins /two_coins' /bcoin.
rewrite prob_bindDl.
rewrite !bindretf.
rewrite !(prob_bindDl,bindretf).
apply (@convex_choice.convACA probConvex).
Qed.
End prob_only.

(* arbitrary nondeterministic choice between booleans *)
Definition arb {M : altMonad} : M bool := Ret true [~] Ret false.

Section mixing_choices.

Variable M : altProbMonad.

Definition arbcoin p : M bool :=
  (do a <- arb ; (do c <- bcoin p; Ret (a == c) : M _))%Do.
Definition coinarb p : M bool :=
  (do c <- bcoin p ; (do a <- arb; Ret (a == c) : M _))%Do.

Lemma Ret_eqb_addL b :
  (fun c => Ret (b == c)) = (fun c => Ret (~~ b (+) c)) :> (bool -> M bool).
Proof. case: b; rewrite boolp.funeqE; by case. Qed.

Lemma Ret_eqb_addR b :
  (fun c => Ret (c == b)) = (fun c => Ret (~~ b (+) c)) :> (bool -> M bool).
Proof. case: b; rewrite boolp.funeqE; by case. Qed.

Definition Ret_eqb_add := (Ret_eqb_addL, Ret_eqb_addR).

Lemma arbcoin_spec p :
  arbcoin p = (bcoin p : M _) [~] bcoin p.~%:pr.
Proof.
rewrite /arbcoin /arb.
rewrite alt_bindDl.
rewrite 2!bindretf.
rewrite 2!Ret_eqb_add ![fun _ => Ret _]/=.
rewrite bindmret; congr (_ [~] _).
rewrite [in RHS]/bcoin choiceC.
rewrite [in RHS](@choice_ext p); last by rewrite /= onemK.
by rewrite {1}/bcoin prob_bindDl 2!bindretf.
Qed.

Lemma coinarb_spec p : coinarb p = arb.
Proof.
rewrite [in LHS]/coinarb [in LHS]/bcoin.
rewrite prob_bindDl.
rewrite 2!bindretf.
rewrite 2!Ret_eqb_add [fun _ => Ret _]/= [in X in _ <| _ |> X = _]/=.
rewrite bindmret.
rewrite {2}/arb alt_bindDl !bindretf [Ret _]/= [Ret (~~ _)]/=.
rewrite {1}/arb.
by rewrite altC choicemm altC.
Qed.

Lemma coinarb_spec_convexity p w : coinarb p =
  (bcoin w : M _) [~] (Ret false : M _) [~] (Ret true : M _) [~] bcoin w.~%:pr.
Proof.
rewrite coinarb_spec [in LHS]/arb [in LHS](convexity _ _ w) 2!choicemm.
rewrite [in LHS]altC -(altA _ (Ret false)) altCA -2![in RHS]altA; congr (_ [~] _).
rewrite -altA altCA; congr (_ [~] _).
by rewrite /bcoin choiceC altC.
Qed.

End mixing_choices.

Module MonadExceptProb.
Record mixin_of (M : exceptMonad) (a : prob -> forall A : Type, M A -> M A -> M A) := Mixin {
  catchDl : forall A w, left_distributive (@Catch M A) (fun x y => a w A x y)
    (* NB: not used? *)
}.
Record class_of (m : Type -> Type) := Class {
  base : MonadExcept.class_of m ;
  base2 : MonadProb.mixin_of (Monad.Pack (MonadFail.base (MonadExcept.base base))) ;
  mixin : @mixin_of (MonadExcept.Pack base) (@Choice (MonadProb.Pack (MonadProb.Class base2)))
}.
Structure t : Type := Pack { m : Type -> Type ; class : class_of m }.
Definition baseType (M : t) : exceptMonad := MonadExcept.Pack (base (class M)).
Module Exports.
Notation exceptProbMonad := t.
Coercion baseType : exceptProbMonad >-> exceptMonad.
Canonical baseType.
Definition prob_of_exceptprob M :=
  MonadProb.Pack (MonadProb.Class (base2 (class M))).
Canonical prob_of_exceptprob.
End Exports.
End MonadExceptProb.
Export MonadExceptProb.Exports.

Definition coins23 {M : exceptProbMonad} : M bool :=
  Ret true <| (/ 2)%:pr |> (Ret false <| (/ 2)%:pr |> (Fail : M _)).

Lemma H23 : (0 <= 2/3 <= 1)%R. Proof. split; lra. Qed.

(* NB: notation for ltac:(split; fourier?)*)
Lemma choiceA_compute {N : probMonad} (T F : bool) (f : bool -> N bool) :
  f T <|(/ 9)%:pr|> (f F <|(/ 8)%:pr|> (f F <|(/ 7)%:pr|> (f F <|(/ 6)%:pr|>
 (f T <|(/ 5)%:pr|> (f F <|(/ 4)%:pr|> (f F <|(/ 3)%:pr|> (f F <|(/ 2)%:pr|>
  f T))))))) = f F <|(/ 3)%:pr|> (f F <|(/ 2)%:pr|> f T) :> N _.
Proof.
have H34 : (0 <= 3/4 <= 1)%R by split; lra.
have H27 : (0 <= 2/7 <= 1)%R by split; lra.
have H721 : (0 <= 7/21 <= 1)%R by split; lra.
have H2156 : (0 <= 21/56 <= 1)%R by split; lra.
have H25 : (0 <= 2/5 <= 1)%R by split; lra.
rewrite [in RHS](choiceA _ _ (/ 2)%:pr (@Prob.mk (2/3) H23)); last first.
  by rewrite 3!probpK /= /onem; split; field.
rewrite choicemm.
rewrite [in LHS](choiceA (/ 3)%:pr (/ 2)%:pr (/ 2)%:pr (@Prob.mk (2/3) H23)); last first.
  by rewrite 3!probpK /= /onem; split; field.
rewrite choicemm.
rewrite [in LHS](choiceA (/ 4)%:pr (@Prob.mk (2/3) H23) (/ 3)%:pr (@Prob.mk (3/4) H34)); last first.
  by rewrite 4!probpK /= /onem; split; field.
rewrite choicemm.
rewrite [in LHS](choiceA (/ 7)%:pr (/ 6)%:pr (/ 2)%:pr (@Prob.mk (2/7) H27)); last first.
  by rewrite 4!probpK /= /onem; split; field.
rewrite choicemm.
rewrite [in LHS](choiceA (/ 8)%:pr (@Prob.mk (2/7) H27) (@Prob.mk (7/21) H721) (@Prob.mk (21/56) H2156)); last first.
  by rewrite 4!probpK /= /onem; split; field.
rewrite (choiceC (@Prob.mk (3/4) H34)).
rewrite [in LHS](choiceA (/ 5)%:pr (probcplt (@Prob.mk (3/4) H34)) (/ 2)%:pr (@Prob.mk (2/5) H25)); last first.
  by rewrite 3!probpK /= /onem; split; field.
rewrite choicemm.
rewrite choicemm.
rewrite (choiceC (@Prob.mk (2/5) H25)).
rewrite [in LHS](choiceA (@Prob.mk (21/56) H2156) (probcplt (Prob.mk H25)) (/ 2)%:pr (Prob.mk H34)); last first.
  by rewrite 3!probpK /= /onem; split; field.
rewrite choicemm.
rewrite (choiceC (Prob.mk H34)).
rewrite [in LHS](choiceA (/ 9)%:pr (probcplt (Prob.mk H34)) (/ 3)%:pr (/ 3)%:pr); last first.
  by rewrite 3!probpK /= /onem; split; field.
rewrite choicemm choiceC.
rewrite (@choice_ext (Prob.mk H23)) //= /onem; by field.
Qed.

Definition uFFT {M : probMonad} : M bool :=
  uniform true [:: false; false; true].

Lemma uFFTE (M : probMonad) : uFFT = bcoin (/ 3)%:pr :> M _.
Proof.
rewrite /uFFT /bcoin uniform_cons.
rewrite (_ : _%:pr = (/ 3)%:pr)%R; last exact/prob_ext.
rewrite uniform_cons.
rewrite [in X in _ <| _ |> X](_ : _%:pr = (/ 2)%:pr)%R; last first.
  exact/prob_ext.
rewrite uniform_singl //=.
rewrite (choiceA _ _ (/ 2)%:pr (Prob.mk H23)); last first.
  rewrite /= /onem; split; field.
rewrite choicemm choiceC.
rewrite (_ : (/ 3)%:pr = probcplt (Prob.mk H23)) //.
apply prob_ext => /=; rewrite /onem; field.
Qed.

Definition uTTF {M : probMonad} : M bool :=
  uniform true [:: true; true; false].

Lemma uTTFE (M : probMonad) : uTTF = bcoin (@Prob.mk (2/3) H23) :> M _.
Proof.
rewrite /uTTF /bcoin uniform_cons.
rewrite (_ : _%:pr = (/ 3)%:pr)%R; last exact: prob_ext.
rewrite uniform_cons.
rewrite [in X in _ <| _ |> X](_ : _%:pr = (/ 2)%:pr)%R; last exact/prob_ext.
rewrite uniform_singl //=.
rewrite (choiceA _ _ (/ 2)%:pr (Prob.mk H23)); last first.
  rewrite /= /onem; split; field.
by rewrite choicemm choiceC.
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
  rewrite (_ : _%:pr = 1%:pr); last by apply prob_ext => /=; rewrite Rinv_1.
  rewrite choice1.
  rewrite 2!bindretf ifF //; apply/negbTE/H; by rewrite mem_head.
rewrite 2!prob_bindDl; congr (_ <| _ |> _).
  rewrite 2!bindretf ifF //; apply/negbTE/H; by rewrite mem_head.
by rewrite IH // => a ta; rewrite H // in_cons ta orbT.
Qed.
