Require Import FunctionalExtensionality Coq.Program.Tactics ProofIrrelevance.
Require Classical.
Require Import Reals Lra.
Require Import ssreflect ssrmatching ssrfun ssrbool.
From mathcomp Require Import eqtype ssrnat seq choice fintype tuple.

Require Import monad.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*
Contents:
- Definition of probabilities
- Module MonadProb.
    probabilistic choice
    example of the function that perfoms a uniform choice
- Module MonadProbDr.
    probabilistic choice + bind left-distributes other choice
- Module MonadAltProb.
    Module MonadAltProb + non-deterministic choice
- Section mixing_choices.
    example illustrating the combined use of probabilistic and non-deterministic choice
- Module MonadExceptProb.
    probabilistic choice + exception
- Module Set3.
    a small theory about sets of three elements for the Monty Hall example
- Section monty
  + using the probabilistic choice only
  + probabilistic choice and non-deterministic choice
  + Section forgetful_monty.
    probabilistic choice and exception
*)

Reserved Notation "[Pr 'of' p ]" (format "[Pr  'of'  p ]").
Reserved Notation "mx <| p |> my" (format "mx  <| p |>  my", at level 50).

(* NB(rei): proofs would be more comfortable with ssrR.v from infotheo *)

(* NB(rei): notation already available in infotheo/Reals_ext. *)
Reserved Notation "p '.~'" (format "p .~", at level 5).
Notation "p '.~'" := (1 - p)%R.

Lemma onemK (p : R) : (p.~).~ = p. Proof. by field. Qed.

Lemma onem_prob (p : R) : (R0 <= p <= R1)%R -> (R0 <= p.~ <= R1)%R.
Proof.
case=> pO p1; split.
apply Rplus_le_reg_r with p.
by rewrite Rplus_0_l Rplus_assoc Rplus_opp_l Rplus_0_r.
apply Rplus_le_reg_r with p.
rewrite Rplus_assoc  Rplus_opp_l; exact: Rplus_le_compat_l.
Qed.

Module Prob.
Record t := mk {
  p : R ;
  H : (0 <= p <= 1)%R }.
Definition H' (p : t) := H p.
Arguments H' : simpl never.
Module Exports.
Notation "[Pr 'of' q ]" := (@mk q (@H' _)).
Coercion p : t >-> R.
End Exports.
End Prob.
Export Prob.Exports.

Lemma probpK p H : Prob.p (@Prob.mk p H) = p. Proof. by []. Qed.

Lemma OO1 : (R0 <= R0 <= R1)%R.
Proof.
rewrite (_ : R0 = INR 0) // (_ : R1 = INR 1) //; by split; apply/le_INR/leP.
Qed.

Lemma O11 : (R0 <= R1 <= R1)%R.
Proof.
rewrite (_ : R0 = INR 0) // (_ : R1 = INR 1) //; by split; apply/le_INR/leP.
Qed.

Canonical prob0 := Prob.mk OO1.
Canonical prob1 := Prob.mk O11.
Canonical probcplt (p : Prob.t) := @Prob.mk p.~ (onem_prob (Prob.H p)).

Lemma prob_IZR (p : positive) : (R0 <= / IZR (Zpos p) <= R1)%R.
Proof.
split; first exact/Rlt_le/Rinv_0_lt_compat/IZR_lt/Pos2Z.is_pos.
rewrite -[X in (_ <= X)%R]Rinv_1; apply Rle_Rinv.
- exact: Rlt_0_1.
- exact/IZR_lt/Pos2Z.is_pos.
- exact/IZR_le/Pos2Z.pos_le_pos/Pos.le_1_l.
Qed.

Canonical probIZR (p : positive) := @Prob.mk _ (prob_IZR p).

Lemma prob_addn (n m : nat) : (R0 <= INR n / INR (n + m) <= R1)%R.
Proof.
have [/eqP ->|n0] := boolP (n == O).
  rewrite /Rdiv Rmult_0_l; exact OO1.
split.
  apply Fourier_util.Rle_mult_inv_pos; first exact: pos_INR.
  by apply/lt_0_INR/ltP; rewrite addn_gt0 lt0n n0.
apply (Rmult_le_reg_l (INR (n + m))).
  by apply/lt_0_INR/ltP; rewrite addn_gt0 lt0n n0.
rewrite -Rmult_assoc Rinv_r_simpl_m ?Rmult_1_r.
  by apply/le_INR/leP; rewrite leq_addr.
by apply/not_O_INR/eqP; rewrite addn_eq0 negb_and n0.
Qed.

Canonical probaddn (n m : nat) := @Prob.mk (INR n / INR (n + m)) (prob_addn n m).

Lemma prob_invn (m : nat) : (R0 <= / INR (1 + m) <= R1)%R.
Proof.
rewrite -(Rmult_1_l (/ _)) (_ : 1%R = INR 1) // -/(Rdiv _ _).
exact: prob_addn.
Qed.

Canonical probinvn (n : nat) := @Prob.mk (/ INR (1 + n)) (prob_invn n).

Module MonadProb.
Record mixin_of (M : monad) : Type := Mixin {
  choice : forall (p : Prob.t) A, M A -> M A -> M A
           where "mx <| p |> my" := (choice p mx my) ;
  (* identity laws *)
  _ : forall A (mx my : M A), mx <| [Pr of 0] |> my = my ;
  _ : forall A (mx my : M A), mx <| [Pr of 1] |> my = mx ;
  (* skewed commutativity law *)
  _ : forall A p (mx my : M A), mx <| p |> my = my <| [Pr of p.~] |> mx ;
  _ : forall A p, idempotent (@choice p A) ;
  (* quasi associativity *)
  _ : forall A (p q r s : Prob.t) (mx my mz : M A),
    (p = r * s :> R /\ s.~ = p.~ * q.~)%R ->
    mx <| p |> (my <| q |> mz) = (mx <| r |> my) <| s |> mz ;
  (* composition distributes leftwards over [probabilistic] choice *)
  _ : forall p, Laws.bind_left_distributive (@Bind M) (choice p)
}.
Record class_of (m : Type -> Type) := Class {
  base : Monad.class_of m ; mixin : mixin_of (Monad.Pack base) }.
Structure t := Pack { m : Type -> Type ; class : class_of m }.
Definition op_choice (M : t) : forall p A, m M A -> m M A -> m M A :=
  let: Pack _ (Class _ (Mixin x _ _ _ _ _ _ )) := M return
    forall p A, m M A -> m M A -> m M A in x.
Arguments op_choice {M} : simpl never.
Definition baseType (M : t) := Monad.Pack (MonadProb.base (class M)).
Module Exports.
Notation Choice := op_choice.
Notation "mx <| p |> my" := (Choice p _ mx my).
Notation probMonad := t.
Coercion baseType : probMonad >-> monad.
Canonical baseType.
End Exports.
End MonadProb.
Export MonadProb.Exports.

Section prob_lemmas.
Variable (M : probMonad).
Lemma choicemm : forall A p, idempotent (@Choice M p A).
Proof. by case: M => m [? []]. Qed.
Lemma choice0 : forall A (mx my : M A), mx <| [Pr of 0] |> my = my.
Proof. by case: M => m [? []]. Qed.
Lemma choice1 : forall A (mx my : M A), mx <| [Pr of 1] |> my = mx.
Proof. by case: M => m [? []]. Qed.
Lemma choiceA A : forall (p q r s : Prob.t) (mx my mz : M A),
    (p = r * s :> R /\ s.~ = p.~ * q.~)%R ->
    mx <| p |> (my <| q |> mz) = (mx <| r |> my) <| s |> mz.
Proof. by case: M A => m [? []]. Qed.
Lemma choiceC : forall A (p : Prob.t) (mx my : M A), mx <| p |> my = my <| [Pr of p.~] |> mx.
Proof. by case: M => m [? []]. Qed.
Lemma prob_bindDl p : Laws.bind_left_distributive (@Bind M) (Choice p).
Proof. by case: M => m [? []]. Qed.
End prob_lemmas.
Arguments choiceA {M} {A} _ _ _ _ {mx} {my} {mz}.
Arguments choiceC {M} {A} _ {mx} {my}.

Fixpoint uniform {M : probMonad} {A} (def(*NB: Coq functions are total*) : A) (s : seq A) : M A :=
  match s with
    | [::] => Ret def
    | [:: x] => Ret x
    | x :: xs => Ret x <| [Pr of / IZR (Z_of_nat (size (x :: xs)))] |> uniform def xs
  end.

Lemma uniform_nil (M : probMonad) A (def : A) :
  uniform def [::] = Ret def :> M A.
Proof. by []. Qed.

Lemma prob_ext (p q : Prob.t) : Prob.p p = Prob.p q -> p = q.
Proof.
move: p q => [p Hp] [q Hq] /= ?; subst q; f_equal; exact: proof_irrelevance.
Qed.

Lemma choice_ext (q p : Prob.t) (M : probMonad) A (m1 m2 : M A) :
  p = q :> R -> m1 <| p |> m2 = m1 <| q |> m2.
Proof. by move/prob_ext => ->. Qed.

Lemma uniform_cons (M : probMonad) A (def : A) h s :
  uniform def (h :: s) = Ret h <| [Pr of / IZR (Z_of_nat (size (h :: s)))] |> uniform def s :> M A.
Proof.
case: s => //.
rewrite (@choice_ext [Pr of 1]) // ?choice1 //.
by rewrite /= Rinv_1.
Qed.

Lemma uniform_singl (M : probMonad) A (def : A) h : size h = 1%nat ->
  uniform def h = Ret (head def h) :> M A.
Proof.
case: h => // h [|//] _.
rewrite uniform_cons uniform_nil (@choice_ext [Pr of 1]) ?choice1 //.
by rewrite /= Rinv_1.
Qed.

Lemma uniform_nseq (M : probMonad) A (def : A) h n :
  uniform def (nseq n.+1 h) = Ret h :> M A.
Proof.
elim: n => // n IH.
by rewrite (_ : nseq _ _ = h :: nseq n.+1 h) // uniform_cons IH choicemm.
Qed.

Lemma uniform_cat (M : probMonad) A (a : A) s t :
  let m := size s in let n := size t in
  uniform a (s ++ t) = uniform a s <| [Pr of INR m / INR (m + n)] |> uniform a t :> M _.
Proof.
elim: s t => [t m n|s1 s2 IH t m n].
  rewrite cat0s uniform_nil /= [X in _ <| X |> _](_ : _ = [Pr of 0]) ?choice0 //.
  by apply prob_ext => /=; rewrite /Rdiv Rmult_0_l.
case/boolP : (m.-1 + n == 0)%nat => [{IH}|] m1n0.
  have s20 : s2 = [::] by move: m1n0; rewrite {}/m /=; case: s2.
  have t0 : t = [::] by move: m1n0; rewrite {}/n /= addnC; case: t.
  subst s2 t.
  rewrite cats0 (_ : Prob.mk _ = [Pr of 1]) ?choice1 //.
  by apply prob_ext => /=; rewrite /Rdiv Rmult_1_l Rinv_1.
rewrite cat_cons uniform_cons uniform_cons.
set pv := ((/ _)%R).
set v : Prob.t := @Prob.mk pv _.
set u := @Prob.mk (INR (size s2) / INR (size s2 + size t))%R (prob_addn _ _).
rewrite -[RHS](choiceA v u).
  by rewrite -IH.
split.
  rewrite 3!probpK.
  rewrite -INR_IZR_INZ.
  rewrite (_ : INR _ = INR m) // -Rmult_assoc Rinv_l; last exact: not_0_INR.
  rewrite /pv.
  rewrite -INR_IZR_INZ.
  by rewrite Rmult_1_l /v [size _]/= size_cat -addSn.
rewrite 3!probpK.
transitivity ( (1 - 1 / INR (m + n)) * (1 - INR (m.-1) / INR (m.-1 + n)))%R; last first.
  congr (_ .~ * _)%R.
  by rewrite /v /pv probpK INR_IZR_INZ [size _]/= size_cat -addSn {1}/Rdiv Rmult_1_l.
transitivity (INR n / INR (m + n))%R.
  rewrite -{1}(Rinv_r (INR (m + n))); last exact/not_0_INR.
  rewrite -Rdiv_minus_distr -minus_INR; last by apply/leP; rewrite leq_addr.
  by rewrite minusE addnC addnK.
rewrite {1}/Rdiv Rmult_comm.
rewrite {1}/Rdiv -[in LHS](Rmult_1_l (INR n)).
rewrite -{1}(Rinv_r (INR (m.-1 + n))); last exact/not_0_INR/eqP.
rewrite -2!Rmult_assoc (Rmult_assoc (_ * _)); congr Rmult.
  rewrite Rmult_comm -subn1.
  rewrite addnC addnBA // minus_INR; last by apply/leP; rewrite addn_gt0 orbT.
  rewrite -/(_ / INR (m + n))%R.
  rewrite Rdiv_minus_distr {1}/Rdiv addnC Rinv_r //; exact/not_0_INR.
rewrite -{1}(Rinv_r (INR (m.-1 + n))); last exact/not_0_INR/eqP.
rewrite -Rdiv_minus_distr Rmult_comm; congr (_ * _)%R.
rewrite -minus_INR; last by apply/leP; rewrite leq_addr.
by rewrite addnC minusE -subnBA // subnn subn0.
Qed.

Lemma uniform2 (M : probMonad) A (def : A) a b :
  uniform def [:: a; b] = uniform def [:: b; a] :> M _.
Proof.
rewrite uniform_cons uniform_singl // uniform_cons uniform_singl //.
set pa := Prob.mk _.
rewrite choiceC /= (@choice_ext pa) //=.
field.
Qed.

Module MonadProbDr.
Record mixin_of (M : probMonad) : Type := Mixin {
  (* composition distributes rightwards over [probabilistic] choice *)
  (* WARNING: this should not be asserted as an axiom in conjunction with distributivity of <||> over [] *)
  prob_bindDr : forall p, Laws.bind_right_distributive (@Bind M) (Choice p) (* NB: not used *)
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
  do x <- uniform a x; m = m.
Proof.
elim: x m => [/= m|x xs IH m]; first by rewrite bindretf.
by rewrite uniform_cons prob_bindDl IH bindretf choicemm.
Qed.

Lemma uniform_naturality (M : probMonad) A B (a : A) (b : B) (f : A -> B) :
  forall x, (0 < size x)%nat ->
  ((@uniform M _ b) \o map f) x = (fmap f \o uniform a) x.
Proof.
elim=> // x [_ _|x' xs].
  rewrite [fmap]lock /= -lock.
  by rewrite /fmap bindretf.
move/(_ isT) => IH _.
rewrite [uniform a]lock [uniform b]lock [fmap]lock /= -3!lock.
rewrite [in LHS]uniform_cons [in RHS]uniform_cons.
set p := (@Prob.mk (/ IZR (Z.of_nat (size _)))%R _ in X in _ = X).
rewrite (_ : @Prob.mk (/ _)%R _ = p); last first.
  by apply prob_ext => /=; rewrite size_map.
rewrite /fmap prob_bindDl bindretf.
by congr Choice.
Qed.

Lemma pair_uniform_base_case (M : probMonad) A a x (y : seq A) :
  (0 < size y)%nat ->
  uniform (a, a) (cp [:: x] y) = pair (uniform a [:: x], uniform a y) :> M _.
Proof.
move=> y0; rewrite cp1.
transitivity (do y' <- @uniform M _ a y; Ret (x, y')).
  by move: (@uniform_naturality M _ _ a (a, a) (fun y' => (x, y')) _ y0).
transitivity (do z <- Ret x; do y' <- @uniform M _ a y; Ret (z, y')).
  by rewrite bindretf.
by [].
Qed.

(* uniform choices are independent, in the sense that choosing consecutively
from two uniform distributions is equivalent to choosing simultaneously from
their cartesian product *)
Lemma pair_uniform (M : probMonad) A a (x y : seq A) :
  (0 < size x)%nat -> (0 < size y)%nat ->
  pair (uniform a x, uniform a y) = uniform (a, a) (cp x y) :> M (A * A)%type.
Proof.
elim: x y => // x; case=> [_ y _ size_y|x' xs IH y _ size_y]; apply/esym.
  exact/pair_uniform_base_case.
set xxs := x' :: xs.
rewrite /cp -cat1s allpairs_cat -/(cp _ _) cp1 uniform_cat.
pose n := size y.
pose l := size (cp xxs y).
rewrite (_ : size _ = n); last by rewrite size_map.
rewrite (_ : Prob.mk _ = probaddn n l); last first.
  rewrite -/(cp _ _) -/l.
  by apply prob_ext => /=.
pose m := size xxs.
have lmn : (l = m * n)%nat by rewrite /l /m /n size_allpairs.
rewrite (_ : probaddn _ _ = @Prob.mk (/ (INR (1 + m))) (prob_invn _))%R; last first.
  apply prob_ext => /=.
  rewrite lmn -mulSn mult_INR {1}/Rdiv Rinv_mult_distr; last 2 first.
    exact/not_0_INR.
    by apply/not_0_INR/eqP; rewrite -lt0n.
  rewrite Rmult_comm Rmult_assoc Rinv_l; last first.
    by apply/not_0_INR/eqP; rewrite -lt0n.
  by rewrite Rmult_1_r -addn1 addnC.
rewrite -IH //.
rewrite -/xxs.
move: (@pair_uniform_base_case M _ a x _ size_y).
rewrite {1}[cp _ _]/= cats0 => ->.
rewrite -prob_bindDl.
rewrite [in RHS]/pair uniform_cat.
rewrite [in RHS](_ : Prob.mk _ = probinvn m) //.
by apply prob_ext => /=; rewrite /Rdiv Rmult_1_l.
Qed.

Module MonadAltProb.
Record mixin_of (M : altCIMonad) (a : Prob.t -> forall A, M A -> M A -> M A) := Mixin {
  _ : forall A (p : Prob.t),
    right_distributive (fun x y : M A => a p _ x y) (fun x y => Alt x y)
}.
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
  right_distributive (fun x y : M A => x <| p |> y) (fun x y => x [~i] y).
Proof. by case: M => m [? ? []]. Qed.
End altprob_lemmas.

(* TODO(rei): incipit of section 5 of gibbonsUTP2012 on the model of MonadAltProb *)

Section convexity_property.

Variables (M : altProbMonad) (A : Type) (p q : M A).

Lemma convexity w : p [~i] q =
  (p <| w |> p) [~i] (q <| w |> p) [~i] (p <| w |> q) [~i] (q <| w |> q).
Proof.
rewrite -[LHS](choicemm (probcplt w)).
rewrite choiceDr.
rewrite -[in RHS]altA altACA.
rewrite -2![in RHS]choiceDr.
by rewrite -2!choiceC.
Qed.

End convexity_property.

(* biased coin *)
Definition bcoin {M : probMonad} (p : Prob.t) : M bool :=
  Ret true <| p |> Ret false.
Arguments bcoin : simpl never.

(* arbitrary nondeterministic choice between booleans *)
Definition arb {M : altMonad} : M bool := Ret true [~i] Ret false.

Section mixing_choices.

Variable M : altProbMonad.

Definition arbcoin p : M bool :=
  do a <- arb ; (do c <- bcoin p; Ret (a == c) : M _).
Definition coinarb p : M bool :=
  do c <- bcoin p ; (do a <- arb; Ret (a == c) : M _).

Lemma Ret_eqb_addL b :
  (fun c => Ret (b == c)) = (fun c => Ret (~~ b (+) c)) :> (bool -> M bool).
Proof. case: b; apply functional_extensionality; by case. Qed.

Lemma Ret_eqb_addR b :
  (fun c => Ret (c == b)) = (fun c => Ret (~~ b (+) c)) :> (bool -> M bool).
Proof. case: b; apply functional_extensionality; by case. Qed.

Definition Ret_eqb_add := (Ret_eqb_addL, Ret_eqb_addR).

Lemma arbcoin_spec p :
  arbcoin p = (bcoin p : M _ (* TODO *) ) [~i] bcoin [Pr of p.~].
Proof.
rewrite /arbcoin /arb.
rewrite alt_bindDl.
rewrite 2!bindretf.
rewrite 2!Ret_eqb_add ![fun _ => Ret _]/=.
rewrite bindmret; congr (_ [~i] _).
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
  (bcoin w : M _) [~i] Ret false [~i] Ret true [~i] bcoin [Pr of w.~].
Proof.
rewrite coinarb_spec [in LHS]/arb [in LHS](convexity _ _ w) 2!choicemm.
rewrite [in LHS]altC -(altA _ (Ret false)) altCA -2![in RHS]altA; congr (_ [~i] _).
rewrite -altA altCA; congr (_ [~i] _).
by rewrite /bcoin choiceC altC.
Qed.

End mixing_choices.

Module MonadExceptProb.
Record mixin_of (M : exceptMonad) (a : Prob.t -> forall A : Type, M A -> M A -> M A) := Mixin {
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
  Ret true <| [Pr of / 2] |> (Ret false <| [Pr of / 2] |> (Fail : M _)).

Module Set3.
Section set3.

Variable X : finType.
Hypothesis HX : #|X| = 3.

Definition a := enum_val (cast_ord (esym HX) ord0).
Definition b := enum_val (cast_ord (esym HX) (lift ord0 ord0)).
Definition c := enum_val (cast_ord (esym HX) (lift ord0 (lift ord0 ord0))).

Lemma enumE : enum X = [:: a; b; c].
Proof.
apply (@eq_from_nth _ a); first by rewrite -cardE HX.
case=> [_|]; first by rewrite [X in _ = X]/= {2}/a (enum_val_nth a).
case=> [_|]; first by rewrite [X in _ = X]/= {1}/b (enum_val_nth a).
case=> [_|]; first by rewrite [X in _ = X]/= {1}/c (enum_val_nth a).
move=> n; rewrite -cardE HX; by case: n.
Qed.

Lemma a_neq_b : a != b. Proof. by apply/eqP => /enum_val_inj. Qed.

Lemma a_neq_c : a != c. Proof. by apply/eqP => /enum_val_inj. Qed.

Lemma b_neq_c : b != c. Proof. by apply/eqP => /enum_val_inj. Qed.

Lemma neq_a x : x != a -> (x == b) || (x == c).
Proof. have : x \in X by []. by rewrite -mem_enum enumE !inE => /orP[->|]. Qed.

Lemma neq_b x : x != b -> (x == a) || (x == c).
Proof.
have : x \in X by [].
rewrite -mem_enum enumE !inE => /orP[-> //|/orP[] /eqP ->];
  by rewrite ?eqxx // orbT.
Qed.

Lemma neq_c x : x != c -> (x == a) || (x == b).
Proof.
have : x \in X by [].
rewrite -mem_enum enumE !inE => /orP[-> //|/orP[] /eqP ->];
  by rewrite ?eqxx // orbT.
Qed.

Definition another (h p : X) : X := odflt a [pick d | d != h & d != p].

Lemma another_ab : another a b = c.
Proof.
rewrite /another; case: pickP => /= [x|].
have : x \in enum X by rewrite mem_enum.
by rewrite enumE !inE => /or3P[] /eqP ->; rewrite ?eqxx //= ?andbF.
move/(_ c).
by rewrite eq_sym a_neq_c eq_sym b_neq_c.
Qed.

Lemma another_ac : another a c = b.
Proof.
rewrite /another; case: pickP => /= [x|].
have : x \in enum X by rewrite mem_enum.
by rewrite enumE !inE => /or3P[] /eqP ->; rewrite ?eqxx //= ?andbF.
move/(_ b).
by rewrite eq_sym a_neq_b b_neq_c.
Qed.

Lemma another_bc : another b c = a.
Proof.
rewrite /another; case: pickP => /= [x|].
have : x \in enum X by rewrite mem_enum.
by rewrite enumE !inE => /or3P[] /eqP ->; rewrite ?eqxx //= ?andbF.
move/(_ a).
by rewrite a_neq_b a_neq_c.
Qed.

Lemma another_sym h p : another h p = another p h.
Proof. rewrite /another; congr odflt; apply eq_pick => ?; by rewrite andbC. Qed.

Lemma another_notin h p : another h p \notin [:: h; p].
Proof.
rewrite /another; case: pickP => [x /andP[xh xp]|] /=.
  by rewrite !inE negb_or xh xp.
have : h \in enum X by rewrite mem_enum.
rewrite enumE !inE => /or3P[] /eqP ->;
  (have : p \in enum X by rewrite mem_enum);
    rewrite enumE !inE => /or3P[] /eqP ->; rewrite ?eqxx /= ?orbT /= ?negb_or.
move/(_ b); by rewrite eq_sym a_neq_b.
move/(_ c); by rewrite eq_sym a_neq_c eq_sym b_neq_c.
move/(_ b); by rewrite eq_sym a_neq_b b_neq_c.
move/(_ c); by rewrite eq_sym b_neq_c eq_sym a_neq_c.
move/(_ a); by rewrite a_neq_b.
move/(_ a); by rewrite a_neq_b a_neq_c.
move/(_ b); by rewrite b_neq_c eq_sym a_neq_b.
move/(_ a); by rewrite a_neq_c a_neq_b.
move/(_ a); by rewrite a_neq_c.
Qed.

Lemma filter_another h p : h != p -> enum X \\ [:: h; p] = [:: another h p].
Proof.
have : h \in enum X by rewrite mem_enum.
rewrite enumE !inE => /or3P[] /eqP ->;
  (have : p \in enum X by rewrite mem_enum);
    rewrite enumE !inE => /or3P[] /eqP ->;
    rewrite ?eqxx //= !inE ?eqxx ?orbT /=;
    rewrite ?(negbTE a_neq_b) ?(negbTE a_neq_c) ?(negbTE b_neq_c) ?orbF /=;
    rewrite ?(eq_sym c) ?(negbTE b_neq_c) /= ?(negbTE a_neq_c) /=;
    rewrite ?(eq_sym b) ?(negbTE a_neq_b) /= => _.
by rewrite another_ab.
by rewrite another_ac.
by rewrite another_sym another_ab.
by rewrite another_bc.
by rewrite another_sym another_ac.
by rewrite another_sym another_bc.
Qed.

Lemma another_another p h : h != p -> another p (another h p) = h.
Proof.
have : h \in enum X by rewrite mem_enum.
rewrite enumE !inE => /or3P[] /eqP ->;
  (have : p \in enum X by rewrite mem_enum);
    rewrite enumE !inE => /or3P[] /eqP ->;
    rewrite ?eqxx // => _; rewrite ?another_ab ?another_ac ?another_bc //.
by rewrite another_sym another_bc.
by rewrite (another_sym b) another_ab another_ac.
by rewrite another_sym another_ac.
by rewrite (another_sym c) another_ac another_ab.
by rewrite (another_sym c) another_bc another_sym another_ab.
Qed.

(*NB: Lemma filter1_another h p : h != p -> enum X \\ [:: p] =i [:: h; another h p]?*)
Lemma filter1_another h p : h != p ->
  enum X \\ [:: p] = [:: h; another h p] \/ enum X \\ [:: p] = [:: another h p; h].
Proof.
have : h \in enum X by rewrite mem_enum.
rewrite enumE !inE => /or3P[] /eqP ->;
  (have : p \in enum X by rewrite mem_enum);
    rewrite enumE !inE => /or3P[] /eqP ->;
    rewrite ?eqxx // => _; rewrite ?another_ab ?another_ac ?another_bc //.
by rewrite /= !inE a_neq_b eqxx /= eq_sym b_neq_c; left.
by rewrite /= !inE a_neq_c b_neq_c eqxx; left.
by rewrite /= !inE eqxx /= eq_sym a_neq_b eq_sym a_neq_c another_sym another_ab; left.
rewrite /= !inE a_neq_c b_neq_c eqxx /=; by right.
rewrite /= !inE eqxx /= eq_sym a_neq_b eq_sym a_neq_c another_sym another_ac; by right.
rewrite /= !inE a_neq_b eqxx /= eq_sym b_neq_c another_sym another_bc; by right.
Qed.

End set3.
End Set3.

Lemma H23 : (0 <= 2/3 <= 1)%R. Proof. split; lra. Qed.

(* NB: notation for ltac:(split; fourier?)*)
Lemma choiceA_compute {N : probMonad} (T F : bool) (f : bool -> N bool) :
  f T <|[Pr of / 9]|> (f F <|[Pr of / 8]|> (f F <|[Pr of / 7]|> (f F <|[Pr of / 6]|>
 (f T <|[Pr of / 5]|> (f F <|[Pr of / 4]|> (f F <|[Pr of / 3]|> (f F <|[Pr of / 2]|>
  f T))))))) = f F <|[Pr of / 3]|> (f F <|[Pr of / 2]|> f T) :> N _.
Proof.
have H34 : (0 <= 3/4 <= 1)%R by split; lra.
have H27 : (0 <= 2/7 <= 1)%R by split; lra.
have H721 : (0 <= 7/21 <= 1)%R by split; lra.
have H2156 : (0 <= 21/56 <= 1)%R by split; lra.
have H25 : (0 <= 2/5 <= 1)%R by split; lra.
rewrite [in RHS](choiceA _ _ [Pr of /2] (@Prob.mk (2/3) H23)); last by rewrite 3!probpK; split; field.
rewrite choicemm.
rewrite [in LHS](choiceA [Pr of /3] [Pr of /2] [Pr of /2] (@Prob.mk (2/3) H23)); last by rewrite 3!probpK; split; field.
rewrite choicemm.
rewrite [in LHS](choiceA [Pr of /4] (@Prob.mk (2/3) H23) [Pr of /3] (@Prob.mk (3/4) H34)); last by rewrite 4!probpK; split; field.
rewrite choicemm.
rewrite [in LHS](choiceA [Pr of /7] [Pr of /6] [Pr of /2] (@Prob.mk (2/7) H27)); last by rewrite 4!probpK; split; field.
rewrite choicemm.
rewrite [in LHS](choiceA [Pr of /8] (@Prob.mk (2/7) H27) (@Prob.mk (7/21) H721) (@Prob.mk (21/56) H2156)); last by rewrite 4!probpK; split; field.
rewrite (choiceC (@Prob.mk (3/4) H34)).
rewrite [in LHS](choiceA [Pr of /5] (probcplt (@Prob.mk (3/4) H34)) [Pr of /2] (@Prob.mk (2/5) H25)); last by rewrite 3!probpK /=; split; field.
rewrite choicemm.
rewrite choicemm.
rewrite (choiceC (@Prob.mk (2/5) H25)).
rewrite [in LHS](choiceA (@Prob.mk (21/56) H2156) (probcplt (Prob.mk H25)) [Pr of /2] (Prob.mk H34)); last by rewrite 3!probpK /=; split; field.
rewrite choicemm.
rewrite (choiceC (Prob.mk H34)).
rewrite [in LHS](choiceA [Pr of /9] (probcplt (Prob.mk H34)) [Pr of /3] [Pr of /3]); last by rewrite 3!probpK /=; split; field.
rewrite choicemm choiceC.
rewrite (@choice_ext (Prob.mk H23)) //=; by field.
Qed.

Definition uFFT {M : probMonad} : M bool :=
  uniform true [:: false; false; true].

Lemma uFFTE (M : probMonad) : uFFT = bcoin [Pr of /3] :> M _.
Proof.
rewrite /uFFT /bcoin uniform_cons.
rewrite (_ : [Pr of _] = [Pr of /3])%R; last exact/prob_ext.
rewrite uniform_cons.
rewrite [in X in _ <| _ |> X](_ : [Pr of _] = [Pr of /2])%R; last first.
  exact/prob_ext.
rewrite uniform_singl //=.
rewrite (choiceA _ _ [Pr of /2] (Prob.mk H23)); last first.
  rewrite /=; split; field.
rewrite choicemm choiceC.
rewrite (_ : [Pr of /3] = probcplt (Prob.mk H23)) //.
apply prob_ext => /=; field.
Qed.

Definition uTTF {M : probMonad} : M bool :=
  uniform true [:: true; true; false].

Lemma uTTFE (M : probMonad) : uTTF = bcoin (@Prob.mk (2/3) H23) :> M _.
Proof.
rewrite /uTTF /bcoin uniform_cons.
rewrite (_ : [Pr of _] = [Pr of /3])%R; last exact: prob_ext.
rewrite uniform_cons.
rewrite [in X in _ <| _ |> X](_ : [Pr of _] = [Pr of /2])%R; last first.
  exact/prob_ext.
rewrite uniform_singl //=.
rewrite (choiceA _ _ [Pr of /2] (Prob.mk H23)); last first.
  rewrite /=; split; field.
by rewrite choicemm choiceC.
Qed.

Lemma uniform_notin (M : probMonad) (A : eqType) (def : A) (s : seq A) B
  (ma mb : A -> M B) (p : pred A) :
  s != [::] ->
  (forall x, x \in s -> ~~ p x) ->
  (do t <- uniform def s ; if p t then ma t else mb t) =
  (do t <- uniform def s ; mb t).
Proof.
elim: s => [//|h t IH _ H].
rewrite uniform_cons.
case/boolP : (t == [::]) => [/eqP -> {IH}|t0].
  rewrite uniform_nil.
  rewrite (_ : [Pr of _] = [Pr of 1]); last by apply prob_ext => /=; rewrite Rinv_1.
  rewrite choice1.
  rewrite 2!bindretf ifF //; apply/negbTE/H; by rewrite mem_head.
rewrite 2!prob_bindDl; congr (_ <| _ |> _).
  rewrite 2!bindretf ifF //; apply/negbTE/H; by rewrite mem_head.
by rewrite IH // => a ta; rewrite H // in_cons ta orbT.
Qed.

Section monty.

Variable door : finType.
Hypothesis card_door : #|door| = 3%nat.

Let A := Set3.a card_door.
Let B := Set3.b card_door.
Let C := Set3.c card_door.
Let doors := enum door.

(* TODO *)
Lemma head_filter def h p : forall x, x \in [:: h; p] -> head def (doors \\ [:: h; p]) != x.
Proof.
move=> x xhp.
have : x \notin doors \\ [:: h; p] by rewrite mem_filter xhp.
apply: contra => /eqP {1}<-; rewrite -nth0.
rewrite mem_nth // lt0n size_eq0 -has_filter; apply/hasP.
exists (Set3.another card_door h p); first by rewrite /doors mem_enum.
by rewrite Set3.another_notin.
Qed.

(* TODO *)
Lemma filter_pred1 h : doors \\ [:: h] != [::].
Proof.
rewrite -has_filter; apply/hasP.
exists (Set3.another card_door h h); first by rewrite mem_enum.
move: (Set3.another_notin card_door h h); apply: contra; by rewrite !inE => ->.
Qed.

Definition monty {M : monad} (hide : M door) (pick : M door) (tease : door -> door -> M door)
  (strategy : door -> door -> M door) : M bool :=
  do h <- hide ;
  do p <- pick ;
  do t <- tease h p ;
  do s <- strategy p t ;
  Ret (s == h).

Section monty_proba.

Let def := A.
Variable M : probMonad.
Let unif_door M := @uniform M _ def.
Let head := head def.
Let unif_pair := @uniform M _ (def, def).

Definition hide {N : probMonad} : N door := unif_door N doors.

Definition pick {N : probMonad} : N door := @uniform N _ def doors.

Definition tease (h p : door) : M door := unif_door M (doors \\ [:: h ; p]).

Definition switch {N : monad} (p t : door) : N door := Ret (head (doors \\ [:: p ; t])).

Definition stick {N : monad} (p t : door) : N door := Ret p.

Definition play (strategy : door -> door -> M door) : M bool :=
  monty hide pick tease strategy.

Lemma play_strategy strategy : play strategy =
  do hp <- unif_pair (cp doors doors) ;
  let h := hp.1 in let p := hp.2 in
  do t <- tease h p ;
  do s <- strategy p t;
  Ret (s == h).
Proof.
rewrite /unif_pair -pair_uniform; last 2 first.
  by rewrite /doors Set3.enumE.
  by rewrite /doors Set3.enumE.
rewrite /play /monty /pair bindA; bind_ext => x.
rewrite bindA.
by rewrite_ bindretf.
Qed.

Lemma uniform_doors_unfold (P : rel door) :
  do hp <- uniform (def, def) (cp doors doors); Ret (P hp.1 hp.2) =
  Ret (P A A) <|[Pr of / 9]|> (Ret (P A B) <|[Pr of / 8]|> (Ret (P A C) <|[Pr of / 7]|>
 (Ret (P B A) <|[Pr of / 6]|> (Ret (P B B) <|[Pr of / 5]|> (Ret (P B C) <|[Pr of / 4]|>
 (Ret (P C A) <|[Pr of / 3]|> (Ret (P C B) <|[Pr of / 2]|> Ret (P C C)))))))) :> M _.
Proof.
transitivity (fmap (uncurry (fun a b => P a b))
                   (@uniform M _ (def, def) (cp doors doors))).
  rewrite /fmap; bind_ext; by case.
transitivity ((fmap (uncurry (fun a b => P a b)) \o (@uniform M _ (def, def)))
              (cp doors doors)); first by [].
rewrite -(@uniform_naturality _ _ _ _ true); last by rewrite /doors Set3.enumE.
by rewrite /doors Set3.enumE /=.
Qed.

(* matching choices: the doors h and p independently chosen at random will match one third of the time *)
Lemma bcoin13E (f : bool -> M bool) :
  do hp <- uniform (def, def) (cp doors doors); f (hp.1 == hp.2) =
  do b <- bcoin [Pr of /3]; f b.
Proof.
transitivity (do hp <- uniform (def, def) (cp doors doors); Ret (hp.1 == hp.2) >>= f).
  bind_ext => -[h p] /=; by rewrite bindretf.
rewrite -bindA uniform_doors_unfold !eqxx.
rewrite (negbTE (Set3.a_neq_c card_door)).
rewrite (eq_sym B) (negbTE (Set3.a_neq_b card_door)).
rewrite (negbTE (Set3.b_neq_c card_door)).
rewrite 2!(eq_sym C) (negbTE (Set3.a_neq_c card_door)).
rewrite (negbTE (Set3.b_neq_c card_door)).
by rewrite choiceA_compute /= -uFFTE.
Qed.

Lemma bcoin23E :
  do hp <- uniform (def, def) (cp doors doors); Ret (hp.1 != hp.2) = bcoin (@Prob.mk (2/3) H23) :> M _.
Proof.
pose P := fun a b : door => a != b.
transitivity
  (do hp <- uniform (def, def) (cp doors doors); Ret (P hp.1 hp.2) : M _).
  by bind_ext.
rewrite uniform_doors_unfold {}/P !eqxx.
rewrite (negbTE (Set3.a_neq_c card_door)).
rewrite (eq_sym B) (negbTE (Set3.a_neq_b card_door)).
rewrite (negbTE (Set3.b_neq_c card_door)).
rewrite 2!(eq_sym C) (negbTE (Set3.a_neq_c card_door)).
rewrite (negbTE (Set3.b_neq_c card_door)).
by rewrite choiceA_compute /= -uTTFE.
Qed.

Lemma hide_pickE {D} (f : door -> door -> M D) :
  do h <- hide ; do p <- pick ; f h p =
  do hp <- uniform (def, def) (cp doors doors) ; f hp.1 hp.2.
Proof.
transitivity (do hp <- pair (hide, pick); f hp.1 hp.2).
  rewrite bindA; bind_ext => x.
  rewrite bindA; by rewrite_ bindretf.
by rewrite pair_uniform // /doors Set3.enumE.
Qed.

Lemma play_stick : play stick = bcoin [Pr of /3].
Proof.
rewrite {1}/play {1}/monty hide_pickE.
transitivity (do hp <- uniform (def, def) (cp doors doors) ;
                  let h := hp.1 in let p := hp.2 in
                  do t <- tease h p ; Ret (p == h)).
  bind_ext => x /=.
  by rewrite_ bindretf.
transitivity (do hp <- @uniform M _ (def, def) (cp doors doors) ;
              let h := hp.1 in let p := hp.2 in
              Ret (h == p)).
  (* t unused and uniform side effect-free, so tease can be eliminated *)
  bind_ext => -[x1 x2] /=.
  by rewrite /tease /unif_door uniform_inde eq_sym.
by rewrite bcoin13E bindmret.
Qed.

Lemma play_switch : play switch = bcoin (@Prob.mk (2/3) H23).
Proof.
rewrite {1}/play {1}/monty hide_pickE.
transitivity (do hp <- uniform (def, def) (cp doors doors);
  do t <- tease hp.1 hp.2; do s <- Ret (head (doors \\ [:: hp.2; t])); Ret (s == hp.1)).
  by [].
transitivity (do hp <- uniform (def, def) (cp doors doors);
  do t <- tease hp.1 hp.2; Ret ((head (doors \\ [:: hp.2; t])) == hp.1)).
  bind_ext => -[h p].
  rewrite [_.1]/= [_.2]/=; by rewrite_ bindretf.
transitivity (do hp <- uniform (def, def) (cp doors doors);
  if hp.1 == hp.2 then Ret false else Ret true : M _).
  bind_ext => -[h p].
  rewrite [_.1]/= [_.2]/=.
  case: ifPn => [/eqP|] hp.
    rewrite -{2}hp.
    With (rewrite (_ : _ == _ = false)) Open (X in _ >>= X).
      apply/negbTE/head_filter; by rewrite inE eqxx.
    reflexivity.
    by rewrite /tease /unif_door uniform_inde.
  rewrite /tease /unif_door.
  (* TODO: could be cleaner *)
  rewrite Set3.filter_another //.
  rewrite uniform_singl // -/(head _).
  rewrite bindretf.
  rewrite (_ : head _ = h) ?eqxx //.
  rewrite Set3.filter_another /=; last first.
    move: (Set3.another_notin card_door h p).
    rewrite !inE negb_or => /andP[_]; by rewrite eq_sym.
  by rewrite Set3.another_another.
transitivity (do hp <- uniform (def, def) (cp doors doors);
  Ret (hp.1 != hp.2) : M _).
  bind_ext => -[h p]; by case: ifPn.
exact: bcoin23E.
Qed.

End monty_proba.

Section monty_nondeter.

Variable M : altProbMonad.

Definition hide_n : M door := arbitrary A doors.
Definition tease_n (h p : door) : M door := arbitrary A (doors \\ [:: h; p]).
Let pick : M door := @pick _.
Definition play_n (strategy : door -> door -> M door) : M bool :=
  monty hide_n pick tease_n strategy.

Lemma monty_choice_your_choice_combine :
  do h <- hide_n ; do p <- pick; Ret (h, p) =
  (do p <- pick; Ret (A, p)) [~i]
  (do p <- pick; Ret (B, p)) [~i]
  (do p <- pick; Ret (C, p)).
Proof.
pose k (h : door) := do p <- pick; Ret (h, p).
transitivity (do h <- hide_n; k h).
  by [].
transitivity (do h <- (Ret A [~i] Ret B [~i] Ret C); k h).
  rewrite /hide_n.
  rewrite /doors Set3.enumE /arbitrary /foldr1 [in LHS]/=.
  by rewrite -[in RHS]altA [in RHS]altC -[in RHS]altA.
by rewrite 2!alt_bindDl 3!bindretf {}/k.
Qed.

Let try (d : door) := do p <- pick; Ret (d, p).

Lemma try_uFFT d : fmap (uncurry (fun a b => a == b)) (try d) = uFFT.
Proof.
rewrite /fmap /try bindA.
rewrite_ bindretf.
rewrite /pick /monty.pick.
transitivity (do p <- Ret A <| [Pr of /3] |> (Ret B <| [Pr of /2] |> Ret C); Ret (d == p) : M _).
  (* TODO: bind_ext? *)
  congr Monad.bind => //.
  by rewrite /doors Set3.enumE 2!uniform_cons.
rewrite 2!prob_bindDl 3!bindretf.
rewrite /uFFT 2!uniform_cons.
rewrite uniform_singl // [head _ _]/=.
have : d \in doors by rewrite mem_enum.
rewrite /doors Set3.enumE !inE => /or3P[] /eqP ->.
- rewrite eqxx (negbTE (Set3.a_neq_b _)) (negbTE (Set3.a_neq_c _)).
  rewrite choiceC.
  erewrite choiceA.
    reflexivity.
  by rewrite /=; split; field.
- rewrite eq_sym (negbTE (Set3.a_neq_b _)) eqxx (negbTE (Set3.b_neq_c _)).
  congr (_ <| _ |> _).
  rewrite choiceC.
  rewrite (@choice_ext [Pr of /2]) //=; by field.
by rewrite eq_sym (negbTE (Set3.a_neq_c _)) eq_sym (negbTE (Set3.b_neq_c _)) eqxx.
Qed.

Lemma hide_pick_nondeter : do h <- hide_n; do p <- pick; Ret (h == p) = uFFT.
Proof.
transitivity (fmap (uncurry (fun a b => a == b)) (do h <- hide_n; do p <- pick; Ret (h, p))).
  rewrite /fmap !bindA; bind_ext => y1.
  rewrite !bindA; by rewrite_ bindretf.
rewrite monty_choice_your_choice_combine -!/(try _).
rewrite 2!naturality_nondeter.
rewrite !try_uFFT.
by rewrite 2!altmm.
Qed.

End monty_nondeter.

Section forgetful_monty.

Variable M : exceptProbMonad.
Let def := A.
Let unif_door : _ -> M _ := @uniform _ _ def.

Definition tease_f (h p : door) : M door :=
  do t <- unif_door (doors \\ [:: p]); if t == h then Fail else Ret t.

Definition play_f (strategy : door -> door -> M door) : M bool :=
  monty hide pick tease_f strategy.

Lemma tease_fE (h p : door) : let d := head def (doors \\ [:: h; p]) in
  tease_f h p = if h == p then unif_door (doors \\ [:: h])
                          else (Fail : M _) <| [Pr of /2] |> Ret d.
Proof.
move=> d.
case: ifPn => [/eqP <-|hp].
  rewrite /tease_f.
  transitivity (do t <- unif_door (doors \\ [:: h]); Ret t).
    rewrite /unif_door uniform_notin //.
    exact: filter_pred1.
    move=> ?; by rewrite mem_filter inE => /andP[].
  by rewrite bindmret.
have Hd : d = Set3.another card_door h p by rewrite {}/d Set3.filter_another.
rewrite /tease_f.
transitivity (do t <- unif_door [:: h; d]; if t == h then Fail else Ret t).
  have hd : h != d.
    rewrite Hd.
    apply: contra (Set3.another_notin card_door h p) => /eqP <-.
    by rewrite inE eqxx.
  move: (Set3.filter1_another card_door hp); rewrite -/doors -Hd => -[] -> //.
  by rewrite /unif_door uniform2.
rewrite /unif_door uniform_cons.
rewrite (_ : [Pr of _] = [Pr of /2])%R; last first.
  apply prob_ext; by rewrite /=; field.
rewrite uniform_singl // [head _ _]/=.
rewrite prob_bindDl 2!bindretf eqxx ifF //.
apply/negbTE/head_filter; by rewrite inE eqxx.
Qed.

Lemma monty_f_stick :
  play_f (@stick _) =
    Ret true <| [Pr of /3] |> ((Fail : M _) <| [Pr of /2] |> Ret false).
Proof.
rewrite /play_f /monty hide_pickE.
rewrite /stick.
rewrite_ bindretf.
rewrite_ tease_fE.
rewrite_ lift_if.
rewrite_ if_ext.
rewrite_ uniform_inde.
Open (X in _ >>= X).
  transitivity (if x.1 == x.2
    then Ret true
    else do _ <- (Fail : M _) <| [Pr of /2] |> Ret (head def (doors \\ [:: x.1; x.2])); Ret false).
    case: ifPn => [/eqP <-|hp]; first by rewrite eqxx.
    by rewrite eq_sym (negbTE hp).
  reflexivity.
rewrite_ prob_bindDl.
rewrite_ (@bindfailf M). (* TODO *)
rewrite_ bindretf.
rewrite (bcoin13E (fun b => if b then Ret true else (Fail : M _) <| [Pr of / 2] |> Ret false)).
rewrite /bcoin.
by rewrite prob_bindDl 2!bindretf.
(* TODO: flattening choices *)
Qed.

Lemma monty_f_switch :
  play_f (@switch M) =
    Ret false <| [Pr of /3] |> ((Fail : M _) <| [Pr of /2] |> Ret true).
Proof.
rewrite /play_f /monty hide_pickE /switch.
Open (X in _ >>= X).
  rewrite_ bindretf.
  reflexivity.
rewrite_ tease_fE.
rewrite_ lift_if.
rewrite_ if_ext.
Open (X in _ >>= X).
transitivity (if x.1 == x.2
  then do x0 <- unif_door (doors \\ [:: x.1]); Ret false
  else
   do x0 <- (Fail : M _) <| [Pr of / 2] |> Ret (head def (doors \\ [:: x.1; x.2]));
   Ret (head A (doors \\ [:: x.2; x0]) == x.1)).
  case: x => h p; rewrite [_.1]/= [_.2]/=; case: ifPn => // /eqP <-.
  transitivity (do x0 <- unif_door (doors \\ [:: h]); if (head A (doors \\ [:: h; x0]) == h) then Ret true else Ret false).
    bind_ext => x; by case: ifPn.
  rewrite {1}/unif_door uniform_notin //.
  exact: filter_pred1.
  move=> x; rewrite mem_filter inE=> _; by rewrite head_filter // inE eqxx.
  reflexivity.
transitivity (do x <- uniform (A, A) (cp doors doors);
  if x.1 == x.2
  then Ret false
  else
   (Fail : M _)
   <| [Pr of / 2] |>
   Ret (head A (doors \\ [:: x.2; head def (doors \\ [:: x.1; x.2])]) == x.1)).
  bind_ext => -[h p]; rewrite [_.1]/= [_.2]/=.
  case: ifPn => [?| hp]; first by rewrite uniform_inde.
  by rewrite prob_bindDl (@bindfailf M) bindretf.
transitivity (
  do x <- uniform (A, A) (cp doors doors);
  if x.1 == x.2
  then Ret false
  else (Fail : M _) <| [Pr of / 2] |> Ret true).
  bind_ext => -[h p]; rewrite [_.1]/= [_.2]/=.
  case: ifPn => // hp; congr (_ <| _ |> Ret _).
  apply/eqP.
  rewrite (_ : _ \\ _ = [:: h]) //.
  rewrite Set3.filter_another; last by rewrite eq_sym head_filter // !inE eqxx orbT.
  by rewrite Set3.filter_another //= Set3.another_another.
rewrite (bcoin13E (fun b => if b then Ret false else (Fail : M _) <| [Pr of / 2] |> Ret true)).
by rewrite prob_bindDl 2!bindretf.
(* TODO: flattening choices *)
Qed.

End forgetful_monty.

End monty.
