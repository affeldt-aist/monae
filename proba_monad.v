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
*)

Reserved Notation "'`Pr' p " (format "`Pr  p", at level 6).
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
  Op1 : (0 <= p <= 1)%R }.
Definition O1 (p : t) := Op1 p.
Arguments O1 : simpl never.
Module Exports.
Notation prob := t.
Notation "'`Pr' q" := (@mk q (@O1 _)).
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
Canonical probcplt (p : prob) := @Prob.mk p.~ (onem_prob (Prob.O1 p)).

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
  choice : forall (p : prob) A, M A -> M A -> M A
           where "mx <| p |> my" := (choice p mx my) ;
  (* identity laws *)
  _ : forall A (mx my : M A), mx <| `Pr 0 |> my = my ;
  _ : forall A (mx my : M A), mx <| `Pr 1 |> my = mx ;
  (* skewed commutativity law *)
  _ : forall A p (mx my : M A), mx <| p |> my = my <| `Pr p.~ |> mx ;
  _ : forall A p, idempotent (@choice p A) ;
  (* quasi associativity *)
  _ : forall A (p q r s : prob) (mx my mz : M A),
    (p = r * s :> R /\ s.~ = p.~ * q.~)%R ->
    mx <| p |> (my <| q |> mz) = (mx <| r |> my) <| s |> mz ;
  (* composition distributes leftwards over [probabilistic] choice *)
  _ : forall p, Laws.bind_left_distributive (@Bind M) (choice p)
}.
Record class_of (m : Type -> Type) := Class {
  base : Monad.class_of m ; mixin : mixin_of (Monad.Pack base) }.
Structure t := Pack { m : Type -> Type ; class : class_of m }.
Definition baseType (M : t) := Monad.Pack (MonadProb.base (class M)).
Module Exports.
Definition Choice (M : t) : forall p A, m M A -> m M A -> m M A :=
  let: Pack _ (Class _ (Mixin x _ _ _ _ _ _ )) := M return
    forall p A, m M A -> m M A -> m M A in x.
Arguments Choice {M} : simpl never.
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
Lemma choice0 : forall A (mx my : M A), mx <| `Pr 0 |> my = my.
Proof. by case: M => m [? []]. Qed.
Lemma choice1 : forall A (mx my : M A), mx <| `Pr 1 |> my = mx.
Proof. by case: M => m [? []]. Qed.
Lemma choiceA A : forall (p q r s : prob) (mx my mz : M A),
    (p = r * s :> R /\ s.~ = p.~ * q.~)%R ->
    mx <| p |> (my <| q |> mz) = (mx <| r |> my) <| s |> mz.
Proof. by case: M A => m [? []]. Qed.
Lemma choiceC : forall A (p : prob) (mx my : M A), mx <| p |> my = my <| `Pr p.~ |> mx.
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
    | x :: xs => Ret x <| `Pr / IZR (Z_of_nat (size (x :: xs))) |> uniform def xs
  end.

Lemma uniform_nil (M : probMonad) A (def : A) :
  uniform def [::] = Ret def :> M A.
Proof. by []. Qed.

Lemma prob_ext (p q : prob) : Prob.p p = Prob.p q -> p = q.
Proof.
move: p q => [p Hp] [q Hq] /= ?; subst q; f_equal; exact: proof_irrelevance.
Qed.

Lemma choice_ext (q p : prob) (M : probMonad) A (m1 m2 : M A) :
  p = q :> R -> m1 <| p |> m2 = m1 <| q |> m2.
Proof. by move/prob_ext => ->. Qed.

Lemma uniform_cons (M : probMonad) A (def : A) h s :
  uniform def (h :: s) = Ret h <| `Pr / IZR (Z_of_nat (size (h :: s))) |> uniform def s :> M A.
Proof.
case: s => //.
rewrite (@choice_ext (`Pr 1)) // ?choice1 //.
by rewrite /= Rinv_1.
Qed.

Lemma uniform_singl (M : probMonad) A (def : A) h : size h = 1%nat ->
  uniform def h = Ret (head def h) :> M A.
Proof.
case: h => // h [|//] _.
rewrite uniform_cons uniform_nil (@choice_ext (`Pr 1)) ?choice1 //.
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
  uniform a (s ++ t) = uniform a s <| `Pr (INR m / INR (m + n)) |> uniform a t :> M _.
Proof.
elim: s t => [t m n|s1 s2 IH t m n].
  rewrite cat0s uniform_nil /= [X in _ <| X |> _](_ : _ = `Pr 0) ?choice0 //.
  by apply prob_ext => /=; rewrite /Rdiv Rmult_0_l.
case/boolP : (m.-1 + n == 0)%nat => [{IH}|] m1n0.
  have s20 : s2 = [::] by move: m1n0; rewrite {}/m /=; case: s2.
  have t0 : t = [::] by move: m1n0; rewrite {}/n /= addnC; case: t.
  subst s2 t.
  rewrite cats0 (_ : Prob.mk _ = `Pr 1) ?choice1 //.
  by apply prob_ext => /=; rewrite /Rdiv Rmult_1_l Rinv_1.
rewrite cat_cons uniform_cons uniform_cons.
set pv := ((/ _)%R).
set v : prob := @Prob.mk pv _.
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
elim=> // x [_ _|x' xs]; first by rewrite /= fmap_def bindretf.
move/(_ isT) => IH _.
rewrite [uniform a]lock [uniform b]lock /= -2!lock.
rewrite [in LHS]uniform_cons [in RHS]uniform_cons.
set p := (@Prob.mk (/ IZR (Z.of_nat (size _)))%R _ in X in _ = X).
rewrite (_ : @Prob.mk (/ _)%R _ = p); last first.
  by apply prob_ext => /=; rewrite size_map.
move: IH; rewrite 2!compE => ->.
rewrite [in RHS]fmap_def prob_bindDl bindretf fmap_def.
by congr Choice.
Qed.
Arguments uniform_naturality {M A B}.

Lemma mpair_uniform_base_case (M : probMonad) A a x (y : seq A) :
  (0 < size y)%nat ->
  uniform (a, a) (cp [:: x] y) = mpair (uniform a [:: x], uniform a y) :> M _.
Proof.
move=> y0; rewrite cp1.
transitivity (do y' <- @uniform M _ a y; Ret (x, y')).
  by rewrite -(compE (uniform _)) (uniform_naturality a) // compE fmap_def.
transitivity (do z <- Ret x; do y' <- uniform a y; Ret (z, y') : M _).
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
move: (@mpair_uniform_base_case M _ a x _ size_y).
rewrite {1}[cp _ _]/= cats0 => ->.
rewrite -prob_bindDl.
rewrite [in RHS]/mpair uniform_cat.
rewrite [in RHS](_ : Prob.mk _ = probinvn m) //.
by apply prob_ext => /=; rewrite /Rdiv Rmult_1_l.
Qed.

Module MonadAltProb.
Record mixin_of (M : altCIMonad) (a : prob -> forall A, M A -> M A -> M A) := Mixin {
  _ : forall A (p : prob),
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

(* arbitrary nondeterministic choice between booleans *)
Definition arb {M : altMonad} : M bool := Ret true [~] Ret false.

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
  arbcoin p = (bcoin p : M _) [~] bcoin (`Pr p.~).
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
  (bcoin w : M _) [~] Ret false [~] Ret true [~] bcoin (`Pr w.~).
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
  Ret true <| `Pr / 2 |> (Ret false <| `Pr / 2 |> (Fail : M _)).

Lemma H23 : (0 <= 2/3 <= 1)%R. Proof. split; lra. Qed.

(* NB: notation for ltac:(split; fourier?)*)
Lemma choiceA_compute {N : probMonad} (T F : bool) (f : bool -> N bool) :
  f T <|`Pr / 9|> (f F <|`Pr / 8|> (f F <|`Pr / 7|> (f F <|`Pr / 6|>
 (f T <|`Pr / 5|> (f F <|`Pr / 4|> (f F <|`Pr / 3|> (f F <|`Pr / 2|>
  f T))))))) = f F <|`Pr / 3|> (f F <|`Pr / 2|> f T) :> N _.
Proof.
have H34 : (0 <= 3/4 <= 1)%R by split; lra.
have H27 : (0 <= 2/7 <= 1)%R by split; lra.
have H721 : (0 <= 7/21 <= 1)%R by split; lra.
have H2156 : (0 <= 21/56 <= 1)%R by split; lra.
have H25 : (0 <= 2/5 <= 1)%R by split; lra.
rewrite [in RHS](choiceA _ _ (`Pr /2) (@Prob.mk (2/3) H23)); last by rewrite 3!probpK; split; field.
rewrite choicemm.
rewrite [in LHS](choiceA (`Pr /3) (`Pr /2) (`Pr /2) (@Prob.mk (2/3) H23)); last by rewrite 3!probpK; split; field.
rewrite choicemm.
rewrite [in LHS](choiceA (`Pr /4) (@Prob.mk (2/3) H23) (`Pr /3) (@Prob.mk (3/4) H34)); last by rewrite 4!probpK; split; field.
rewrite choicemm.
rewrite [in LHS](choiceA (`Pr /7) (`Pr /6) (`Pr /2) (@Prob.mk (2/7) H27)); last by rewrite 4!probpK; split; field.
rewrite choicemm.
rewrite [in LHS](choiceA (`Pr /8) (@Prob.mk (2/7) H27) (@Prob.mk (7/21) H721) (@Prob.mk (21/56) H2156)); last by rewrite 4!probpK; split; field.
rewrite (choiceC (@Prob.mk (3/4) H34)).
rewrite [in LHS](choiceA (`Pr /5) (probcplt (@Prob.mk (3/4) H34)) (`Pr /2) (@Prob.mk (2/5) H25)); last by rewrite 3!probpK /=; split; field.
rewrite choicemm.
rewrite choicemm.
rewrite (choiceC (@Prob.mk (2/5) H25)).
rewrite [in LHS](choiceA (@Prob.mk (21/56) H2156) (probcplt (Prob.mk H25)) (`Pr /2) (Prob.mk H34)); last by rewrite 3!probpK /=; split; field.
rewrite choicemm.
rewrite (choiceC (Prob.mk H34)).
rewrite [in LHS](choiceA (`Pr /9) (probcplt (Prob.mk H34)) (`Pr /3) (`Pr /3)); last by rewrite 3!probpK /=; split; field.
rewrite choicemm choiceC.
rewrite (@choice_ext (Prob.mk H23)) //=; by field.
Qed.

Definition uFFT {M : probMonad} : M bool :=
  uniform true [:: false; false; true].

Lemma uFFTE (M : probMonad) : uFFT = bcoin (`Pr /3) :> M _.
Proof.
rewrite /uFFT /bcoin uniform_cons.
rewrite (_ : `Pr _ = `Pr /3)%R; last exact/prob_ext.
rewrite uniform_cons.
rewrite [in X in _ <| _ |> X](_ : `Pr _ = `Pr /2)%R; last first.
  exact/prob_ext.
rewrite uniform_singl //=.
rewrite (choiceA _ _ (`Pr /2) (Prob.mk H23)); last first.
  rewrite /=; split; field.
rewrite choicemm choiceC.
rewrite (_ : (`Pr / 3)%R = probcplt (Prob.mk H23)) //.
apply prob_ext => /=; field.
Qed.

Definition uTTF {M : probMonad} : M bool :=
  uniform true [:: true; true; false].

Lemma uTTFE (M : probMonad) : uTTF = bcoin (@Prob.mk (2/3) H23) :> M _.
Proof.
rewrite /uTTF /bcoin uniform_cons.
rewrite (_ : `Pr _ = `Pr /3)%R; last exact: prob_ext.
rewrite uniform_cons.
rewrite [in X in _ <| _ |> X](_ : `Pr _ = `Pr /2)%R; last exact/prob_ext.
rewrite uniform_singl //=.
rewrite (choiceA _ _ (`Pr /2) (Prob.mk H23)); last first.
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
  rewrite (_ : `Pr _ = `Pr 1); last by apply prob_ext => /=; rewrite Rinv_1.
  rewrite choice1.
  rewrite 2!bindretf ifF //; apply/negbTE/H; by rewrite mem_head.
rewrite 2!prob_bindDl; congr (_ <| _ |> _).
  rewrite 2!bindretf ifF //; apply/negbTE/H; by rewrite mem_head.
by rewrite IH // => a ta; rewrite H // in_cons ta orbT.
Qed.
