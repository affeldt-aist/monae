From mathcomp Require Import all_ssreflect.
Require Import imonae_lib ihierarchy imonad_lib ifail_lib istate_lib imonad_model.

(******************************************************************************)
(*                    Formalization of monad transformers                     *)
(*                                                                            *)
(* This file corresponds to the formalization of [Mauro Jaskelioff,           *)
(* Modular Monad Transformers, ESOP 2009] (up to Sect. 5, Example 22). Up to  *)
(* Sect. 4, it is documented in [Célestine Sauvage, Reynald Affeldt, David    *)
(* Nowak, Vers la formalisation en Coq des transformateurs de monades         *)
(* modulaires, JFLA 2020]. From functorial monad transformers, this is work   *)
(* in progress.                                                               *)
(*                                                                            *)
(*             monadM == monad morphism                                       *)
(*             monadT == monad transformer                                    *)
(*   E .-aoperation M == algebraic E.-operation M                             *)
(*                FMT == functorial monad transformer                         *)
(*                                                                            *)
(******************************************************************************)

(* - Module monadM
     monad morphism
   - Module monadT.
     monad transformer
   - examples of monad transformers
     - state monad transformer
     - exception monad transformer
     - continuation monad transformer
       continuation_monad_transformer_examples
   - Section instantiations_with_the_identity_monad
   - Section calcul.
     example using the model of callcc
   - Module Lifting
     Definition 14
   - Module AOperation
     Definition 15
   - Section proposition17.
   - Section theorem19.
     algebraic lifting
   - Section examples_of_lifting.
   - Section examples_of_programs.
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.

Reserved Notation "E .-aoperation M" (at level 2, format "E  .-aoperation  M").

Import Univ.

Module MonadMLaws.
Section monadmlaws.
Variables (M N : monad).
Definition ret (e : M ~~> N) := forall A : UU0, e A \o Ret = Ret.
Definition bind (e : M ~~> N) := forall (A B : UU0) (m : M A) (f : A -> M B),
    e B (m >>= f) = e A m >>= (e B \o f).
End monadmlaws.
End MonadMLaws.

Module monadM.
Section monadm.
Variables (M N : monad).
Record mixin_of (e : M ~~> N) := Mixin
  {_ : MonadMLaws.ret e ; _ : MonadMLaws.bind e }.
Structure t := Pack { e : M ~~> N ; class : mixin_of e }.
End monadm.
Module Exports.
Notation monadM := t.
Coercion e : monadM >-> Funclass.
End Exports.
End monadM.
Export monadM.Exports.

Section monadM_interface.
Variables (M N : monad) (f : monadM M N).
Lemma monadMret A : f A \o Ret = Ret.
Proof. by case: f => ? []. Qed.
Lemma monadMbind A B (m : M A) (h : A -> M B) :
  f _ (m >>= h) = f _ m >>= (f _ \o h).
Proof. by case: f => ? []. Qed.
End monadM_interface.

Section monadM_lemmas.
Variables (M N : monad) (e : monadM M N).
Lemma natural_monadM : naturality M N e.
Proof.
move=> A B h; apply fun_ext => m /=.
by rewrite !fmapE monadMbind compA monadMret.
Qed.
End monadM_lemmas.

Canonical monadM_nt (M N : monad) (e : monadM M N) : M ~> N :=
  Natural.Pack (Natural.Mixin (natural_monadM e)).

Module MonadT.
Record mixin_of (T : monad -> monad) := Mixin {
  liftT : forall M : monad, monadM M (T M) }.
Record t := Pack {m : monad -> monad ; class : mixin_of m}.
Module Exports.
Notation monadT := t.
Coercion m : monadT >-> Funclass.
Definition Lift (T : t) : forall M : monad, monadM M (m T M) :=
  let: Pack _ (Mixin f) := T return forall M : monad, monadM M (m T M) in f.
Arguments Lift _ _ : simpl never.
End Exports.
End MonadT.
Export MonadT.Exports.

Section state_monad_transformer.

Local Obligation Tactic := idtac.

Variables (S : UU0) (M : monad).

Definition MS := fun A : UU0 => S -> M (A * S)%type.

Definition retS (A : UU0) : A -> MS A := curry Ret.

Definition bindS A B (m : MS A) f : MS B := fun s => m s >>= uncurry f.

Definition MS_fmap (A B : UU0) (f : A -> B) (m : MS A) : MS B :=
  (M # (fun x => (f x.1, x.2))) \o m.

Lemma MS_id : FunctorLaws.id MS_fmap.
Proof.
move=> A; apply fun_ext => m.
rewrite /MS_fmap; apply fun_ext => s.
rewrite (_ : (fun x : A * S => _) = id) ?functor_id //.
by apply fun_ext; case.
Qed.

Lemma MS_comp : FunctorLaws.comp MS_fmap.
Proof.
move=> A B C g h; rewrite /MS_fmap; apply fun_ext => m.
by apply fun_ext => s /=; rewrite -[RHS]compE -functor_o.
Qed.

Definition MS_functor := Functor.Pack (Functor.Mixin MS_id MS_comp).

Lemma naturality_retS : naturality FId MS_functor retS.
Proof.
move=> A B h; rewrite /Actm /=; apply fun_ext => a /=.
rewrite /MS_fmap /=; apply fun_ext => s /=.
by rewrite /retS [in LHS]curryE (natural RET).
Qed.

Definition retS_natural : FId ~> MS_functor :=
  Natural.Pack (Natural.Mixin naturality_retS).

Program Definition estateMonadM : monad :=
  @Monad_of_ret_bind MS_functor retS_natural bindS _ _ _.
Next Obligation.
by move=> A B a f; rewrite /bindS; apply fun_ext => s; rewrite bindretf.
Defined.
Next Obligation.
move=> A m; rewrite /bindS; apply fun_ext => s.
rewrite -[in RHS](bindmret (m s)); by bind_ext; case.
Defined.
Next Obligation.
move=> A B C m f g; rewrite /bindS; apply fun_ext => s.
by rewrite bindA; bind_ext; case.
Defined.

Definition liftS A (m : M A) : estateMonadM A :=
  fun s => m >>= (fun x => Ret (x, s)).

Program Definition stateMonadM : monadM M estateMonadM :=
  locked (monadM.Pack (@monadM.Mixin _ _ liftS _ _)).
Next Obligation.
move=> A.
rewrite /liftS; apply fun_ext => a /=; apply fun_ext => s /=.
by rewrite bindretf.
Qed.
Next Obligation.
move=> A B m f; rewrite /liftS; apply fun_ext => s.
rewrite [in RHS]/Bind [in RHS]/Join /= /Monad_of_ret_bind.join /= /bindS !bindA.
bind_ext => a; by rewrite !bindretf.
Qed.

End state_monad_transformer.

Definition stateT S : monadT := MonadT.Pack (MonadT.Mixin (@stateMonadM S)).

Section exception_monad_transformer.

Local Obligation Tactic := idtac.

Variables (Z : UU0) (* the type of exceptions *) (M : monad).

Definition MX := fun X : UU0 => M (Z + X)%type.

Definition retX X x : MX X := Ret (inr x).

Definition bindX X Y (t : MX X) (f : X -> MX Y) : MX Y :=
  t >>= fun c => match c with inl z => Ret (inl z) | inr x => f x end.

Local Open Scope mprog.
Definition MX_map (A B : UU0) (f : A -> B) : MX A -> MX B :=
  M # (fun x => match x with inl y => inl y | inr y => inr (f y) end).
Local Close Scope mprog.

Lemma MX_map_i : FunctorLaws.id MX_map.
Proof.
move=> A; apply fun_ext => x.
rewrite /MX in x *.
by rewrite /MX_map (_ : (fun _ => _) = id) ?functor_id //; apply fun_ext; case.
Qed.

Lemma MX_map_o : FunctorLaws.comp MX_map.
Proof.
rewrite /MX_map => A B C g h /=.
apply fun_ext => x /=.
rewrite -[RHS]compE -functor_o /=; congr (_ # _).
by apply fun_ext; case.
Qed.

Definition exceptionT_functor := Functor.Pack (Functor.Mixin MX_map_i MX_map_o).

Lemma naturality_retX : naturality FId exceptionT_functor retX.
Proof.
move=> A B h; rewrite /retX; apply fun_ext => /= a.
by rewrite /Actm /= /MX_map -[LHS]compE (natural RET).
Qed.

Definition retX_nat : FId ~> exceptionT_functor :=
  Natural.Pack (Natural.Mixin naturality_retX).

Program Definition eexceptionMonadM : monad :=
  @Monad_of_ret_bind exceptionT_functor retX_nat bindX _ _ _.
Next Obligation. by move=> A B a f; rewrite /bindX bindretf. Qed.
Next Obligation.
move=> A m; rewrite /bindX -[in RHS](bindmret m); by bind_ext; case.
Qed.
Next Obligation.
move=> A B C m f g; rewrite /bindX bindA; bind_ext; case => //.
by move=> z; rewrite bindretf.
Qed.

Definition liftX X (m : M X) : eexceptionMonadM X :=
  m >>= (fun x => @RET eexceptionMonadM _ x).

Program Definition exceptionMonadM : monadM M eexceptionMonadM :=
  monadM.Pack (@monadM.Mixin _ _ liftX _ _).
Next Obligation.
by move=> A; apply fun_ext => a; rewrite /liftX /= bindretf.
Qed.
Next Obligation.
move=> A B m f; rewrite /liftX [in RHS]/Bind [in RHS]/Join /=.
rewrite  /Monad_of_ret_bind.join /= /bindX !bindA.
bind_ext => a; by rewrite !bindretf.
Qed.

End exception_monad_transformer.

Definition errorT Z := MonadT.Pack (MonadT.Mixin (@exceptionMonadM Z)).

Section continuation_monad_tranformer.

Local Obligation Tactic := idtac.

Variables (r : UU0) (M : monad).

Definition MC : UU0 -> UU0 := fun A => (A -> M r) -> M r %type.

Definition retC (A : UU0) (a : A) : MC A := fun k => k a.

Definition bindC A B (m : MC A) f : MC B := fun k => m (f^~ k).

Definition MC_map (A B : UU0) (f : A -> B) (m : MC A) : MC B.
move=> Br; apply m => a.
apply Br; exact: (f a).
Defined.

Definition MC_functor : functor.
apply: (Functor.Pack (@Functor.Mixin MC MC_map _ _)).
by [].
by [].
Defined.

Lemma naturality_retC : naturality FId MC_functor retC.
Proof. by []. Qed.

Definition retC_nat : FId ~> MC_functor :=
  Natural.Pack (Natural.Mixin naturality_retC).

Program Definition econtMonadM : monad :=
  @Monad_of_ret_bind MC_functor retC_nat bindC _ _ _.
Next Obligation. by []. Qed.
Next Obligation. by []. Qed.
Next Obligation. by []. Qed.

Definition liftC A (x : M A) : econtMonadM A := fun k => x >>= k.

Program Definition contMonadM : monadM M econtMonadM  :=
  monadM.Pack (@monadM.Mixin _ _ liftC  _ _).
Next Obligation.
move => A.
rewrite /liftC; apply fun_ext => a /=.
apply fun_ext => s.
by rewrite bindretf.
Qed.
Next Obligation.
move => A B m f.
rewrite /liftC; apply fun_ext => cont.
by rewrite !bindA.
Qed.

End continuation_monad_tranformer.

Definition contT r := MonadT.Pack (MonadT.Mixin (@contMonadM r)).

Definition abortT r X (M : monad) A : contT r M A := fun _ : A -> M r => Ret X.
Arguments abortT {r} _ {M} {A}.

Section continuation_monad_transformer_examples.

Fixpoint for_loop (M : monad) (it min : nat) (body : nat -> contT unit M unit) : M unit :=
  if it <= min then Ret tt
  else if it is it'.+1 then
      (body it') (fun _ => for_loop it' min body)
      else Ret tt.

Section for_loop_lemmas.
Variable M : monad.
Implicit Types body : nat  -> contT unit M unit.

Lemma loop0 i body : for_loop i i body = Ret tt.
Proof.
by case i => //= n; rewrite ltnS leqnn.
Qed.

Lemma loop1 i j body : for_loop (i.+1 + j) i body =
  (body (i + j)) (fun _ => for_loop (i + j) i body).
Proof.
rewrite /=.
by case : ifPn ; rewrite ltnNge leq_addr.
Qed.

Lemma loop2 i j body :
  body (i + j) = abortT tt -> for_loop (i + j).+1 i body = Ret tt.
Proof.
move=> Hbody /=.
case : ifPn => Hcond.
- reflexivity.
- by rewrite Hbody /= /abortT.
Qed.

End for_loop_lemmas.
(* TODO : instantiate with RunStateMonad *)

Definition foreach (M : monad) (items : list nat) (body : nat -> contT unit M unit) : M unit :=
  foldr
    (fun x next => (body x) (fun _ => next))
    (Ret tt)
    items.

(* Lemma loop3 : forall i j body, *)
(*      foreach (i + j).+1 i body = Ret tt -> body (i + j) = @abort_tt m unit. *)
(* Proof. *)
(* move => i j body /=. *)
(* case : ifPn => //; rewrite ltnNge; rewrite leq_addr. *)
(* by []. *)
(* move => _ /= Hfor. *)
(* have Hcont2 : forall cont, body (i + j) = @abort_tt m unit -> body (i + j) cont = Ret tt. *)
(*   (* split. *) *)
(*   rewrite /= /abort_tt /abort. *)
(*   by rewrite funeqE. *)
(* have Hcont1 : (forall cont, body (i + j) cont = Ret tt) -> body (i + j) = @abort_tt m unit.   *)
(*   move => Hcont. *)
(*   rewrite /= /abort_tt /abort. *)
(*   rewrite funeqE => k. *)
(*   exact: Hcont. *)
(* apply Hcont1. *)
(* move => cont. *)
(* rewrite Hcont2 //. *)

(* set bl := (fun _ : unit => foreach (i + j) i body). *)
(* (* Check (fun _ : unit => foreach (i + j) i body). *) *)
(* generalize (Hcont1 bl). *)

(* move => bl. *)
(* Qed *)

Section sum.
Variables M : stateMonad nat.

Let sum n : M unit := for_loop n O
  (fun i : nat => liftC (Get >>= (fun z => Put (z + i)) ) ).

Lemma sum_test n :
  sum n = Get >>= (fun m => Put (m + sumn (iota 0 n))).
Proof.
elim: n => [|n ih].
  rewrite /sum.
  rewrite loop0.
  rewrite (_ : sumn (iota 0 0) = 0) //.
  rewrite -[LHS]bindskipf.
  rewrite -getputskip.
  rewrite bindA.
  bind_ext => a.
  rewrite addn0.
  rewrite -[RHS]bindmret.
  bind_ext.
  by case.
rewrite /sum -add1n loop1 /liftC bindA; bind_ext => m.
rewrite -/(sum n) {}ih -bindA putget bindA bindretf putput.
congr Put.
rewrite add0n (addnC 1).
rewrite iota_add /= sumn_cat /=.
by rewrite add0n addn0 /= addnAC addnA.
Qed.

Example sum_from_0_to_10 : M unit :=
  foreach (iota 100 0) (fun i => if i > 90 then
                            abortT tt
                          else
                            liftC (Get >>= (fun z => Put (z + i)))).

End sum.

End continuation_monad_transformer_examples.

Lemma functor_ext (F G : functor) :
  forall (H : Functor.acto F = Functor.acto G),
  Functor.actm (Functor.class G) =
  eq_rect _ (fun m : UU0 -> UU0 => forall A B : UU0, (A -> B) -> m A -> m B) (Functor.actm (Functor.class F)) _ H  ->
  G = F.
Proof.
move: F G => [F [HF1 HF2 HF3]] [G [HG1 HG2 HG3]] /= H; subst G => /= ?; subst HG1.
congr (Functor.Pack (Functor.Mixin _ _)); exact/proof_irr.
Defined.

Require Import Logic.Eqdep.

Lemma natural_ext (F G G' : functor) (t : F ~> G) (t' : F ~> G') :
  forall (H : G = G'),
  forall (K : forall X (x : F X), Natural.cpnt t' x = eq_rect _ (fun m : functor => m X) (Natural.cpnt t x) _ H),
  t' = eq_rect _ (fun m => F ~> m) t _ H.
Proof.
move : t t' => [t t1] [t' t'1] /= H; subst G' => H /=.
have ? : t = t'.
  apply FunctionalExtensionality.functional_extensionality_dep => A.
  apply FunctionalExtensionality.functional_extensionality => x.
  rewrite H.
  by rewrite -[in RHS]eq_rect_eq.
subst t'.
congr Natural.Pack; exact/proof_irr.
Qed.

Lemma natural_ext2 (F F' : functor) (t : F \O F ~> F) (t' : F' \O F' ~> F') :
  forall (K : F = F'),
  forall L : (forall X (x : (F' \O F') X),
    Natural.cpnt t' x = eq_rect _ (fun m : functor => m X)
      (Natural.cpnt t (eq_rect _ (fun m : functor => (m \O m) X) x _ (esym K)))
      _ K),
  t' = eq_rect _ (fun m => m \O m ~> m) t _ K.
Proof.
move: t t' => [t t1] [t' t'1] /= H L; subst F.
rewrite -[in RHS]eq_rect_eq /=.
have ? : t = t'.
  apply FunctionalExtensionality.functional_extensionality_dep => A.
  apply FunctionalExtensionality.functional_extensionality => x.
  rewrite L.
  by rewrite -[in RHS]eq_rect_eq.
subst t'.
congr Natural.Pack; exact/proof_irr.
Qed.

Lemma monad_of_ret_bind_ext (F G : functor) (RET1 : FId ~> F) (RET2 : FId ~> G)
  (bind1 : forall A B : UU0, F A -> (A -> F B) -> F B)
  (bind2 : forall A B : UU0, G A -> (A -> G B) -> G B) :
  forall (FG : F = G),
  RET1 = eq_rect _ (fun m => FId ~> m) RET2 _ ((*beuh*) (esym FG)) ->
  bind1 = eq_rect _ (fun m : functor => forall A B : UU0, m A -> (A -> m B) -> m B) bind2 _ (esym FG) ->
  forall H1 K1 H2 K2 H3 K3,
  @Monad_of_ret_bind F RET1 bind1 H1 H2 H3 =
  @Monad_of_ret_bind G RET2 bind2 K1 K2 K3.
Proof.
move=> FG; subst G; move=> HRET; subst RET1; move=> HBIND; subst bind1 => H1 K1 H2 K2 H3 K3.
rewrite /Monad_of_ret_bind; congr Monad.Pack; simpl in *.
have <- : H1 = K1 by exact/proof_irr.
have <- : H2 = K2 by exact/proof_irr.
have <- : H3 = K3 by exact/proof_irr.
by [].
Qed.

(* result of a discussion with Maxime and Enrico on 2019-09-12 *)
Section eq_rect_ret.
Variable X : UU0.
Let U  : UU1 := functor.
Let Q : U -> UU0 := Functor.acto^~ X.

Lemma eq_rect_ret (p p' : U) (K : Q p' = Q p) (x : Q p') (h : p = p') :
  x = eq_rect p Q (eq_rect _ (fun X : UU0 => id X) x _ K) p' h.
Proof.
rewrite /eq_rect; destruct h; rewrite (_ : K = erefl) //; exact/proof_irr.
Qed.

Lemma eq_rect_state_ret S (p := ModelMonad.State.functor S : U)
  (p' := MS_functor S ModelMonad.identity : U)
  (x : Q p') (h : p = p') : x = eq_rect p Q x p' h.
Proof.
have K : Q p' = Q p by [].
rewrite {2}(_ : x = eq_rect _ (fun x : UU0 => x) x _ K) //; first exact: eq_rect_ret.
rewrite /eq_rect (_ : K = erefl) //; exact/proof_irr.
Qed.

Lemma eq_rect_error_ret (E : UU0) (p : U := ModelMonad.Except.functor E)
  (p' : U := exceptionT_functor E ModelMonad.identity)
  (x : Q p') (h : p = p') : x = eq_rect p Q x p' h.
Proof.
have K : Q p' = Q p by [].
rewrite {2}(_ : x = eq_rect _ (fun x : UU0 => x) x _ K) //; first exact: eq_rect_ret.
rewrite /eq_rect (_ : K = erefl) //; exact/proof_irr.
Qed.

Lemma eq_rect_cont_ret r (p : U := ModelMonad.Cont.functor r)
  (p' : U := MC_functor r ModelMonad.identity)
  (x : Q p') (h : p = p') : x = eq_rect p Q x p' h.
Proof.
have K : Q p' = Q p by [].
rewrite {2}(_ : x = eq_rect _ (fun x : UU0 => x) x _ K) //; first exact: eq_rect_ret.
rewrite /eq_rect (_ : K = erefl) //; exact/proof_irr.
Qed.

End eq_rect_ret.

Section eq_rect_bind.
Let U : Type := functor.
Let Q : U -> Type := fun F => forall A B, Functor.acto F A -> (A -> Functor.acto F B) -> Functor.acto F B.

Lemma eq_rect_bind (p p' : U) (K : Q p' = Q p) (x : Q p') (h : p = p') :
  x = eq_rect p Q (eq_rect _ id x _ K) p' h.
Proof.
rewrite /eq_rect; destruct h; rewrite (_ : K = erefl) //; exact/proof_irr.
Qed.

Lemma eq_rect_bind_state S (p : U := ModelMonad.State.functor S)
  (p' : U := MS_functor S ModelMonad.identity)
  (x : Q p') (h : p = p') : x = eq_rect p Q x p' h.
Proof.
have K : Q p' = Q p by [].
rewrite {2}(_ : x = eq_rect _ id x _ K); first exact: eq_rect_bind.
rewrite /eq_rect (_ : K = erefl) //; exact/proof_irr.
Qed.

Lemma eq_rect_bind_error E (p : U := ModelMonad.Except.functor E)
  (p' : U := exceptionT_functor E ModelMonad.identity)
  (x : Q p') (h : p = p') : x = eq_rect p Q x p' h.
Proof.
have K : Q p' = Q p by [].
rewrite {2}(_ : x = eq_rect _ id x _ K) //; first exact: eq_rect_bind.
rewrite /eq_rect (_ : K = erefl) //; exact/proof_irr.
Qed.

Lemma eq_rect_bind_cont S (p : U := ModelMonad.Cont.functor S)
  (p' : U := MC_functor S ModelMonad.identity)
  (x : Q p') (h : p = p') : x = eq_rect p Q x p' h.
Proof.
have K : Q p' = Q p by [].
rewrite {2}(_ : x = eq_rect _ id x _ K) //; first exact: eq_rect_bind.
rewrite /eq_rect (_ : K = erefl) //; exact/proof_irr.
Qed.

End eq_rect_bind.

Section instantiations_with_the_identity_monad.

Lemma state_monad_stateT S :
  stateT S ModelMonad.identity = ModelMonad.State.t S.
Proof.
rewrite /= /estateMonadM /ModelMonad.State.t.
have FG : MS_functor S ModelMonad.identity = ModelMonad.State.functor S.
  apply: functor_ext => /=.
  apply FunctionalExtensionality.functional_extensionality_dep => A.
  apply FunctionalExtensionality.functional_extensionality_dep => B.
  apply fun_ext => f; apply fun_ext => m; apply fun_ext => s.
  by rewrite /MS_fmap /Actm /= /ModelMonad.State.map; destruct (m s).
apply (@monad_of_ret_bind_ext _ _ _ _ _ _ FG) => /=.
  apply/natural_ext => A a /=; exact: eq_rect_state_ret _ (esym FG).
set x := @bindS _ _; exact: (@eq_rect_bind_state S x (esym FG)).
Qed.

Lemma error_monad_errorT (Z : UU0) :
  errorT Z ModelMonad.identity = ModelMonad.Except.t Z.
Proof.
rewrite /= /eexceptionMonadM /ModelMonad.Except.t.
have FG : exceptionT_functor Z ModelMonad.identity = ModelMonad.Except.functor Z.
  apply: functor_ext => /=.
  apply FunctionalExtensionality.functional_extensionality_dep => A.
  apply FunctionalExtensionality.functional_extensionality_dep => B.
  apply fun_ext => f; apply fun_ext => m.
  by rewrite /MX_map /Actm /= /ModelMonad.Except.map; destruct m.
apply (@monad_of_ret_bind_ext _ _ _ _ _ _ FG) => /=.
  apply/natural_ext => A a /=; exact: (eq_rect_error_ret _ (esym FG)).
set x := @bindX _ _; exact: (@eq_rect_bind_error Z x (esym FG)).
Qed.

Lemma cont_monad_contT r :
  contT r ModelMonad.identity = ModelMonad.Cont.t r.
Proof.
rewrite /= /econtMonadM /ModelMonad.Cont.t.
have FG : MC_functor r ModelMonad.identity = ModelMonad.Cont.functor r.
  apply: functor_ext => /=.
  apply FunctionalExtensionality.functional_extensionality_dep => A.
  apply FunctionalExtensionality.functional_extensionality_dep => B.
  by apply fun_ext => f; apply fun_ext => m.
apply (@monad_of_ret_bind_ext _ _ _ _ _ _ FG) => /=.
  apply/natural_ext => A a /=; exact: (@eq_rect_cont_ret A r _ (esym FG)).
set x := @bindC _ _; exact: (@eq_rect_bind_cont r x (esym FG)).
Qed.

End instantiations_with_the_identity_monad.

Section calcul.

Let contTi := @contT^~ ModelMonad.identity.
Let callcci := ModelCont.callcc.

Definition break_if_none (m : monad) (break : _) (acc : nat) (x : option nat) : m nat :=
  if x is Some x then Ret (x + acc) else break acc.

Definition sum_until_none (xs : seq (option nat)) : contTi nat nat :=
  callcci (fun break : nat -> contTi nat nat => foldM (break_if_none break) 0 xs).

Goal sum_until_none [:: Some 2; Some 6; None; Some 4] = @^~ 8.
by cbv.
Abort.

Definition calcul : contTi nat nat :=
  (contTi _ # (fun x => 8 + x))
  (callcci (fun k : _ -> contTi nat _ => (k 5) >>= (fun y => Ret (y + 4)))).

Goal calcul = @^~ 13.
by cbv.
Abort.

End calcul.

Section lifting.
Variables (E : functor) (M : monad) (op : E.-operation M)
          (N : monad) (e : monadM M N).
Definition lifting (f : E \O N ~~> N) :=
  forall X : UU0, e X \o op X = f X \o (E # e X).
End lifting.

Section liftingt.
Variables (E : functor) (M : monad) (op : E.-operation M)
          (t : monadT).
Definition lifting_monadT := lifting op (Lift t M).
End liftingt.

Section algebraicity.
Variables (E : functor) (M : monad).
Definition algebraicity (op : E.-operation M) :=
  forall (A B : UU0) (f : A -> M B) (t : E (M A)),
    op A t >>= f = op B ((E # (fun m => m >>= f)) t).
End algebraicity.

Module AOperation.
Section aoperation.
Variables (E : functor) (M : monad).
Record mixin_of (op : E \O M ~> M) := Mixin { _ : algebraicity op }.
Record class_of (op : E \O M ~~> M) := Class {
  base : Natural.mixin_of op ;
  mixin : mixin_of (Natural.Pack base) }.
Structure t := Pack { m : E \O M ~~> M ; class : class_of m }.
Definition baseType (o : t) := Natural.Pack (base (class o)).
End aoperation.
Module Exports.
Arguments m {E} {M}.
Notation aoperation := t.
Coercion baseType : aoperation >-> nattrans.
Canonical baseType.
End Exports.
End AOperation.
Export AOperation.Exports.

Notation "E .-aoperation M" := (aoperation E M).

Section algebraic_operation_interface.
Variables (E : functor) (M : monad) (op : E.-aoperation M).
Lemma algebraic : algebraicity op.
Proof. by case: op => ? [? []]. Qed.
Lemma aoperation_ext (f g : E.-aoperation M) :
  f = g <-> forall a, (f a = g a :> (_ -> _)).
Proof.
split => [ -> // |]; move: f g => [f Hf] [g Hg] /= fg.
have ? : f = g by exact: FunctionalExtensionality.functional_extensionality_dep.
subst g; congr (AOperation.Pack _); exact/proof_irr.
Qed.

End algebraic_operation_interface.

Section algebraic_operation_examples.

Lemma algebraic_empty : algebraicity ListOps.empty_op.
Proof. by []. Qed.

Lemma algebraic_append : algebraicity ListOps.append_op.
Proof.
move=> A B f [t1 t2] /=.
rewrite !bindE /= /ModelMonad.ListMonad.bind /= /Actm /=.
rewrite /Monad_of_ret_bind.Map /=.
rewrite /ModelMonad.ListMonad.bind /= /ModelMonad.ListMonad.ret /=.
by rewrite -flatten_cat -map_cat /= -flatten_cat -map_cat.
Qed.

Lemma algebraic_output L : algebraicity (@OutputOps.output_op L).
Proof.
move=> A B f [w [x w']].
rewrite bindE /= /OutputOps.output /= bindE /= !cats0.
by case: f => x' w''; rewrite catA.
Qed.

(* NB: flush is not algebraic *)
Lemma algebraic_flush L : algebraicity (@OutputOps.flush_op L).
Proof.
move=> A B f [x w].
rewrite /OutputOps.flush_op /=.
rewrite /OutputOps.flush /=.
rewrite /Actm /=.
rewrite bindE /=.
rewrite /OutputOps.Flush.actm.
rewrite bindE /=.
rewrite cats0.
case: f => x' w'.
Abort.

Lemma algebraic_throw Z : algebraicity (@ExceptOps.throw_op Z).
Proof. by []. Qed.

Definition throw_aop Z : (ExceptOps.Throw.func Z).-aoperation (ModelMonad.Except.t Z) :=
  AOperation.Pack (AOperation.Class (AOperation.Mixin (@algebraic_throw Z))).

(* NB: handle is not algebraic *)
Lemma algebraic_handle Z : algebraicity (@ExceptOps.handle_op Z).
Proof.
move=> A B f t.
rewrite /ExceptOps.handle_op /=.
rewrite /ExceptOps.handle /=.
rewrite /uncurry /prod_curry.
case: t => -[z//|a] g /=.
rewrite bindE /=.
case: (f a) => // z.
rewrite bindE /=.
rewrite /ModelMonad.Except.bind /=.
rewrite /Actm /=.
rewrite /Monad_of_ret_bind.Map /=.
rewrite /ModelMonad.Except.bind /=.
case: (g z) => [z0|a0].
Abort.

Lemma algebraic_ask E : algebraicity (@EnvironmentOps.ask_op E).
Proof. by []. Qed.

(* NB: local is not algebraic *)
Lemma algebraic_local E : algebraicity (@EnvironmentOps.local_op E).
Proof.
move=> A B f t.
rewrite /EnvironmentOps.local_op /=.
rewrite /EnvironmentOps.local /=.
apply fun_ext => e /=.
rewrite bindE /=.
rewrite /ModelMonad.Environment.bind /=.
rewrite /Actm /=.
rewrite /Monad_of_ret_bind.Map /=.
rewrite /ModelMonad.Environment.bind /=.
rewrite /ModelMonad.Environment.ret /=.
rewrite /EnvironmentOps.Local.actm /=.
case: t => /= ee m.
rewrite bindE /=.
rewrite /ModelMonad.Environment.bind /=.
rewrite /Actm /=.
rewrite /Monad_of_ret_bind.Map /=.
rewrite /ModelMonad.Environment.bind /=.
rewrite /ModelMonad.Environment.ret /=.
Abort.

Lemma algebraic_get S : algebraicity (@StateOps.get_op S).
Proof. by []. Qed.

Definition get_aop S : (StateOps.Get.func S).-aoperation (ModelMonad.State.t S) :=
  AOperation.Pack (AOperation.Class (AOperation.Mixin (@algebraic_get S))).

Lemma algebraic_put S : algebraicity (@StateOps.put_op S).
Proof. by move=> ? ? ? []. Qed.

Definition put_aop S : (StateOps.Put.func S).-aoperation (ModelMonad.State.t S) :=
  AOperation.Pack (AOperation.Class (AOperation.Mixin (@algebraic_put S))).

Lemma algebraicity_abort r : algebraicity (ContOps.abort_op r).
Proof. by []. Qed.

Definition abort_aop r : (ContOps.Abort.func r).-aoperation (ModelMonad.Cont.t r) :=
  AOperation.Pack (AOperation.Class (AOperation.Mixin (@algebraicity_abort r))).

Lemma algebraicity_callcc r : algebraicity (ContOps.acallcc_op r).
Proof. by []. Qed.

Definition callcc_aop r : (ContOps.Acallcc.func r).-aoperation (ModelMonad.Cont.t r) :=
  AOperation.Pack (AOperation.Class (AOperation.Mixin (@algebraicity_callcc r))).

End algebraic_operation_examples.

Section proposition17.

Section psi.
Variables (E : functor) (M : monad).

Definition psi' (n : E ~~> M) : E \O M ~~> M :=
  fun X => Join \o n (M X).

Lemma natural_psi' (n : E ~> M) : naturality (E \O M) M (psi' n).
Proof.
move=> A B h; rewrite /psi'.
rewrite -/(Join \o n (M A)) compA natural.
by rewrite -compA (natural n).
Qed.

Definition psi0 (n : E ~> M) : E.-operation M := Natural.Pack (Natural.Mixin (natural_psi' n)).

Lemma algebraic_psi0 (n : E ~> M) : algebraicity (psi0 n).
Proof.
move=> A B g t.
rewrite bindE /Bind.
rewrite -(compE (M # g)).
rewrite compA.
rewrite /=.
rewrite -[in X in _ = Join X]compE.
rewrite -[in RHS](natural n).
transitivity (Join ((M # (Join \o (M # g))) (n (M A) t))) => //.
rewrite -[in X in Join X = _]compE.
rewrite (natural JOIN).
rewrite functor_o.
rewrite -[in RHS]FCompE.
rewrite -[RHS]compE.
rewrite [in RHS]compA.
by rewrite joinA.
Qed.

Definition psi (n : E ~> M) : E.-aoperation M :=
  AOperation.Pack (AOperation.Class (AOperation.Mixin (algebraic_psi0 n))).

Lemma psiE (n : E ~> M) A : (psi n) A = Join \o n (M A).
Proof. by []. Qed.

End psi.

Section phi.
Variables (E : functor) (M : monad).

Definition phi' (op : E.-operation M) : E ~~> M := fun X => op X \o (E # Ret).

Lemma natural_phi' (op : E.-operation M) : naturality E M (phi' op).
Proof.
move=> A B h; rewrite /phi'.
rewrite compA.
rewrite (natural op).
rewrite -compA.
rewrite -[in RHS]compA.
congr (_ \o _).
rewrite /=.
rewrite -2!(functor_o E).
rewrite (natural RET).
by rewrite FIdf.
Qed.

Definition phi (op : E.-operation M) : E ~> M :=
  Natural.Pack (Natural.Mixin (natural_phi' op)).

Lemma phiE (op : E.-operation M) X : phi op X = op X \o (E # Ret).
Proof. by []. Qed.

End phi.

Section bijection.
Variables (E : functor) (M : monad).

Lemma psiK (op : E ~> M) : phi (psi op) = op.
Proof.
apply/nattrans_ext => A.
rewrite phiE psiE; apply fun_ext => m /=.
rewrite -(compE (op _)) -(natural op) -(compE Join).
by rewrite compA joinMret.
Qed.

Lemma phiK (op : E.-aoperation M) : psi (phi op) = op.
Proof.
apply/aoperation_ext => A.
rewrite psiE phiE; apply fun_ext => m /=.
rewrite -(compE (op _)) joinE (algebraic op).
rewrite -(compE (E # _)) -functor_o.
rewrite -(compE (op _)).
rewrite /Bind.
rewrite (_ : (fun _ => Join _) = Join \o (M # id)) //.
rewrite -(compA Join).
rewrite functor_id.
rewrite compidf.
by rewrite joinretM functor_id compfid.
Qed.

End bijection.
End proposition17.

Section theorem19.
Variables (E : functor) (M : monad) (op : E.-aoperation M).
Variables (N : monad) (e : monadM M N).

Definition alifting : E.-aoperation N := psi (monadM_nt e \v phi op).

Lemma aliftingE :
  alifting = (fun X => Join \o e (N X) \o phi op (N X)) :> (_ ~~> _).
Proof. by []. Qed.

Lemma theorem19 : lifting op e alifting.
Proof.
move=> X.
apply fun_ext => Y.
transitivity (e X (op X Y)) => //.
rewrite /alifting compE psiE vcompE phiE.
rewrite 3!compE.
rewrite (_ : (E # Ret) ((E # e X) Y) = (E # (M # e X)) ((E # Ret) Y)); last first.
  rewrite -[in LHS]compE -functor_o.
  rewrite -[in RHS]compE -functor_o.
  rewrite (natural RET).
  by rewrite FIdf.
rewrite (_ : op (N X) ((E # (M # e X)) ((E # Ret) Y)) =
             (M # e X) (op (M X) ((E # Ret) Y))); last first.
  rewrite -(compE (M # e X)).
  by rewrite (natural op).
transitivity (e X (Join (op (M X) ((E # Ret) Y)))); last first.
  rewrite joinE monadMbind.
  rewrite bindE.
  rewrite -(compE _ (M # e X)).
  by rewrite -natural.
congr (e X _).
by rewrite -[in LHS](phiK op).
Qed.
End theorem19.

Section examples_of_lifting.

Section state_errorT.
Variables S Z : UU0.
Let M : monad := ModelState.state S.
Let erZ : monadT := errorT Z.

Let lift_getX : (StateOps.Get.func S).-aoperation (erZ M) :=
  alifting (get_aop S) (Lift erZ M).

Goal forall X (k : S -> erZ M X), lift_getX _ k = StateOps.get_op _ k.
by [].
Abort.

Goal lift_getX _ Ret = liftX _ (@ModelState.get S).
by [].
Abort.

End state_errorT.

Section continuation_stateT.
Variable (r S : UU0).
Let M : monad := ModelCont.t r.
Let stS : monadT := stateT S.

Let lift_acallccS : (ContOps.Acallcc.func r).-aoperation (stS M) :=
  alifting (callcc_aop r) (Lift stS M).

Goal forall A (f : (stS M A -> r) -> stS M A),
  lift_acallccS _ f = (fun s k => f (fun m => uncurry m (s, k)) s k) :> stS M A.
move=> A f.
rewrite /lift_acallccS /=.
by rewrite /stS /= /stateT /= /stateMonadM /=; unlock => /=.
Abort.

Definition usual_callccS (A B : UU0) (f : (A -> stS M B) -> stS M A) : stS M A :=
  fun s k => f (fun x _ _ => k (x, s)) s k.

Lemma callccS_E A B f : lift_acallccS _
    (fun k : stS M A -> r =>
       f (fun x => (fun (_ : S) (_ : B * S -> r) => k (@RET (stS M) A x)) : stS M B)) =
  usual_callccS f.
Proof.
rewrite /lift_acallccS /=.
by rewrite /stS /= /stateT /= /stateMonadM /=; unlock => /=.
Qed.

End continuation_stateT.

End examples_of_lifting.

Section examples_of_programs.

Lemma stateMonad_of_stateT S (M : monad) : MonadState.class_of S (stateT S M).
Proof.
refine (@MonadState.Class _ _ _ (@MonadState.Mixin _ (stateT S M) (fun s => Ret (s, s)) (fun s' _ => Ret (tt, s')) _ _ _ _)).
move=> s s'.
apply fun_ext => s0.
case: M => m [[f fi fo] [/= r j a b c]].
rewrite /Bind /Join /JOIN /estateMonadM /Monad_of_ret_bind /bindS /Actm /=.
rewrite /Monad_of_ret_bind.Map bindretf /=.
by rewrite /retS bindretf.
move=> s.
apply fun_ext => s0.
case: M => m [[f fi fo] [/= r j a b c]].
rewrite /retS /Ret /RET /Bind /estateMonadM /Monad_of_ret_bind /Actm /bindS /=.
rewrite /Monad_of_ret_bind.Map.
by rewrite 4!bindretf /=.
apply fun_ext => s.
case: M => m [[f fi fo] [/= r j a b c]].
rewrite /Bind /Join /JOIN /=.
rewrite /estateMonadM /Monad_of_ret_bind /bindS /Actm /=.
rewrite /Monad_of_ret_bind.Map bindretf /=.
by rewrite /retS bindretf.
case: M => m [[f fi fo] [/= r j a b c]].
move=> A k.
apply fun_ext => s.
rewrite /Bind /Join /JOIN /= /bindS /estateMonadM /=.
rewrite /Monad_of_ret_bind /Actm /Monad_of_ret_bind.Map /=.
rewrite /Monad_of_ret_bind.Map /= /bindS /=.
by rewrite !bindretf /= !bindretf.
Qed.

Canonical stateMonad_of_stateT' S M := MonadState.Pack (stateMonad_of_stateT S M).

Variable M : failMonad.
Let N := stateT nat M.
Let incr : N unit := Get >>= (Put \o (fun i => i.+1)).
Let prog := incr >> (liftS Fail : N nat) >> incr.

End examples_of_programs.

Section examples_of_programs2.

Let M := ModelState.state nat.
Definition optionT := errorT unit M.
Definition liftOpt := liftX unit.

Lemma failMonad_of_ : MonadFail.class_of optionT.
Proof.
refine (@MonadFail.Class _ _ (@MonadFail.Mixin optionT (fun B => Ret (@inl _ B tt))  _ )).
by [].
Qed.

Canonical failMonad_of_' := MonadFail.Pack failMonad_of_.

Definition GetO := liftOpt (@Get nat M).
Definition PutO := (fun s => liftOpt (@Put nat M s)).
Let incr := GetO >>= (fun i => PutO (i.+1)).
Let prog := incr >> (Fail : optionT nat) >> incr.

End examples_of_programs2.

Section lifting_uniform.

Let M S: monad := ModelState.state S.
Let optT : monadT := errorT unit.

Definition lift_getX S : (StateOps.Get.func S) \O (optT (M S)) ~> (optT (M S)) :=
  alifting (get_aop S) (Lift optT (M S)).

Let lift_putX S : (StateOps.Put.func S) \O (optT (M S)) ~> (optT (M S)) :=
  alifting (put_aop S) (Lift optT (M S)).

Let incr : optT (M nat) unit := (@lift_getX _ _ Ret) >>= (fun i => @lift_putX _ _ (i.+1, Ret tt)).
Let prog : optT (M nat) unit := incr >> (Fail : optT (M nat) unit) >> incr.

End lifting_uniform.

Definition natural_hmap_lift (t : monadT)
    (h : forall (M N : monad), (M ~> N) -> (t M ~> t N)) :=
  forall (M N : monad) (n : M ~> N) X,
    h M N n X \o Lift t M X = Lift t N X \o n X.

Module Fmt.
Section functorial_monad_transformer.
Record mixin_of (t : monadT) := Class {
  hmap : forall (M N : monad), (M ~> N) -> (t M ~> t N) ;
  _ : forall M N (e : monadM M N), MonadMLaws.ret (hmap (monadM_nt e)) ;
  _ : forall M N (e : monadM M N), MonadMLaws.bind (hmap (monadM_nt e)) ;
  _ : forall (M : monad), hmap (NId M) = NId (t M) ;
  _ : forall (M N P : monad) (t : M ~> N) (s : N ~> P), hmap s \v hmap t = hmap (s \v t) ;
  _ : natural_hmap_lift hmap }.
Structure t := Pack { m : monadT ; class : mixin_of m }.
End functorial_monad_transformer.
Module Exports.
Notation FMT := t.
Definition Hmap (T : t) : forall (M N : monad), (M ~> N) -> (m T M ~> m T N) :=
  let: Pack _ (Class f _ _ _ _ _) := T return forall (M N : monad), (M ~> N) -> (m T M ~> m T N) in f.
Arguments Hmap _ _ : simpl never.
Coercion m : FMT >-> monadT.
End Exports.
End Fmt.
Export Fmt.Exports.

Section fmt_lemmas.
Lemma fmt_ret (t : FMT) M N (e : monadM M N) :
  MonadMLaws.ret (Hmap t (monadM_nt e)).
Proof. by case: t M N e => m []. Qed.
Lemma fmt_bind (t : FMT) M N (e : monadM M N) :
  MonadMLaws.bind (Hmap t (monadM_nt e)).
Proof. by case: t M N e => m []. Qed.
Lemma fmt_NId (t : FMT) (M : monad) : Hmap t (NId M) = NId (t M).
Proof. by case: t M => m []. Qed.
Lemma fmt_vcomp (t : FMT) (M N P : monad) (n : M ~> N) (s : N ~> P) :
  Hmap t s \v Hmap t n = Hmap t (s \v n).
Proof. by case: t M N P n s => m []. Qed.
Lemma natural_hmap (T : FMT) : natural_hmap_lift (Hmap T).
Proof. by case: T => [? []]. Qed.
End fmt_lemmas.

Section error_FMT.
Variable X : UU0.
Let T : monadT := errorT X.
Let hmapX' (F G : monad) (tau : F ~> G) (A : UU0) (t : T F A) : T G A :=
  tau _ t.

Lemma natural_hmapX' (F G : monad) (tau : F ~> G) :
  naturality (T F) (T G) (hmapX' tau).
Proof.
move=> A B h.
rewrite /hmapX' -2!FunctionalExtensionality.eta_expansion.
have H : forall G, errorT X G # h = MX_map h.
  move=> E; apply fun_ext => m /=.
  rewrite /Actm /= /Monad_of_ret_bind.Map /MX_map /= /bindX /= fmapE.
  congr (_ >>= _).
  by apply fun_ext; case.
by rewrite 2!H /MX_map /= natural.
Qed.

Definition hmapX (F G : monad) (tau : F ~> G) : T F ~> T G :=
  Natural.Pack (Natural.Mixin (natural_hmapX' tau)).

Let monadMret_hmapX (F G : monad) (e : monadM F G) :
  MonadMLaws.ret (hmapX (monadM_nt e)).
Proof.
move=> A; apply fun_ext => /= a.
by rewrite /hmapX' /retX /= -(compE (e _)) monadMret.
Qed.

Let monadMbind_hmapX (F G : monad) (e : monadM F G) :
  MonadMLaws.bind (hmapX (monadM_nt e)).
Proof.
move=> A B m f; rewrite /hmapX /=.
rewrite !bindE /= /bindX /=.
rewrite !monadMbind /=.
rewrite !bindA /=.
congr (_ >>= _).
apply fun_ext.
case.
  move=> x.
  rewrite bindretf.
  rewrite -(compE (e _)) monadMret.
  rewrite bindretf /=.
  by rewrite -(compE (e _)) monadMret.
move=> a.
rewrite /retX bindretf /=.
rewrite -(compE (e _)) monadMret.
by rewrite bindretf.
Qed.

Let hmapX_NId (M : monad) : hmapX (NId M) = NId (T M).
Proof. by apply nattrans_ext. Qed.

Let hmapX_v (M N P : monad) (t : M ~> N) (s : N ~> P) :
  hmapX s \v hmapX t = hmapX (s \v t).
Proof. exact/nattrans_ext. Qed.

Let hmapX_lift : natural_hmap_lift hmapX.
Proof.
move=> M N t A.
rewrite /hmapX.
rewrite /Lift /= /liftX /=.
rewrite -!FunctionalExtensionality.eta_expansion.
rewrite /retX /=.
rewrite /Bind /=.
rewrite (_ : (fun x : A => Ret (inr x)) = Ret \o inr) //.
rewrite (_ : (fun m : Monad.acto M A => Join ((M # (Ret \o inr)) m)) =
             Join \o (M # (Ret \o inr)) ) //.
rewrite functor_o.
rewrite (compA Join).
rewrite joinMret.
rewrite compidf.
rewrite (_ : (fun m : N A => Join _) = Join \o (N # (Ret \o inr))) //.
rewrite functor_o.
rewrite (compA Join).
rewrite joinMret.
rewrite compidf.
by rewrite natural.
Qed.

Program Definition errorFMT : FMT := @Fmt.Pack (errorT X)
  (@Fmt.Class _ (fun M N nt => hmapX nt) monadMret_hmapX
    monadMbind_hmapX _ hmapX_v hmapX_lift).

End error_FMT.

Section Fmt_stateT.
Variable S : UU0.
Let T : monadT := stateT S.
Definition hmapS' (F G : monad) (tau : F ~> G) (A : UU0) (t : T F A) : T G A :=
  fun s => tau _ (t s).

Lemma natural_hmapS' (F G : monad) (tau : F ~> G) :
  naturality (T F) (T G) (hmapS' tau).
Proof.
move=> A B h.
rewrite /hmapS'.
rewrite /=.
have H : forall G, estateMonadM S G # h = MS_functor S G # h.
  move=> H; apply fun_ext => m.
  rewrite /Actm /=.
  rewrite /Monad_of_ret_bind.Map /=.
  rewrite /bindS /MS_fmap /retS /=.
  apply fun_ext => s.
  set j := uncurry _.
  have -> : j = Ret \o (fun x : A * S => (h x.1, x.2)).
    by apply fun_ext; case.
  by rewrite -fmapE.
rewrite !H {H}.
rewrite {1}/MS_functor /= {1}/Actm /=.
rewrite /MS_fmap; apply fun_ext => m; apply fun_ext => s /=.
rewrite -(compE  _ (tau (A * S)%type)).
by rewrite natural.
Qed.

Definition hmapS (F G : monad) (tau : F ~> G) : T F ~> T G :=
  Natural.Pack (Natural.Mixin (natural_hmapS' tau)).

Let monadMret_hmapS (F G : monad) (e : monadM F G) :
  MonadMLaws.ret (hmapS (monadM_nt e)).
Proof.
move=> A; apply fun_ext => /= a.
rewrite /hmapS' /= /retS /=; apply fun_ext => s.
by rewrite [in LHS]curryE monadMret.
Qed.

Let monadMbind_hmapS (F G : monad) (e : monadM F G) :
  MonadMLaws.bind (hmapS (monadM_nt e)).
Proof.
move=> A B m f.
rewrite /hmapS /=; apply fun_ext => s.
rewrite !bindE /= /bindS /=.
rewrite !monadMbind /=.
rewrite !bindA /=.
congr (_ >>= _).
apply fun_ext; case => a s'.
rewrite /retS /=.
rewrite bindretf.
rewrite -(compE _ Ret).
rewrite /uncurry /prod_curry.
rewrite -bind_fmap.
rewrite monadMret.
rewrite -(compE _ Ret).
rewrite natural.
rewrite FIdf.
rewrite bindE.
rewrite -(compE _ Ret).
rewrite -(compE _ (_ \o _)).
rewrite natural.
rewrite compA.
rewrite joinretM.
rewrite FIdf.
by rewrite compidf.
Qed.

Let hmapS_NId (M : monad) : hmapS (NId M) = NId (T M).
Proof. by apply nattrans_ext. Qed.

Let hmapS_v (M N P : monad) (t : M ~> N) (s : N ~> P) :
  hmapS s \v hmapS t = hmapS (s \v t).
Proof. exact/nattrans_ext. Qed.

Let hmapS_lift : natural_hmap_lift hmapS.
Proof.
move=> M N t A.
rewrite /hmapS /= /hmapS'.
rewrite /Lift /=.
rewrite /stateMonadM /=.
unlock.
rewrite /=.
rewrite /liftS /=.
rewrite /Bind /=.
apply fun_ext => ma /=.
apply fun_ext => s /=.
rewrite 2!(_ : (fun x : A => Ret (x, s)) = Ret \o (fun x => (x, s))) //.
rewrite functor_o.
rewrite -(compE Join).
rewrite compA.
rewrite joinMret.
rewrite compidf.
rewrite functor_o.
rewrite -(compE Join).
rewrite compA.
rewrite joinMret.
rewrite compidf.
rewrite -(compE _ (t A)).
by rewrite natural.
Qed.

Program Definition stateFMT : FMT := @Fmt.Pack T
  (@Fmt.Class _ (fun M N nt => hmapS nt) monadMret_hmapS
    monadMbind_hmapS _ hmapS_v hmapS_lift).

End Fmt_stateT.
