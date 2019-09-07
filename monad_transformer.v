From mathcomp Require Import all_ssreflect.
From mathcomp Require boolp.
Require Import monae_lib monad fail_monad.

(* main: reference modular monad transformer, Jaskelioff ESOP 2009 *)

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
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.

Module monadM.
Section monadm.
Variables (M N : monad).
Record class_of (e : M ~~> N) := Class {
  _ : forall A, @Ret _ A = e _ \o Ret _;
  _ : forall A B (m : M A) (f : A -> M B),
    e _ (m >>= f) = e _ m >>= (fun a => e _ (f a)) }.
Structure t := Pack { e : M ~~> N ; class : class_of e }.
End monadm.
Module Exports.
Notation monadM := t.
Coercion e : monadM >-> Funclass.
End Exports.
End monadM.
Export monadM.Exports.

Section monadM_interface.
Variables (M N : monad) (f : monadM M N).
Lemma monadMret : forall A, @Ret _ A = f _ \o Ret _.
Proof. by case: f => ? []. Qed.
Lemma monadMbind A B (m : M A) (h : A -> M B) :
  f _ (m >>= h) = f _ m >>= (fun a => f _ (h a)).
Proof. by case: f => ? []. Qed.
End monadM_interface.

Section monadM_lemmas.
Variables (M N : monad) (f : monadM M N).
Lemma natural_monadM : naturality M N f.
Proof.
move=> A B h; rewrite boolp.funeqE => m /=.
have <- : Join ((M # (Ret _ \o h)) m) = (M # h) m.
  by rewrite functor_o [LHS](_ : _ = (Join \o M # Ret _) ((M # h) m)) // joinMret.
move: (@monadMbind M N f A B m (Ret _ \o h)); rewrite 2!bindE => ->.
rewrite (_ : (fun a => f _ ((Ret _ \o h) a)) = Ret _ \o h); last first.
  by rewrite [in RHS](monadMret f).
rewrite [RHS](_ : _ = (Join \o (N # Ret _ \o N # h)) (f _ m)); last first.
  by rewrite compE functor_o.
by rewrite compA joinMret.
Qed.
End monadM_lemmas.

Definition natural_of_monadM (M N : monad) (f : monadM M N) : M ~> N :=
  Natural.Pack (@Natural.Class _ _ _ (natural_monadM f)).

Module MonadT.
Record class_of (T : monad -> monad) := Class {
  retT : forall M : monad, FId ~~> T M;
  bindT : forall (M : monad) A B, (T M) A -> (A -> (T M) B) -> (T M) B ;
  liftT : forall M : monad, monadM M (T M) }.
Record t := Pack {m : monad -> monad ; class : class_of m}.
Module Exports.
Notation monadT := t.
Coercion m : monadT >-> Funclass.
Definition RetT (T : t) : forall M : monad, FId ~~> m T M :=
  let: Pack _ (Class f _ _) := T return forall M : monad, FId ~~> m T M in f.
Arguments RetT _ _ [A] : simpl never.
Definition BindT (T : t) : forall (M : monad) A B, (m T M) A -> (A -> (m T M) B) -> (m T M) B :=
  let: Pack _ (Class _ f _) := T return forall (M : monad) A B, (m T M) A -> (A -> (m T M) B) -> (m T M) B in f.
Arguments BindT _ _ [A] [B] : simpl never.
Definition LiftT (T : t) : forall M : monad, monadM M (m T M) :=
  let: Pack _ (Class _ _ f) := T return forall M : monad, monadM M (m T M) in f.
Arguments LiftT _ _ : simpl never.
End Exports.
End MonadT.
Export MonadT.Exports.

Section state_monad_transformer.

Local Obligation Tactic := idtac.

Variables (S : Type) (M : monad).

Definition MS := fun A => S -> M (A * S)%type.

Definition retS A (a : A) : MS A :=
  fun (s : S) => Ret _ (a, s) : M (A * S)%type.

Definition bindS A B (m : MS A) f := (fun s => m s >>= uncurry f) : MS B.

Definition MS_fmap A B (f : A -> B) (m : MS A) : MS B.
move=> s.
rewrite /MS in m.
move: (m s) => m'.
Local Open Scope mprog.
exact: (fmap (fun x => (f x.1, x.2)) m').
Local Close Scope mprog.
Defined.

Definition MS_functor : functor.
apply: (Functor.Pack (@Functor.Class MS MS_fmap _ _)).
move=> A.
rewrite boolp.funeqE => m.
rewrite /MS_fmap /=.
rewrite boolp.funeqE => s.
rewrite (_ : (fun x : A * S => (x.1, x.2)) = id) //.
by rewrite functor_id.
by rewrite boolp.funeqE; case.
move=> A B C g h.
rewrite /MS_fmap.
rewrite boolp.funeqE => m.
rewrite boolp.funeqE => s /=.
rewrite -[RHS]compE.
by rewrite -functor_o /=.
Defined.

Definition retS_natural : FId ~> MS_functor.
apply: (@Natural.Pack FId MS_functor retS (Natural.Class _)).
move=> A B h.
rewrite /Fun /=.
rewrite boolp.funeqE => a /=.
rewrite /MS_fmap /=.
rewrite boolp.funeqE => s /=.
rewrite /retS.
rewrite -[LHS]compE.
by rewrite (natural Ret).
Defined.

Program Definition estateMonadM : monad :=
  @Monad_of_ret_bind MS_functor retS_natural bindS _ _ _.
Next Obligation.
by move=> A B a f; rewrite /bindS boolp.funeqE => s; rewrite bindretf.
Defined.
Next Obligation.
move=> A m; rewrite /bindS boolp.funeqE => s.
rewrite -[in RHS](bindmret (m s)); by bind_ext; case.
Defined.
Next Obligation.
move=> A B C m f g; rewrite /bindS boolp.funeqE => s.
by rewrite bindA; bind_ext; case.
Defined.

Definition liftS A (m : M A) : estateMonadM A :=
  fun s => @Bind M _ _ m (fun x => @Ret M _ (x, s)).

Program Definition stateMonadM : monadM M estateMonadM :=
  monadM.Pack (@monadM.Class _ _ liftS _ _).
Next Obligation.
move=> A.
rewrite /liftS boolp.funeqE => a /=; rewrite boolp.funeqE => s /=.
by rewrite bindretf.
Qed.
Next Obligation.
move=> A B m f; rewrite /liftS boolp.funeqE => s.
rewrite [in RHS]/Bind [in RHS]/Join /= /Monad_of_ret_bind.join /= /bindS !bindA.
bind_ext => a; by rewrite !bindretf.
Qed.

End state_monad_transformer.

Definition stateT S : monadT :=
  MonadT.Pack (@MonadT.Class (estateMonadM S) (@retS S) (@bindS S) (@stateMonadM S)).

Section exception_monad_transformer.

Local Obligation Tactic := idtac.

Variables (Z : Type) (* the type of exceptions *) (M : monad).

Definition MX := fun X => M (Z + X)%type.

Definition retX X x : MX X := Ret _ (inr x).

Definition bindX X Y (t : MX X) (f : X -> MX Y) : MX Y :=
  t >>= fun c => match c with inl z => Ret _ (inl z) | inr x => f x end.

Local Open Scope mprog.
Definition MX_map A B (f : A -> B) (m : MX A) : MX B :=
  fmap (fun x => match x with inl y => inl y | inr y => inr (f y) end) m.
Local Close Scope mprog.

Definition exceptionT_functor : functor.
apply: (Functor.Pack (@Functor.Class MX MX_map _ _)).
move=> A; rewrite boolp.funeqE => x.
rewrite /MX in x *.
rewrite /MX_map.
by rewrite (_ : (fun _ => _) = id) ?functor_id // boolp.funeqE; case.
rewrite /MX_map /=.
move=> A B C g h /=.
rewrite boolp.funeqE => x /=.
rewrite -[RHS]compE -functor_o /=; congr (_ # _).
by rewrite boolp.funeqE; case.
Defined.

Definition retX_nat : FId ~> exceptionT_functor.
apply: (@Natural.Pack FId exceptionT_functor retX (Natural.Class _)).
move=> A B h.
rewrite /retX boolp.funeqE /= => a.
rewrite /Fun /= /MX_map.
rewrite -[LHS]compE.
by rewrite (natural Ret).
Defined.

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

Definition liftX X (m : M X) : eexceptionMonadM X := @Bind M _ _ m (fun x => @Ret eexceptionMonadM _ x).

Program Definition exceptionMonadM : monadM M eexceptionMonadM :=
  monadM.Pack (@monadM.Class _ _ liftX _ _).
Next Obligation.
by move=> A; rewrite boolp.funeqE => a; rewrite /liftX /= bindretf.
Qed.
Next Obligation.
move=> A B m f; rewrite /liftX [in RHS]/Bind [in RHS]/Join /=.
rewrite  /Monad_of_ret_bind.join /= /bindX !bindA.
bind_ext => a; by rewrite !bindretf.
Qed.

End exception_monad_transformer.

Definition errorT Z : monadT :=
  MonadT.Pack (@MonadT.Class (eexceptionMonadM Z) (@retX Z) (@bindX Z) (@exceptionMonadM Z)).

Section continuation_monad_tranformer.

Local Obligation Tactic := idtac.

Variables (r : Type)  (M : monad).

Definition MC : Type -> Type := fun A => (A -> M r) -> M r %type.

Definition retC A (a : A) : MC A := fun k => k a.

Definition bindC A B (m : MC A) f : MC B := fun k => m (f^~ k).

Definition MC_map A B (f : A -> B) (m : MC A) : MC B.
move=> Br; apply m => a.
apply Br; exact: (f a).
Defined.

Definition MC_functor : functor.
apply: (Functor.Pack (@Functor.Class MC MC_map _ _)).
by [].
by [].
Defined.

Definition retC_nat : FId ~> MC_functor.
apply: (@Natural.Pack FId MC_functor retC (Natural.Class _)).
by [].
Defined.

Program Definition econtMonadM : monad :=
  @Monad_of_ret_bind MC_functor retC_nat bindC _ _ _.
Next Obligation. by []. Qed.
Next Obligation. by []. Qed.
Next Obligation. by []. Qed.

Definition liftC A (x : M A) : econtMonadM A := fun k => x >>= k.

Program Definition contMonadM : monadM M econtMonadM  :=
  monadM.Pack (@monadM.Class _ _ liftC  _ _).
Next Obligation.
move => A.
rewrite /liftC boolp.funeqE => a /=.
rewrite boolp.funeqE => s.
by rewrite bindretf.
Qed.
Next Obligation.
move => A B m f.
rewrite /liftC boolp.funeqE => cont.
by rewrite !bindA.
Qed.

End continuation_monad_tranformer.

Definition contT r : monadT :=
  MonadT.Pack (@MonadT.Class (econtMonadM r) (@retC r) (@bindC r) (@contMonadM r)).

Definition abortT r X (M : monad) A : contT r M A := fun _ : A -> M r => Ret _ X.
Arguments abortT {r} _ {M} {A}.

Require Import state_monad.

Section continuation_monad_transformer_examples.

Fixpoint for_loop (M : monad) (it min : nat) (body : nat -> contT unit M unit) : M unit :=
  if it <= min then Ret _ tt
  else if it is it'.+1 then
      (body it') (fun _ => for_loop it' min body)
      else Ret _ tt.

Section for_loop_lemmas.
Variable M : monad.
Implicit Types body : nat  -> contT unit M unit.

Lemma loop0 i body : for_loop i i body = Ret _ tt.
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
  body (i + j) = abortT tt -> for_loop (i + j).+1 i body = Ret _ tt.
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
    (Ret _ tt)
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

Require Import monad_model.

Section instantiations_with_the_identity_monad.

Lemma functor_ext (F G : functor) :
  forall (H : Functor.m F = Functor.m G),
  Functor.f (Functor.class G) =
  eq_rect _ (fun m => forall A B, (A -> B) -> m A -> m B) (Functor.f (Functor.class F)) _ H  ->
  G = F.
Proof.
move: F G => [F [HF1 HF2 HF3]] [G [HG1 HG2 HG3]] /= H; subst G => /= ?; subst HG1.
congr (Functor.Pack (Functor.Class _ _)); exact/boolp.Prop_irrelevance.
Qed.

Lemma natural_ext (F G G' : functor) (t : F ~> G) (t' : F ~> G') (H : G' = G):
  Natural.m t' = eq_rect _ (fun A => _) (Natural.m t) _ (esym H) ->
  t = eq_rect _ _ t' _ H.
Proof.
move=> K.
destruct F.
destruct G.
destruct G'.
simpl in *.
destruct class.
destruct class0.
destruct class1.
destruct H.
destruct t.
destruct t'.
simpl in *.
subst m3.
congr Natural.Pack.
apply/boolp.Prop_irrelevance.
Qed.

Lemma Monad_of_ret_bind_ext (M M' : functor) (ret : FId ~> M) (ret' : FId ~> M')
  (bind : forall A B : Type, M A -> (A -> M B) -> M B)
  (bind' : forall A B : Type, M' A -> (A -> M' B) -> M' B)
  (H1 : BindLaws.left_neutral bind ret)
  (H2 : BindLaws.right_neutral bind ret)
  (H3 : BindLaws.associative bind)
  (H1' : BindLaws.left_neutral bind' ret')
  (H2' : BindLaws.right_neutral bind' ret')
  (H3' : BindLaws.associative bind') :
forall (MM' : M' = M),
ret = eq_rect _ _ ret' _ (MM') ->
bind = @eq_rect _ _ (fun M : functor => forall A B : Type, M A -> (A -> M B) -> M B) bind' _ (MM') ->
Monad_of_ret_bind H1 H2 H3
=
Monad_of_ret_bind H1' H2' H3'.
Proof.
move=> ?; subst M'.
rewrite -Classical_Prop.Eq_rect_eq.eq_rect_eq => ?.
subst ret'.
rewrite -Classical_Prop.Eq_rect_eq.eq_rect_eq => ?.
subst bind'.
congr Monad_of_ret_bind.
exact/boolp.Prop_irrelevance.
exact/boolp.Prop_irrelevance.
exact/boolp.Prop_irrelevance.
Qed.

Lemma state_monad_stateT S :
  stateT S ModelMonad.identity = ModelMonad.State.t S.
Proof.
rewrite /=.
rewrite /estateMonadM /=.
rewrite /ModelMonad.State.t /=.
have MM' : ModelMonad.State.state_functor S = MS_functor S ModelMonad.identity.
  apply: functor_ext => /=.
  rewrite /ModelMonad.State.state_map /MS_fmap.
  apply FunctionalExtensionality.functional_extensionality_dep => A.
  apply FunctionalExtensionality.functional_extensionality_dep => B.
  rewrite boolp.funeqE => x.
  rewrite boolp.funeqE => y.
  rewrite boolp.funeqE => s.
  rewrite /Fun /=.
  rewrite /Monad_of_ret_bind.Map /=.
  by case: (y s).
apply (@Monad_of_ret_bind_ext _ _ _ _ _ _ _ _ _ _ _ _ MM') => //.
apply natural_ext => /=.
apply FunctionalExtensionality.functional_extensionality_dep => A.
apply FunctionalExtensionality.functional_extensionality_dep => B.
rewrite boolp.funeqE => s /=.
move: MM'.
rewrite /=.
admit.
rewrite /bindS.
apply FunctionalExtensionality.functional_extensionality_dep => A.
apply FunctionalExtensionality.functional_extensionality_dep => B.
rewrite boolp.funeqE => x.
rewrite boolp.funeqE => y.
rewrite boolp.funeqE => s.
rewrite /eq_rect.
Abort.

Lemma error_monad_errorT Z :
  errorT Z ModelMonad.identity = ModelMonad.error Z.
Proof. (*congr (Monad_of_ret_bind _ _ _); exact/boolp.Prop_irrelevance. Qed.*) Abort.

Lemma cont_monad_contT r :
  contT r ModelMonad.identity = ModelMonad.Cont.t r.
(*Proof. congr Monad_of_ret_bind; exact/boolp.Prop_irrelevance. Qed.*) Abort.

End instantiations_with_the_identity_monad.

Section calcul.

Let contTi := @contT^~ ModelMonad.identity.
Let callcci := ModelCont.callcc.

Definition break_if_none (m : monad) (break : _) (acc : nat) (x : option nat) : m nat :=
  if x is Some x then Ret _ (x + acc) else break acc.

Definition sum_until_none (xs : seq (option nat)) : contTi nat nat :=
  callcci (fun break : nat -> contTi nat nat => foldM (break_if_none break) 0 xs).

Goal sum_until_none [:: Some 2; Some 6; None; Some 4] = @^~ 8.
by cbv.
Abort.

Definition calcul : contTi nat nat :=
  (contTi _ # (fun x => 8 + x))
  (callcci (fun k : _ -> contTi nat _ => (k 5) >>= (fun y => Ret _ (y + 4)))).

Goal calcul = @^~ 13.
by cbv.
Abort.

End calcul.

Module Lifting.
Section lifting.
Variables (E : functor) (M : monad) (op : operation E M) (N : monad) (e : monadM M N).
Definition P (f : E \O N ~~> N) := forall X, e X \o op X = @f X \o (E # (e X)).
Record mixin_of (f : E \O N ~~> N) := Mixin {
  _ : P f }.
Record class_of (f : E \O N ~~> N) := Class {
  base : Natural.class_of f ;
  mixin : mixin_of f }.
Structure t := Pack {
  m : E \O N ~~> N ;
  class : class_of m }.
Definition baseType (M : t) := Natural.Pack (base (class M)).
End lifting.
Module Exports.
Notation lifting := t.
Coercion baseType : lifting >-> Natural.t.
Canonical baseType.
Notation lifting_def := P.
End Exports.
End Lifting.
Export Lifting.Exports.

Section lifting_interface.
Variables (E : functor) (M : monad) (op : operation E M) (N : monad)
  (e : monadM M N) (L : lifting op e).
Lemma liftingP : forall X, e X \o op X = L X \o (E # (e X)).
Proof. by case: L => ? [? []]. Qed.
End lifting_interface.

Module LiftingT.
Section liftingt.
Variables (E : functor) (M : monad) (op : operation E M) (T : monadT).
Definition t := Lifting.t op (LiftT T M).
End liftingt.
End LiftingT.

(* Algebraic operation *)
Module AOperation.
Section aoperation.
Variables (E : functor) (M : monad).
Definition P (op : E \O M ~~> M) :=
  forall A B (f : A -> M B) (t : E (M A)),
    (op A t >>= f) = op B ((E # (fun m => m >>= f)) t).
Record mixin_of (op : E \O M ~~> M) := Mixin {
  _ : P op }.
Record class_of (op : E \O M ~~> M) := Class {
  base : Natural.class_of op ;
  mixin : mixin_of op }.
Structure t := Pack {
  m : E \O M ~~> M ;
  class : class_of m }.
Definition baseType (M : t) := Natural.Pack (base (class M)).
End aoperation.
Module Exports.
Arguments m {E} {M}.
Notation aoperation := t.
Coercion baseType : aoperation >-> Natural.t.
Canonical baseType.
Notation algebraicity := P.
End Exports.
End AOperation.
Export AOperation.Exports.

Section algebraic_operation_interface.
Variables (E : functor) (M : monad) (op : aoperation E M).
Lemma algebraic : forall A B (f : A -> M B) (t : E (M A)),
   (op A t >>= f) = op B ((E # (fun m => m >>= f)) t).
Proof. by case: op => ? [? []]. Qed.
End algebraic_operation_interface.

Lemma algebraic_get S : algebraicity (@StateOps.get_op S).
Proof. by []. Qed.

Program Definition get_aop S : aoperation (StateOps.get_fun S) (ModelMonad.State.t S) :=
  AOperation.Pack (AOperation.Class _ (AOperation.Mixin (@algebraic_get S))).
Next Obligation. by []. Qed.

Lemma algebraic_put S : algebraicity (@StateOps.put_op S).
Proof. by move=> ? ? ? []. Qed.

Lemma algebraicity_callcc r : algebraicity (ContOps.acallcc_op r).
Proof. by []. Qed.

Program Definition callcc_aop r : aoperation (ContOps.acallcc_fun r) (ModelMonad.Cont.t r) :=
  AOperation.Pack (AOperation.Class _ (AOperation.Mixin (@algebraicity_callcc r))).
Next Obligation. by []. Qed.

Section proposition17.
Section psi.
Variables (E : functor) (M : monad).

Definition psi_g (op' : E ~~> M) : E \O M ~~> M :=
  fun X m => (Monad.Exports.Join X \o @op' _) m.

Lemma natural_psi (op' : E ~> M) : naturality (E \O M) M (psi_g op').
Proof.
move=> A B h; rewrite {}/psi_g.
rewrite (compA (M # h)) compfid.
rewrite (compA (M # h)).
rewrite natural.
rewrite -compA.
rewrite FCompE.
by rewrite (natural op').
Qed.

Definition psi (op' : E ~> M) : operation E M :=
  Natural.Pack (@Natural.Class _ _ _ (natural_psi op')).

Lemma algebraic_psi (op' : E ~> M) : algebraicity (psi op').
Proof.
move=> A B g t.
rewrite bindE /Bind.
rewrite -(compE (M # g)).
rewrite compA.
rewrite /=.
rewrite -[in X in _ = Join X]compE.
rewrite -[in RHS](natural op').
transitivity (Join ((M # (Join \o (M # g))) (op' (Monad.m M A) t))) => //.
rewrite -[in X in Join X = _]compE.
rewrite (natural Monad.Exports.Join).
rewrite functor_o.
rewrite -[in RHS]FCompE.
rewrite -[RHS]compE.
rewrite [in RHS]compA.
by rewrite joinA.
Qed.
End psi.
Section phi.
Variables (E : functor) (M : monad).

Definition phi_g (op : operation E M) : E ~~> M := fun X => op X \o (E # Ret _).

Lemma natural_phi (op : operation E M) : naturality E M (phi_g op).
Proof.
move=> A B h; rewrite /phi_g.
rewrite compA.
rewrite (natural op).
rewrite -compA.
rewrite -[in RHS]compA.
congr (_ \o _).
rewrite /=.
rewrite -2!(functor_o E).
rewrite (natural Ret).
by rewrite FIdf.
Qed.

Definition phi (op : operation E M) : E ~> M :=
  Natural.Pack (@Natural.Class _ _ _ (natural_phi op)).
End phi.
Section bijection.
Variables (E : functor) (M : monad).

Lemma psiK (op : E ~> M) A : phi (psi op) A = op A.
Proof.
rewrite /= /phi_g /psi /psi_g /= boolp.funeqE => m /=.
rewrite -(compE (op _)) -(natural op) -(compE Join).
by rewrite compA joinMret.
Qed.

Lemma phiK (op : aoperation E M) A : psi (phi op) A = op A.
Proof.
rewrite /psi /phi /= /psi_g /phi_g boolp.funeqE => m /=.
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
Variables (E : functor) (M : monad) (op : aoperation E M).
Variables (N : monad) (e : monadM M N).

Definition alifting : E \O N ~~> N := fun X =>
  locked (Join \o e (N X) \o phi op (N X)).

Lemma aliftingE : alifting = psi (natural_of_monadM e \v phi op).
Proof. rewrite /alifting; unlock; by []. Qed.

Lemma natural_alifting : @naturality (E \O N) N alifting.
Proof. rewrite aliftingE; exact: natural_psi. Qed.

Lemma theorem19a : algebraicity alifting.
Proof. by move=> ? ? ? ?; rewrite aliftingE algebraic_psi. Qed.

Lemma theorem19b : lifting_def op e alifting.
Proof.
move=> X /=.
rewrite aliftingE.
rewrite boolp.funeqE.
move=> Y.
rewrite /=.
rewrite /psi_g /=.
rewrite /ntcomp /=.
rewrite /phi_g /=.
rewrite (_ : (E # Ret _) ((E # e X) Y) = (E # (M # e X)) ((E # Ret _) Y)); last first.
  rewrite -(compE (E # Ret _)).
  rewrite -functor_o.
  rewrite -(compE (E # (_ # _))).
  rewrite -functor_o.
  congr (_ Y).
  congr (E # _).
  rewrite (natural Ret).
  by rewrite FIdf.
rewrite (_ : AOperation.m op (Monad.m N X) ((E # (M # e X)) ((E # Ret _) Y)) =
             (M # e X) (AOperation.m op (Monad.m M X) ((E # Ret _) Y))); last first.
  rewrite -(compE (M # e X)).
  by rewrite (natural op).
set tmp := (op _ _ in RHS).
transitivity (e X (Join tmp)); last first.
  rewrite joinE monadMbind.
  rewrite bindE.
  rewrite -(compE _ (M # e X)).
  by rewrite -(natural_monadM e).
rewrite {}/tmp.
congr (e X _).
rewrite -[in LHS](phiK op).
rewrite -(compE Join).
rewrite -/(psi_g op _).
transitivity ((@psi _ _ op) _ ((E # Ret _) Y)); last by [].
by [].
Qed.

End theorem19.

Section examples_of_lifting.

Section state_errorT.
Variable (S Z : Type).
Let M : monad := ModelState.state S.
Let erZ : monadT := errorT Z.

Let lift_getX : (StateOps.get_fun S) \O (erZ M) ~~> (erZ M) :=
  alifting (get_aop S) (LiftT erZ M).

Goal forall X (k : S -> erZ M X), lift_getX k = StateOps.get k :> erZ M X.
move=> X0 k.
by rewrite /lift_getX aliftingE.
Abort.

Goal lift_getX (Ret _) = @liftX  _ _ _ (@ModelState.get S).
Proof.
by rewrite /lift_getX aliftingE.
Abort.

End state_errorT.

Section continuation_stateT.
Variable (r S : Type).
Let M : monad := ModelCont.t r.
Let stS : monadT := stateT S.

Let lift_acallccS : (ContOps.acallcc_fun r) \O (stS M) ~~> (stS M) :=
  alifting (callcc_aop r) (LiftT stS M).

Goal forall A (f : (stS M A -> r) -> stS M A),
  lift_acallccS f = (fun s k => f (fun m => uncurry m (s, k)) s k) :> stS M A.
move=> A f.
by rewrite /lift_acallccS aliftingE.
Abort.

Definition usual_callccS A B (f : (A -> stS M B) -> stS M A) : stS M A :=
  fun s k => f (fun x _ _ => k (x, s)) s k.

Lemma callccS_E A B f : lift_acallccS
    (fun k : stS M A -> r =>
       f (fun x => (fun (_ : S) (_ : B * S -> r) => k (@Ret (stS M) A x)) : stS M B)) =
  usual_callccS f.
Proof. by rewrite /lift_acallccS aliftingE. Qed.

End continuation_stateT.

End examples_of_lifting.
