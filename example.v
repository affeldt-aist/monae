From mathcomp Require Import all_ssreflect.
From mathcomp Require Import finmap.
From mathcomp Require boolp.
From mathcomp Require Import classical_sets.
From infotheo Require convex_choice classical_sets_ext.
Require Import monae_lib monad fail_monad state_monad trace_monad monad_transformer.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.

(* monade identité : ModelMonad.identity *)

(* Section identity.
Local Obligation Tactic := by [].
Definition identity_functor : FId ~> FId := Natural.Pack (@natural_id FId).
Program Definition identity := @Monad_of_ret_bind _ identity_functor
  (fun A B (a : id A) (f : A -> id B) => f a) _ _ _.
End identity. *)

Section maybe_monad_transformer.

Definition ID (A : Type) := A.

Definition retID A (a : A) : ID A := a.

Definition bindID A B (ma : ID A) (f : A -> ID B) : ID B :=
  f ma.

Local Obligation Tactic := idtac.

(*  *)

Inductive option (A : Type) :=
| Some : A -> option A
| None : option A.

Arguments Some [A] _.
Arguments None [A].

Definition optionRet A (a : A) : option A := Some a.
Definition optionBind A B (ma : option A) (f : A -> option B) : option B :=
  match ma with None => None | Some x => f x end.

Definition fail A : option A :=
  None.

Lemma fail_left_zero A B (f : A -> option B) :
  optionBind (@fail A) f = @fail B.
Proof.
rewrite /optionBind /fail.
by [].
Qed.

Variable S : Type.

Definition State (A : Type) := S -> A * S.

(* Arguments State [S]. *)

Definition state_pure A (a : A) : State A := 
  fun s => (a,s).

Definition state_bind A (st_a : State A) B  (f : A -> State B) :=
  fun  s => let (a,s) := st_a s in
            f a s.

Definition putS (x : S) : State unit :=
  fun _ => (tt,x).

Definition getS : State S :=
  fun x => (x,x).

(* Arguments getS _ : assert. *)

Definition runState  {A} (op : State A) : S -> A * S := op.

Variables (M : monad).

Definition maybeX := fun X => M (option X)%type.

Definition retMx X x : maybeX X := Ret (Some x).

Definition bindMx X Y (t : maybeX X) (f : X -> maybeX Y) : maybeX Y :=
  t >>= fun c => match c with None => Ret None | Some x => f x end.

Local Open Scope mprog.
Definition maybeX_map A B (f : A -> B) (m : maybeX A) : maybeX B :=
  fmap (fun x => match x with None => None | Some y => Some (f y) end) m.
Local Close Scope mprog.

Definition maybeT_functor : functor.
apply: (Functor.Pack (@Functor.Class maybeX maybeX_map _ _)).
move=> A; rewrite boolp.funeqE => x.
rewrite /maybeX in x *.
rewrite /maybeX_map.
by rewrite (_ : (fun _ => _) = id) ?functor_id // boolp.funeqE; case.
rewrite /maybeX_map /=.
move=> A B C g h /=.
rewrite boolp.funeqE => x /=.
rewrite -[RHS]compE -functor_o /=; congr (_ # _).
by rewrite boolp.funeqE; case.
Defined.

Lemma naturality_retMx : naturality FId maybeT_functor retMx.
Proof.
move=> A B h; rewrite /retMx boolp.funeqE /= => a.
by rewrite /Fun /= /maybeX_map -[LHS]compE (natural RET).
Qed.

Definition retMx_nat : FId ~> maybeT_functor := Natural.Pack naturality_retMx.

Program Definition eexceptionMonadMx : monad :=
  @Monad_of_ret_bind maybeT_functor retMx_nat bindMx _ _ _.
Next Obligation. by move=> A B a f; rewrite /bindMx bindretf. Qed.
Next Obligation.
move=> A m; rewrite /bindMx -[in RHS](bindmret m); by bind_ext; case.
Qed.
Next Obligation.
move=> A B C m f g; rewrite /bindMx bindA; bind_ext; case => //.
by rewrite bindretf.
Qed.

Definition liftMx X (m : M X) : eexceptionMonadMx X := @Bind M _ _ m (fun x => @RET eexceptionMonadMx _ x).

(* Local Open Scope mprog.
Definition liftMx2 X (m : M X) : eexceptionMonadMx X := fmap Some m.
Local Close Scope mprog. *)

Program Definition exceptionMonadMx : monadM M eexceptionMonadMx :=
  monadM.Pack (@monadM.Class _ _ liftMx _ _).
Next Obligation.
by move=> A; rewrite boolp.funeqE => a; rewrite /liftMx /= bindretf.
Qed.
Next Obligation.
move=> A B m f; rewrite /liftMx [in RHS]/Bind [in RHS]/Join /=.
rewrite  /Monad_of_ret_bind.join /= /bindMx !bindA.
bind_ext => a; by rewrite !bindretf.
Qed.

End maybe_monad_transformer.

Section exception_monad_transformer.

Local Obligation Tactic := idtac.

Variables (Z : Type) (* the type of exceptions *) (M : monad).

Definition MX := fun X => M (Z + X)%type.

Definition retX X x : MX X := Ret (inr x).

Definition bindX X Y (t : MX X) (f : X -> MX Y) : MX Y :=
  t >>= fun c => match c with inl z => Ret (inl z) | inr x => f x end.

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

Lemma naturality_retX : naturality FId exceptionT_functor retX.
Proof.
move=> A B h; rewrite /retX boolp.funeqE /= => a.
by rewrite /Fun /= /MX_map -[LHS]compE (natural RET).
Qed.

Definition retX_nat : FId ~> exceptionT_functor := Natural.Pack naturality_retX.

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

Definition liftX X (m : M X) : eexceptionMonadM X := @Bind M _ _ m (fun x => @RET eexceptionMonadM _ x).

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

Section option.
(* Local Obligation Tactic := by []. *)

Variable S : Type.

Definition optionT := eexceptionMonadMx (monad_model.ModelMonad.State.t S).

Program Definition fail_class := @MonadFail.Class _ _ 
  (@MonadFail.Mixin optionT (fun B => @Ret (@None B)) _).
Next Obligation.
rewrite /BindLaws.left_zero.
(* rewrite /BindLaws.left_zero. *)
(* move => A B g.
simpl.
SearchAbout RET.
SearchAbout ">>=".
rewrite /bindretf.
rewrite /bindretf.
by []. *)
Definition fail := MonadFail.Pack fail_class.
End option.


