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

Local Obligation Tactic := idtac.


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

Section MonadFail.
(* Local Obligation Tactic := by []. *)
(* 
Variable S : Type. *)

Definition optionT := eexceptionMonadMx monad_model.ModelMonad.identity.

Program Definition fail_class := @MonadFail.Class _ _ 
  (@MonadFail.Mixin optionT (fun B => @Ret (@None B)) _).
Next Obligation.
by [].
Defined.
Definition mfail := MonadFail.Pack fail_class.
End MonadFail.




