From HB Require Import structures.
From mathcomp Require Import all_ssreflect classical_sets.
Require Import monad_lib hierarchy.

(* WIP
   references:
   - Swierstra, Baanen, A Predicate Transformer Semantics for Effects
   - Schrijvers, Pirog, Wu, Jaskelioff, Monad transformers and Modular Algebraic Effects: What Binds Them Together. Haskell'19
   - Seynaeve, Pauwels, Schrijvers, State will do, TFP 2020
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive Free (C : Type) (R : C -> Type) (a : Type) : Type :=
| Pure : a -> Free R a
| Step : forall c : C, (R c -> Free R a) -> Free R a.
Arguments Pure {C} {R} {a} _.
Arguments Step {C} {R} {a} _ _.

Section monadfree.
Variables (C : Type) (R : C -> Type).
Definition freeMonad : Type -> Type := Free R.
Local Notation M := freeMonad.
Fixpoint actm X Y (f : X -> Y) (m : Free R X) : Free R Y :=
  match m with
  | Pure x => Pure (f x)
  | Step c k => Step c (fun r => actm f (k r))
  end.
Lemma map_id : FunctorLaws.id actm.
Proof.
move=> X; rewrite boolp.funeqE; elim => //= c k ih; congr (Step _ _).
rewrite boolp.funeqE => rc /=; exact: ih.
Qed.
Lemma map_comp : FunctorLaws.comp actm.
Proof.
move=> X Y Z g h; rewrite boolp.funeqE; elim => // c k ih /=; congr (Step _ _).
rewrite boolp.funeqE => r; exact: ih.
Qed.
(*HB.instance Definition _ (* func *) := isFunctor.Build acto map_id map_comp.*)

Local Open Scope monae_scope.
Definition ret : idfun ~~> M := fun A (a : A) => Pure a.

(*Lemma naturality_ret : naturality idfun acto ret.
Proof. by move=> A B h /=; rewrite boolp.funeqE. Qed.*)

(*HB.instance Definition _ (*ret*) (*: idfun ~> acto*) :=
  isNatural.Build idfun acto ret naturality_ret.*)

Fixpoint bind A B (ma : M A) (f : A -> M B) :=
  match ma with
  | Pure a => f a
  | Step c k => Step c (fun r => bind (k r) f)
  end.
Lemma left_neutral : @BindLaws.left_neutral M bind ret.
Proof. by []. Qed.
Lemma right_neutral : @BindLaws.right_neutral M bind ret.
Proof.
move=> A; elim => // c k ih /=; congr (Step _ _).
rewrite boolp.funeqE => rc; exact: ih.
Qed.
Lemma associative : @BindLaws.associative M bind.
Proof.
move=> X Y Z; elim => // c k /= ih f g; congr Step.
by rewrite boolp.funeqE => rc /=; rewrite ih.
Qed.
HB.instance Definition _ :=
  @isMonad_ret_bind.Build M ret bind left_neutral right_neutral associative.

End monadfree.

Module freeFail.
Inductive Cmd := Abort : Cmd.
Definition Res (c : Cmd) : Type := let Abort := c in False.
Definition t : monad := freeMonad Res.
Definition abort (A : pointedType) := Step Abort (fun=> Ret (@point A) : t _).
Definition hdl (A : pointedType) (m : t A) :=
  match m with
  | Pure a => a
  | Step Abort _ => point
  end.
End freeFail.

Require Import fail_lib.

HB.instance Definition nat_pointedType := isPointed.Build nat O.

Section freefastprod.
Local Open Scope mprog.
Fixpoint freefastprod (s : seq nat) : freeFail.t nat :=
  match s with
  | [::] => Ret 1
  | O :: _ => freeFail.abort nat
  | h :: t => fmap (muln^~ h) (freefastprod t)
end.
Example is6 :  freeFail.hdl (freefastprod [:: 1; 2; 3]) = 6.
Proof. by []. Qed.
Example isO :  freeFail.hdl (freefastprod [:: 1; O; 3; 4]) = O.
Proof. by []. Qed.
End freefastprod.

Module freeState.
Section free_state.
Variable S : Type.
Inductive Cmd := Get | Put : S -> Cmd.
Definition Res (c : Cmd) :=
  match c with
  | Get => S
  | Put _ => unit
  end.
Definition t : monad := freeMonad Res.
Definition get : t S := Step Get (Ret : S -> t S).
Definition put : S -> t unit := fun s => Step (Put s) (fun=> Ret tt : t unit).
Fixpoint hdl A (m : t A) (s : S) : A * S :=
  match m with
  | Pure a => (a, s)
  | Step Get k => hdl (k s) s
  | Step (Put s) k => hdl (k tt) s
  end.
End free_state.
Module Exports.
Notation fState := t.
Arguments get {S}.
Notation fget := get.
Arguments put {S}.
Notation fput := put.
End Exports.
End freeState.
Export freeState.Exports.

Section state_example.
Local Open Scope monae_scope.
Definition incr' : fState nat unit := fget >>= (fput \o (fun n => n.+1)).
Goal freeState.hdl incr' 5 = (tt, 6).
Proof. by []. Qed.
Goal freeState.hdl (incr' >> fget) 5 = (6, 6).
Proof. by []. Qed.
End state_example.

Module MonadRunFreeState.
Local Open Scope monae_scope.
Record mixin_of S := Mixin {
  run : forall A, fState S A -> S -> A * S ;
  r1 : forall A (a : A) s, run (Pure a) s = (a, s) ;
  r2 : forall A B (m : fState S A) (f : A -> fState S B) s,
    run (m >>= f) s = let: (a, s') := run m s in run (f a) s';
  r3 : forall A (k : freeState.Res (freeState.Get S) -> Free (@freeState.Res S) A) s,
    run (Step (freeState.Get S) k) s = run (k s) s ;
  r4 : forall A (k : unit -> Free (@freeState.Res S) A) s' s,
    run (Step (freeState.Put s) k) s' = run (k tt) s }.
Structure t S := Pack { sort : Type ; class : mixin_of S }.
Module Exports.
Definition fRun S (M : t S) : forall A, fState S A -> S -> A * S :=
  let: Pack _ (Mixin x _ _ _ _) := M in x.
Arguments fRun {S} _ {A} : simpl never.
Notation runFreeStateMonad := t.
End Exports.
End MonadRunFreeState.
Export MonadRunFreeState.Exports.

Section monadrunfreestate_lemmas.
Local Open Scope monae_scope.
Variables (S : Type) (M : runFreeStateMonad S).
Lemma runfreestate_Pure A (a : A) s : fRun M (Pure a) s = (a, s).
Proof. by case: M => ? []. Qed.
Lemma runfreestate_bind A B (m : fState S A) (f : A -> fState S B) s :
  fRun M (m >>= f) s = let: (a, s') := fRun M m s in fRun M (f a) s'.
Proof. by case: M => ? []. Qed.
Lemma runfreestate_Get A
  (k : freeState.Res (freeState.Get S) -> Free (@freeState.Res S) A) s :
  fRun M (Step (freeState.Get S) k) s = fRun M (k s) s.
Proof. by case: M => ? []. Qed.
Lemma runfreestate_Put A (k : unit -> Free (@freeState.Res S) A) s' s :
  fRun M (Step (freeState.Put s) k) s' = fRun M (k tt) s.
Proof. by case: M => ? []. Qed.
End monadrunfreestate_lemmas.

Section example.
Variable M : runFreeStateMonad nat.

Goal fRun M incr' 0 = (tt, 1).
rewrite /incr'.
rewrite runfreestate_bind /=.
rewrite /get.
rewrite runfreestate_Get /=.
rewrite runfreestate_Pure /=.
rewrite runfreestate_Put /=.
by rewrite runfreestate_Pure /=.
Abort.

End example.

Module freeNondet.
Inductive Cmd : Type := Fail | Choice.
Definition Res (c : Cmd) : Type :=
  match c with
  | Fail => False
  | Choice => bool
  end.
Definition t : monad := freeMonad Res.
Definition fail (A : pointedType) := @Step _ _ A Fail (fun _ => Ret point : t _).
Definition choice A (m1 m2 : t A) : t A :=
  Step Choice (fun b : bool => if b then m1 else m2).
Fixpoint hdl A (m : t A) :=
  match m with
  | Pure x => [:: x]
  | Step Fail _ => [::]
  | Step Choice k => hdl (k true) ++ hdl (k false)
  end.
End freeNondet.

Module MonadNondetRun.
Local Open Scope monae_scope.
Record mixin_of (M : nondetMonad) (Fail : forall X, M X)
  (Alt : forall X, M X -> M X -> M X) : Type := Mixin {
  run : forall A : Type, M A -> seq A ;
  _ : forall (A : Type) (a : A), run (Ret a) = [:: a] ;
  _ : forall (A B : Type) (m : M A) (f : A -> M B),
      run (m >>= f) =
      let: a' := run m in flatten (map (@run B \o f) a') ;
  _ : forall (A : Type), run (@Fail A) = [::] ;
  _ : forall (A : Type) (m1 m2 : M A), run (Alt _ m1 m2) = run m1 ++ run m2}.
Record class_of (m : Type -> Type) := Class {
  base : MonadNondet.class_of m ;
  mixin_nondetRun : @mixin_of (MonadNondet.Pack base)
    (@Fail (MonadNondet.Pack base))
    (@Alt (alt_of_nondet (MonadNondet.Pack base))) }.
Structure t := Pack { m : Type -> Type ; class : class_of m }.
Definition baseType (M : t) := MonadNondet.Pack (base (class M)).
Module Exports.
Notation nondetRunMonad := t.
Coercion baseType : nondetRunMonad >-> nondetMonad.
Canonical baseType.
End Exports.
End MonadNondetRun.
Export MonadNondetRun.Exports.

Section simulation.
Variable A : Type.
Fail Inductive prog := Prog : State (seq A * seq prog) unit -> prog.
End simulation.
