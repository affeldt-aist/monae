(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2020 monae authors, license: LGPL-2.1-or-later               *)
Ltac typeof X := type of X.

Require Import ssrmatching Reals JMeq.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp Require boolp.
From mathcomp Require Import mathcomp_extra Rstruct reals.
From infotheo Require Import Reals_ext.
From infotheo Require Import realType_ext.
Require Import preamble.
From HB Require Import structures.
Require Import hierarchy monad_transformer.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.

Section free_monad.
Variable F : UU0 -> UU0.

Inductive freer (T : UU0) :=
| Pure : T -> freer T
| Impure : forall U : UU0, F U -> (U -> freer T) -> freer T.

Local Definition freer_ret := Pure.

Local Fixpoint freer_bind (T U : UU0) (m : freer T) (f : T -> freer U) : freer U :=
match m with
| Pure x => f x
| Impure _ n k => Impure n (fun x => freer_bind (k x) f)
end.

Let bindretf : BindLaws.left_neutral freer_bind freer_ret.
Proof. by []. Qed.

Let bindmret : BindLaws.right_neutral freer_bind freer_ret.
Proof. by move=> T; elim => //= *; congr Impure; exact/boolp.funext. Qed.

Let bindA : BindLaws.associative freer_bind.
Proof. by move=> T U V; elim=> //= *; congr Impure; exact/boolp.funext. Qed.

HB.instance Definition _ := @isMonad_ret_bind.Build
  _ freer_ret freer_bind bindretf bindmret bindA.

Let freer_map (T U : UU0) (f : T -> U) m :=
  freer_bind m (fun x => freer_ret (f x)).

Let freer_mapE (T U : UU0) (f : T -> U) : freer # f = @freer_map T U f.
Proof. by []. Qed.

Fixpoint freer_fold (T U : UU0) (f : T -> U)
  (g : forall V : UU0, F V -> (V -> U) -> U) (m : freer T) : U :=
match m with
| Pure x => f x
| Impure _ n k => g _ n (fun v => freer_fold f g (k v))
end.

Lemma fold_bind (X Y Z : UU0) (f : X -> Y)
  (g : forall Z, F Z -> (Z -> Y) -> Y)
  (m : freer Z) (h : Z -> freer X) :
  freer_fold f g (m >>= h) =
  freer_fold (fun z => freer_fold f g (h z)) g m.
Proof.
Admitted.

End free_monad.

Section monad_morphism1.
Variable S : UU0.

Inductive effect : UU0 -> UU0 :=
| Get : effect S
| Put : S -> effect unit.

Definition freer_get : freer effect S :=
  @Impure _ _ S Get Ret.

Definition freer_put (s : S) : freer effect S :=
  Impure (Put s) (fun=> Ret s).

Variable M : stateMonad S.

HB.instance Definition _ := Monad.on (freer effect).

Inductive equiv : forall X : UU0, freer effect X -> freer effect X -> Prop :=
| PutGet : forall (s : S),
    equiv (freer_put s >> freer_get) (freer_put s >> Ret s).

Definition denote_effect (A : UU0) (eff : effect A) : M A :=
  match eff with
  | Get => get
  | Put s => put s
  end.

Definition denote : freer effect ~~> M :=
  fun T => freer_fold Ret (fun V eff => bind (denote_effect eff)).

Let monadMret : MonadMLaws.ret denote.
Proof. by move=> T; exact/boolp.funext. Qed.

Let monadMbind : MonadMLaws.bind denote.
Proof.
move=> T U; elim=> /= [t f|V eff f ih g].
  by rewrite /denote/= !bindretf.
rewrite /denote/=.
rewrite /denote_effect/=.
destruct eff => /=.
  rewrite !bindA.
  bind_ext => s.
  exact: ih.
rewrite !bindA.
bind_ext => -[].
exact: ih.
Qed.

HB.instance Definition _ := isMonadM_ret_bind.Build (freer effect) M
  denote monadMret monadMbind.

Lemma equiv_eq (X : UU0) (m1 m2 : freer effect X) :
   equiv m1 m2 -> denote m1 = denote m2.
Proof.
case=> s.
by rewrite /denote /= -bindA bindmret putget.
(* TODO: put the congruence in the equiv relation,
prove that equiv is an equivalence relation *)
Admitted.

End rel.
