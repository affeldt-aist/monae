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

Section monad_morphism.
Variable S : UU0.

Inductive effect : UU0 -> UU0 :=
| Get : effect S
| Put : S -> effect unit.

Definition freer_get : freer effect S :=
  @Impure _ _ S Get Ret.

Definition freer_put (s : S) : freer effect S :=
  Impure (Put s) (fun=> Ret s).

Variable M : stateMonad S.

Definition denote_effect (A V : UU0)
    (eff : effect V) (k : V -> M A) : M A :=
  get >>= (fun s => k
  match eff with
  | Get => s
  | Put s' => (fun=> tt) s'
  end).

Definition freer_effect := freer effect.

HB.instance Definition _ := Monad.on freer_effect.

Definition e : freer_effect ~~> M :=
  fun T => freer_fold Ret (@denote_effect T).

Let monadMret : MonadMLaws.ret e.
Proof. by move=> T; exact/boolp.funext. Qed.

Lemma test (T U : UU0) (m : freer effect T) g
    (h := denote_effect)
(*    (h : forall U V : UU0, effect V -> (V -> M U) -> M U)*) :
  freer_fold Ret (h U) (m >>= g) =
  freer_fold Ret (h T) m >>=
  (freer_fold Ret (h U) \o g).
Proof.
(*rewrite fold_bind/=.
elim: m => //= [t|].
  by rewrite bindretf.
move=> A eff f ih.*)
elim: m => /= [t|V eff f ih].
  by rewrite !bindretf.
transitivity (
  h U V eff
    (fun v : V => freer_fold Ret (h U) ((f v) >>= g))
) => //.
rewrite (_ : (fun v : V => freer_fold Ret (h U) (f v >>= g)) =
  (fun v => freer_fold Ret (h T) (f v) >>= (freer_fold Ret (h U) \o g))); last first.
  apply/boolp.funext => u.
  by rewrite ih.
rewrite /=.
rewrite /h/=.
destruct eff => //=.
rewrite /denote_effect /=.
rewrite !bindA.
by bind_ext.
by rewrite !bindA.
Qed.

Let monadMbind : MonadMLaws.bind e.
Proof.
move=> T U; elim=> /= [t f|V eff f ih g].
  by rewrite /e/= !bindretf.
rewrite /e/=.
rewrite !bindA.
rewrite {1}/denote_effect/=.
bind_ext => s.
destruct eff.
  by rewrite test//.
by rewrite test//.
Qed.

HB.instance Definition _ := isMonadM_ret_bind.Build freer_effect M
  e monadMret monadMbind.

End monad_morphism.
