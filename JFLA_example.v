From mathcomp Require Import all_ssreflect.
From mathcomp Require Import finmap.
From mathcomp Require boolp.
From mathcomp Require Import classical_sets.
From infotheo Require convex_choice classical_sets_ext.
Require Import monae_lib monad fail_monad state_monad trace_monad.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.

(* Morphisme de monade *)
Module monadM.
Section monadm.
Variables (M N : monad).
(* Loi pour le morphisme de monade, Jaskelioff 2009 *)
Record class_of (e : M ~~> N) := Class {
  _ : forall A, @RET _ A = e _ \o Ret;
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
Lemma monadMret : forall A, @RET _ A = f _ \o Ret.
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
have <- : Join ((M # (Ret \o h)) m) = (M # h) m.
  by rewrite functor_o [LHS](_ : _ = (Join \o M # Ret) ((M # h) m)) // joinMret.
move: (@monadMbind M N f A B m (Ret \o h)); rewrite 2!bindE => ->.
rewrite (_ : (fun a => f _ ((Ret \o h) a)) = Ret \o h); last first.
  by rewrite [in RHS](monadMret f).
rewrite [RHS](_ : _ = (Join \o (N # Ret \o N # h)) (f _ m)); last first.
  by rewrite compE functor_o.
by rewrite compA joinMret.
Qed.
End monadM_lemmas.

Definition natural_of_monadM (M N : monad) (f : monadM M N) : M ~> N :=
  Natural.Pack (natural_monadM f).

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

Local Open Scope monae_scope.

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

Definition _m : Type -> Type :=
  fun A => S -> {fset (convex_choice.choice_of_Type A * convex_choice.choice_of_Type S)}.

Let ret' := fun A (a : A) s =>
  [fset (a : convex_choice.choice_of_Type A, s : convex_choice.choice_of_Type S)].

Let bind := fun A B (m : _m A)
  (f : A -> S -> {fset (convex_choice.choice_of_Type B * convex_choice.choice_of_Type S)}) =>
  fun s => \bigcup_(i <- (fun x : [choiceType of convex_choice.choice_of_Type A *
                                           convex_choice.choice_of_Type S] => f x.1 x.2) @` (m s))
                 i.

Definition map A B (f : A -> B) (m : _m A) : _m B :=
  bind m (@ret' _ \o f).

Lemma map_id : FunctorLaws.id map.
Proof.
move=> A; rewrite /map boolp.funeqE => m.
rewrite /bind boolp.funeqE => s.
rewrite compfid big_imfset /=; last first.
  by move=> [a0 s0] [a1 s1] /= _ _ /fset1_inj.
rewrite /ret'; apply/fsetP => /= -[a0 s0].
apply/idP/idP.
  case/(@bigfcupP _ _ (m s)) => /= -[a1 s1].
  rewrite andbT => H1 /=.
  by move/fset1P => ->.
move=> H0.
apply/(@bigfcupP _ _ (m s)).
exists (a0, s0) => //.
by rewrite andbT.
by apply/fset1P.
Qed.

Lemma map_comp : FunctorLaws.comp map.
move=> A B C g h.
rewrite /map /bind boolp.funeqE => m.
rewrite boolp.funeqE => s /=.
apply/fsetP => /= -[c0 s0].
apply/idP/idP.
  case/bigfcupP => /= x.
  rewrite andbT => /imfsetP /= -[[a1 s1] H1] ->{x} /=.
  rewrite /ret' => /fset1P [->{c0} ->{s0}].
  apply/bigfcupP => /=.
  eexists; last exact/fset1P.
  rewrite andbT.
  apply/imfsetP => /=.
  exists ((h a1), s1).
  apply/bigfcupP => /=.
  eexists; last exact/fset1P.
  rewrite andbT.
  apply/imfsetP => //=.
  eexists.
  exact: H1.
  by [].
  by [].
case/bigfcupP => /= x.
rewrite andbT.
case/imfsetP => /= -[b1 s1].
move/bigfcupP => /= -[bs].
rewrite andbT.
move/imfsetP => /= [[a2 s2]] H2 ->{bs} /= /fset1P -[->{b1} ->{s1}] ->{x}.
move/fset1P => [->{c0} ->{s0}].
apply/bigfcupP => /=.
eexists; last exact/fset1P.
rewrite andbT.
by apply/imfsetP; exists (a2, s2).
Qed.

Definition functor := Functor.Pack (Functor.Class map_id map_comp).

Lemma naturality_ret' : naturality FId functor ret'.
Proof.
move=> A B h; rewrite /ret' boolp.funeqE => a; rewrite boolp.funeqE => s.
by rewrite /functor /Fun /map /bind /= imfset_set1 /= big_seq_fset1.
Qed.

Definition ret : FId ~> functor := Natural.Pack naturality_ret'.

Program Definition t := @Monad_of_ret_bind functor ret bind _ _ _.

Section fail.
Variable S : choiceType.
Program Definition _fail : failMonad := @MonadFail.Pack _
  (@MonadFail.Class _ (Monad.class (t S))
    (@MonadFail.Mixin _ (fun (A : Type) (_ : S) => fset0) _)).
Next Obligation.
move=> A B g; rewrite boolp.funeqE => s; apply/fsetP => x; rewrite inE BindE; apply/negbTE.
apply/bigfcupP'; case => /= x0 /imfsetP[/= sa].
by rewrite (@in_fset0 [choiceType of convex_choice.choice_of_Type A * convex_choice.choice_of_Type S]).
Qed.