Require Import ssreflect ssrmatching ssrfun ssrbool.

From mathcomp Require Import eqtype ssrnat seq path div choice fintype tuple.
From mathcomp Require Import finfun bigop.
From mathcomp Require boolp.
From monae Require Import monad.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* - monad morphism

   - monad transformer
     - state monad transformer
     - exception monad transformer
     - continuation monad transformer

    - sigma operations
     - state sigma operation (get)

    - examples
       - usage of continuation monad transformer
*)

(* modular monad transformer, Jaskelioff ESOP 2009 *)

Module monadM.
Section monad_morphism.
Variables M N : monad.
Record t := mk {
  e : M ~> N ;
  ret : forall {A} (a : A), Ret a = e (Ret a) ;
  bind : forall {A B} (m : M A) (f : A -> M B),
    e (m >>= f) = e m >>= (fun a => e (f a))
}.
End monad_morphism.
Module Exports.
Notation monadM := t.
Definition coercion := e.
Coercion coercion : monadM >-> Funclass.
End Exports.
End monadM.
Export monadM.Exports.

Section monadM_lemmas.
Variables M N : monad.
Lemma monadMret (f : monadM M N) : forall {A} (a : A), Ret a = f _ (Ret a).
Proof. by case: f. Qed.
Lemma monadMbind (f : monadM M N) : forall {A B} (m : M A) (h : A -> M B),
  f _ (m >>= h) = f _ m >>= (fun a => f _ (h a)).
Proof. by case: f. Qed.
End monadM_lemmas.

Section monad_morphism.
Variables M N : monad.

Lemma natural_monad_morphism (f : monadM M N) : naturalP M N f.
Proof.
move=> A B h; rewrite boolp.funeqE => m /=.
have <- : Join ((M # (Ret \o h)) m) = (M # h) m.
  by rewrite functor_o [LHS](_ : _ = (Join \o M # Ret) ((M # h) m)) // joinMret.
move: (@monadMbind M N f A B m (Ret \o h)); rewrite 2!bindE => ->.
rewrite (_ : (fun a => f _ ((Ret \o h) a)) = Ret \o h); last first.
  by rewrite boolp.funeqE => y; rewrite -monadMret.
rewrite [RHS](_ : _ = (Join \o (N # Ret \o N # h)) (f _ m)); last first.
  by rewrite compE functor_o.
by rewrite compA joinMret.
Qed.

End monad_morphism.

Module MonadT.
Section monad_transformer.
Record t := mk {
  T : monad -> monad ;
  retT : forall (M : monad), FId ~> (T M);
  bindT : forall (M : monad) A B, (T M) A -> (A -> (T M) B) -> (T M) B ;
  liftT : forall (M : monad), monadM M (T M) }.
End monad_transformer.
Module Exports.
Notation monadT := t.
Coercion T : monadT >-> Funclass.
End Exports.
End MonadT.
Export MonadT.Exports.

From mathcomp Require Import boolp.

Section state_monad_transformer.

Local Obligation Tactic := idtac.

Variables (S : Type) (M : monad).

Definition MS := fun A => S -> M (A * S)%type.

Definition retS A (a : A) : MS A :=
  fun (s : S) => Ret (a, s) : M (A * S)%type.

Definition bindS A B (m : MS A) f := (fun s => m s >>= uncurry f) : MS B.

Program Definition estateMonadM : monad :=
  @Monad_of_ret_bind MS retS bindS _ _ _.
Next Obligation.
by move=> A B a f; rewrite /bindS funeqE => s; rewrite bindretf.
Qed.
Next Obligation.
move=> A m; rewrite /bindS funeqE => s.
rewrite -[in RHS](bindmret (m s)); by bind_ext; case.
Qed.
Next Obligation.
move=> A B C m f g; rewrite /bindS funeqE => s.
by rewrite bindA; bind_ext; case.
Qed.

Definition liftS A (m : M A) : estateMonadM A :=
  fun s => @Bind M _ _ m (fun x => @Ret M _ (x, s)).

Program Definition stateMonadM : monadM M estateMonadM :=
  @monadM.mk _ _ liftS _ _.
Next Obligation.
by move=> A a; rewrite /liftS funeqE => s; rewrite bindretf.
Qed.
Next Obligation.
move=> A B m f; rewrite /liftS funeqE => s.
rewrite [in RHS]/Bind [in RHS]/Join /= /Monad_of_ret_bind.join /= /bindS !bindA.
bind_ext => a; by rewrite !bindretf.
Qed.

End state_monad_transformer.

Definition statemonad_transformer S : monadT :=
  @MonadT.mk (estateMonadM S) (@retS S) (@bindS S) (@stateMonadM S).

Section exception_monad_transformer.

Local Obligation Tactic := idtac.

Variables (Z : Type) (* the type of exceptions *) (M : monad).

Definition MX := fun X => M (Z + X)%type.

Definition retX X x : MX X := Ret (inr x).

Definition bindX X Y (t : MX X) (f : X -> MX Y) : MX Y :=
  t >>= fun c => match c with inl z => Ret (inl z) | inr x => f x end.

Program Definition eexceptionMonadM : monad :=
  @Monad_of_ret_bind MX retX bindX _ _ _.
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
  @monadM.mk _ _ liftX _ _.
Next Obligation. by move=> A a; rewrite /liftX bindretf. Qed.
Next Obligation.
move=> A B m f; rewrite /liftX [in RHS]/Bind [in RHS]/Join /=.
rewrite  /Monad_of_ret_bind.join /= /bindX !bindA.
bind_ext => a; by rewrite !bindretf.
Qed.

End exception_monad_transformer.

Definition exceptionmonad_transformer Z : monadT :=
  @MonadT.mk (eexceptionMonadM Z) (@retX Z) (@bindX Z) (@exceptionMonadM Z).

Section continuation_monad_tranformer.

Local Obligation Tactic := idtac.

Variables (r : Type)  (M : monad).

Definition MC : Type -> Type := fun A => (A -> M r) -> M r %type.

Definition retC A (a : A) : MC A :=
  fun cont => cont a.

Definition bindC A B (m : MC A) f : MC B :=
  fun cont => m (f^~ cont).

Program Definition econtMonadM : monad :=
  @Monad_of_ret_bind MC retC bindC _ _ _.
Next Obligation. by []. Qed.
Next Obligation. by []. Qed.
Next Obligation. by []. Qed.

Definition liftC A (x : M A) : econtMonadM A :=
  fun cont => x >>= cont.

Program Definition contMonadM : monadM M econtMonadM  :=
  @monadM.mk _ _ liftC  _ _.
Next Obligation.
move => A a.
rewrite /liftC funeqE => cont.
by rewrite !bindretf.
Qed.
Next Obligation.
move => A B m f.
rewrite /liftC funeqE => cont.
by rewrite !bindA.
Qed.

End continuation_monad_tranformer.

Definition continuationmonad_transformer R : monadT :=
  @MonadT.mk (econtMonadM R) (@retC R) (@bindC R) (@contMonadM R).

Require Import state_monad monad_model.

Definition callcc R M A B (f : (A -> continuationmonad_transformer R M B) -> continuationmonad_transformer R M A) : continuationmonad_transformer R M A :=
  fun cont => f (fun x _ => cont x) cont. (*NB(rei): similar def in monad_model.*)

Definition abort R r (m : monad) A : continuationmonad_transformer R m A := fun (k : A -> m R) => Ret r.
Arguments abort {R} _ {m} {A}.

Section examples_continuation_monad_transformer.

Local Notation CMT := (@continuationmonad_transformer).

Definition foreach (m : monad) (items : list nat) (body : nat -> CMT unit m unit) : m unit :=
  foldr
    (fun x next => (body x) (fun _ => next))
    (Ret tt)
    items.

Fixpoint for_loop (m : monad) (it min : nat) (body : nat -> CMT unit m unit) : m unit :=
  if it <= min then Ret tt
  else if it is it'.+1 then
      (body it') (fun _ => for_loop it' min body)
      else Ret tt.

Section for_loop_lemmas.
Variable m : monad.
Implicit Types body : nat -> (continuationmonad_transformer unit) m unit.

Lemma loop0 : forall i body, for_loop i i body = Ret tt.
Proof.
move => i body /=.
by case i => //= n; rewrite ltnS leqnn.
Qed.

Lemma loop1 : forall i j body, for_loop (i.+1 + j) i body =
     (body (i + j)) (fun _ => for_loop (i + j) i body).
Proof.
move => i j body /=.
by case : ifPn ; rewrite ltnNge leq_addr.
Qed.

Lemma loop2 : forall i j body ,
    body (i + j) = abort tt -> for_loop (i + j).+1 i body = Ret tt.
Proof.
move => i j body Hbody /=.
case : ifPn => Hcond.
reflexivity.
by rewrite Hbody /= /abort.
Qed.

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

End for_loop_lemmas.
(* TODO : instantiate with RunStateMonad *)

Let ms : stateMonad nat := ModelState.state nat.

Let sum n : ms unit := for_loop n O
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

Example sum_from_0_to_10 : ms unit :=
  foreach (iota 100 0) (fun i => if i > 90 then
                            abort tt
                          else
                            liftC (Get >>= (fun z => Put (z + i)))).

Let CM := @continuationmonad_transformer^~ ModelMonad.identity.
Let callcc_i := @callcc^~ ModelMonad.identity.
Goal forall R, @ModelCont.callcc R = @callcc_i R.
by []. Qed.

Definition break_if_none (m : monad) (break : _) (acc : nat) (x : option nat) : m nat :=
  if x is Some x then Ret (x + acc) else break acc.

Definition sum_until_none (xs : seq (option nat)) : CM nat nat :=
  callcc (fun break : nat -> CM nat nat => foldM (break_if_none break) 0 xs).

Compute (sum_until_none [:: Some 2; Some 6; None; Some 4]).

(* Definition liftM A B {m : monad} (f: A -> B) (ma: m A): m B := *)
(*  ma >>= (fun a => Ret (f a)). *)

Definition calcul : CM nat nat :=
  fmap (fun x => 8 + x) (callcc_i (fun k : (_ -> CM nat _) => (k 5) >>= (fun y => Ret (y + 4)))).

Compute calcul.

End examples_continuation_monad_transformer.

Module Operation.
Record t (E : functor) (M : monad) := mk {
  f :> E \O M ~> M ;
  H : naturalP (E \O M) M f }.
End Operation.
Notation operation := Operation.t.
Coercion Operation.f : operation >-> Funclass.

Section sigma_operations.
(* TODO: rewrite ModelState.get,put,callcc with get_op, etc.? *)

Section get_functor.
Variable S : Type.
Definition get_act_obj X := S -> X.
Definition get_act_mor X Y (f : X -> Y) (t : get_act_obj X) : get_act_obj Y := fun s => f (t s).
Program Definition get_fun := Functor.Pack (@Functor.Class get_act_obj get_act_mor _ _ ).
Next Obligation. by move=> A; rewrite /get_act_mor funeqE. Qed.
Next Obligation. by move=> A B C g h; rewrite /get_act_mor funeqE. Qed.
End get_functor.

Definition get_op S A (k : S -> ModelMonad.acto S A) : ModelMonad.acto S A := fun s => k s s.

Program Definition get_operation S : operation (get_fun S) (ModelMonad.state S) :=
  @Operation.mk _ _ (@get_op S) _.
Next Obligation.
move=> A B h; rewrite boolp.funeqE => /= m /=.
rewrite boolp.funeqE => s.
by rewrite FCompE Monad_of_ret_bind.fmapE.
Qed.

Lemma getE S : @ModelState.get S = @get_op S S (@Ret (ModelMonad.state S) S).
Proof. by []. Qed.

Section put_functor.
Variable S : Type.
Definition put_act_obj X := (S * X)%type.
Definition put_act_mor X Y (f : X -> Y) (sx : put_act_obj X) : put_act_obj Y := (sx.1, f sx.2).
Program Definition put_fun := Functor.Pack (@Functor.Class put_act_obj put_act_mor _ _ ).
Next Obligation. by move=> A; rewrite /put_act_mor funeqE; case. Qed.
Next Obligation. by move=> A B C g h; rewrite /put_act_mor funeqE. Qed.
End put_functor.

Definition put_op S A (s : S) (m : ModelMonad.acto S A) : ModelMonad.acto S A :=
  fun _ => m s.

Program Definition put_operation S : operation (put_fun S) (ModelMonad.state S) :=
  @Operation.mk _ _ (fun A => uncurry (@put_op S A)) _.
Next Obligation.
move=> A B h.
rewrite boolp.funeqE => /=; case => s m /=.
rewrite boolp.funeqE => s'.
by rewrite 2!Monad_of_ret_bind.fmapE.
Qed.

Lemma putE S : @ModelState.put S = fun s => put_op s (@Ret (ModelMonad.state S) _ tt).
Proof. by []. Qed.

Section callcc.

Let C r := ModelCont.contM r.
Definition callcc_op r A (f : (C r A -> r) -> C r A) : C r A := fun k => f (fun m => m k) k.

Section callcc_functor.
Definition callcc_act_obj r A := (A -> r) -> A.
Definition callcc_act_mor r X Y (f : X -> Y) (t : callcc_act_obj r X) : callcc_act_obj r Y :=
  fun (g : Y -> r) => f (t (fun x => g (f x))).
Program Definition callcc_fun r := Functor.Pack (@Functor.Class (callcc_act_obj r) (@callcc_act_mor r) _ _ ).
Next Obligation. by move=> A; rewrite /callcc_act_mor funeqE. Qed.
Next Obligation. by move=> A B D g h; rewrite /callcc_act_mor funeqE. Qed.
End callcc_functor.

Program Definition callcc_operation r : operation (callcc_fun r) (ModelCont.contM r) :=
  @Operation.mk _ _ (@callcc_op r) _.
Next Obligation.
move=> A B h.
rewrite boolp.funeqE => /= m /=.
rewrite boolp.funeqE => g.
by rewrite Monad_of_ret_bind.fmapE.
Qed.

Lemma callccE r A B (f : (A -> C r B) -> C r A) :
  ModelCont.callcc f = callcc_op (fun k => f (fun x _ => k (@Ret _ _ x))).
Proof. by []. Qed.

End callcc.

End sigma_operations.

Module Lifting.
Section lifting.
Variables (E : functor) (M : monad) (op : operation E M).
Variables (N : monad) (e : monadM M N).
Record t := mk {
  f :> operation E N ;
  H : forall X, e X \o op X = @f X \o (E # e X) }.
End lifting.
End Lifting.

Module LiftingT.
Section liftingt.
Variables (E : functor) (M : monad) (op : operation E M).
Variable (T : monadT).
Definition t := Lifting.t op (@MonadT.liftT T M).
Definition mk H := @Lifting.mk _ _ op _ (@MonadT.liftT T M) H.
End liftingt.
End LiftingT.

(* Algebraic operation *)
Module AOperation.
Section aoperation.
Variables (E : functor) (M : monad).
Record t := mk {
  op :> operation E M ;
  H : forall A B (f : A -> M B) (t : E (M A)),
    (op A t >>= f) = op B ((E # (fun m => m >>= f)) t)
}.
End aoperation.
End AOperation.
Notation aoperation := AOperation.t.

From mathcomp Require Import classical_sets.

Local Open Scope classical_set_scope.

Module Tnat.
Record t (M N : functor) := mk {
  f : M ~> N ;
  H : naturalP _ _ f }.
End Tnat.
Notation tnat := Tnat.t.

Section proposition17.
Variables (E : functor) (M : monad).

Definition phi (op : aoperation E M) : tnat E M.
Admitted.

Definition psi (op' : tnat E M) : aoperation E M.
case: op' => op' Hop'.
have op : operation E M.
  have @f : E \O M ~> M.
    move=> X m.
    apply: (@Join M X \o @op' (M X)).
    exact: m.
  refine (@Operation.mk _ _ f _).
  move=> A B h.
  admit.
refine (@AOperation.mk _ _ op _).
move=> A B f  t.
admit.
Admitted.

End proposition17.
