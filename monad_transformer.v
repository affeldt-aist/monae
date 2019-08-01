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
Section monadm.
Variables (M N : monad).
Record class_of (e : M ~~> N) := Class {
  _ : forall A (a : A), Ret a = e _ (Ret a) ;
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
Lemma monadMret A (a : A) : Ret a = f _ (Ret a).
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
  by rewrite boolp.funeqE => y; rewrite -monadMret.
rewrite [RHS](_ : _ = (Join \o (N # Ret \o N # h)) (f _ m)); last first.
  by rewrite compE functor_o.
by rewrite compA joinMret.
Qed.
End monadM_lemmas.

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
  fun (s : S) => Ret (a, s) : M (A * S)%type.

Definition bindS A B (m : MS A) f := (fun s => m s >>= uncurry f) : MS B.

Program Definition estateMonadM : monad :=
  @Monad_of_ret_bind MS retS bindS _ _ _.
Next Obligation.
by move=> A B a f; rewrite /bindS boolp.funeqE => s; rewrite bindretf.
Qed.
Next Obligation.
move=> A m; rewrite /bindS boolp.funeqE => s.
rewrite -[in RHS](bindmret (m s)); by bind_ext; case.
Qed.
Next Obligation.
move=> A B C m f g; rewrite /bindS boolp.funeqE => s.
by rewrite bindA; bind_ext; case.
Qed.

Definition liftS A (m : M A) : estateMonadM A :=
  fun s => @Bind M _ _ m (fun x => @Ret M _ (x, s)).

Program Definition stateMonadM : monadM M estateMonadM :=
  monadM.Pack (@monadM.Class _ _ liftS _ _).
Next Obligation.
by move=> A a; rewrite /liftS boolp.funeqE => s; rewrite bindretf.
Qed.
Next Obligation.
move=> A B m f; rewrite /liftS boolp.funeqE => s.
rewrite [in RHS]/Bind [in RHS]/Join /= /Monad_of_ret_bind.join /= /bindS !bindA.
bind_ext => a; by rewrite !bindretf.
Qed.

End state_monad_transformer.

Definition statemonad_transformer S : monadT :=
  MonadT.Pack (@MonadT.Class (estateMonadM S) (@retS S) (@bindS S) (@stateMonadM S)).

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
  monadM.Pack (@monadM.Class _ _ liftX _ _).
Next Obligation. by move=> A a; rewrite /liftX bindretf. Qed.
Next Obligation.
move=> A B m f; rewrite /liftX [in RHS]/Bind [in RHS]/Join /=.
rewrite  /Monad_of_ret_bind.join /= /bindX !bindA.
bind_ext => a; by rewrite !bindretf.
Qed.

End exception_monad_transformer.

Definition exceptionmonad_transformer Z : monadT :=
  MonadT.Pack (@MonadT.Class (eexceptionMonadM Z) (@retX Z) (@bindX Z) (@exceptionMonadM Z)).

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
  monadM.Pack (@monadM.Class _ _ liftC  _ _).
Next Obligation.
move => A a.
rewrite /liftC boolp.funeqE => cont.
by rewrite !bindretf.
Qed.
Next Obligation.
move => A B m f.
rewrite /liftC boolp.funeqE => cont.
by rewrite !bindA.
Qed.

End continuation_monad_tranformer.

Definition continuationmonad_transformer R : monadT :=
  MonadT.Pack (@MonadT.Class (econtMonadM R) (@retC R) (@bindC R) (@contMonadM R)).

Definition callcc R (M : monad) A B
  (f : (A -> continuationmonad_transformer R M B) -> continuationmonad_transformer R M A) :
  continuationmonad_transformer R M A :=
  fun cont => f (fun x _ => cont x) cont. (*NB(rei): similar def in monad_model.*)

Definition abort R r (M : monad) A :
  continuationmonad_transformer R M A := fun (k : A -> M R) => Ret r.
Arguments abort {R} _ {M} {A}.

Require Import state_monad.

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

Variables ms : stateMonad nat.
(*Let ms : stateMonad nat := ModelState.state nat.*)

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

End examples_continuation_monad_transformer.

Require Import monad_model.

Section calcul.

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
  (CM _ # (fun x => 8 + x)) (callcc_i (fun k : (_ -> CM nat _) => (k 5) >>= (fun y => Ret (y + 4)))).

Compute calcul.

End calcul.

Definition operation (E : functor) (M : monad) := (E \O M) ~> M.

Section sigma_operations.
(* TODO: rewrite ModelState.get,put,callcc with get_op, etc.? *)

Section get_functor.
Variable S : Type.
Definition get_act_obj X := S -> X.
Definition get_act_mor X Y (f : X -> Y) (t : get_act_obj X) : get_act_obj Y := fun s => f (t s).
Program Definition get_fun := Functor.Pack (@Functor.Class get_act_obj get_act_mor _ _ ).
Next Obligation. by move=> A; rewrite /get_act_mor boolp.funeqE. Qed.
Next Obligation. by move=> A B C g h; rewrite /get_act_mor boolp.funeqE. Qed.
End get_functor.

Definition get_op S A (k : S -> ModelMonad.acto S A) : ModelMonad.acto S A := fun s => k s s.

Program Definition get_operation S : operation (get_fun S) (ModelMonad.state S) :=
  Natural.Pack (@Natural.Class _ _ (@get_op S) _).
Next Obligation.
move=> A B h; rewrite boolp.funeqE => /= m /=.
rewrite boolp.funeqE => s.
by rewrite FCompE Monad_of_ret_bind.MapE.
Qed.
Arguments get_operation {S}.

Lemma getE S : @ModelState.get S = get_operation _ Ret.
Proof. by []. Qed.

Section put_functor.
Variable S : Type.
Definition put_act_obj X := (S * X)%type.
Definition put_act_mor X Y (f : X -> Y) (sx : put_act_obj X) : put_act_obj Y := (sx.1, f sx.2).
Program Definition put_fun := Functor.Pack (@Functor.Class put_act_obj put_act_mor _ _ ).
Next Obligation. by move=> A; rewrite /put_act_mor boolp.funeqE; case. Qed.
Next Obligation. by move=> A B C g h; rewrite /put_act_mor boolp.funeqE. Qed.
End put_functor.

Definition put_op S A (s : S) (m : ModelMonad.acto S A) : ModelMonad.acto S A :=
  fun _ => m s.

Program Definition put_operation S : operation (put_fun S) (ModelMonad.state S) :=
  Natural.Pack (@Natural.Class _ _ (fun A => uncurry (@put_op S A)) _).
Next Obligation.
move=> A B h.
rewrite boolp.funeqE => /=; case => s m /=.
rewrite boolp.funeqE => s'.
by rewrite 2!Monad_of_ret_bind.MapE.
Qed.

Lemma putE S : @ModelState.put S = fun s => put_op s (@Ret (ModelMonad.state S) _ tt).
Proof. by []. Qed.

Section callcc.

Let C r := ModelCont.contM r.

Section callcc_functor.
Definition callcc_act_obj r A := (A -> r) -> A.
Definition callcc_act_mor r X Y (f : X -> Y) (t : callcc_act_obj r X) : callcc_act_obj r Y :=
  fun (g : Y -> r) => f (t (fun x => g (f x))).
Program Definition callcc_fun r := Functor.Pack (@Functor.Class (callcc_act_obj r) (@callcc_act_mor r) _ _ ).
Next Obligation. by move=> A; rewrite /callcc_act_mor boolp.funeqE. Qed.
Next Obligation. by move=> A B D g h; rewrite /callcc_act_mor boolp.funeqE. Qed.
End callcc_functor.

Definition callcc_op r A (f : (C r A -> r) -> C r A) : C r A :=
  fun k => f (fun m => m k) k.

Program Definition callcc_operation r : operation (callcc_fun r) (ModelCont.contM r) :=
  Natural.Pack (@Natural.Class _ _ (@callcc_op r) _).
Next Obligation.
move=> A B h.
rewrite boolp.funeqE => /= m /=.
rewrite boolp.funeqE => g.
by rewrite Monad_of_ret_bind.MapE.
Qed.

Lemma callccE r A B (f : (A -> C r B) -> C r A) :
  ModelCont.callcc f = callcc_operation _ _ (fun k => f (fun x _ => k (Ret x))).
Proof. by []. Qed.

End callcc.

End sigma_operations.

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
Variables (E : functor) (M : monad) (op : operation E M) (N : monad) (e : monadM M N) (L : lifting op e).
Lemma liftingP : forall X, e X \o op X = L X \o (E # (e X)).
Proof. by case: L => ? [? []]. Qed.
End lifting_interface.

Module LiftingT.
Section liftingt.
Variables (E : functor) (M : monad) (op : operation E M).
Variable (T : monadT).
Definition t := Lifting.t op (LiftT T M).
Program Definition mk H : t := Lifting.Pack (Lifting.Class
  (Natural.class H)
  (@Lifting.Mixin _ _ op (T M) (LiftT T M) _ _)).
Next Obligation.
Admitted.

End liftingt.
End LiftingT.

(* Algebraic operation, mauro jaskelioff, modular monad transformers, esop 2009 *)
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
Notation aoperation := t.
Coercion baseType : aoperation >-> Natural.t.
Canonical baseType.
Notation algebraic_def := P.
End Exports.
End AOperation.
Export AOperation.Exports.
(*Lemma val_injP E M (h g : t E M) : op h = op g <-> h = g.
Proof.
split; move: h g => [h Hh] [g Hg] /= hg; last by case: hg.
rewrite hg in Hh Hg *; congr mk; exact: Prop_irrelevance.
Qed.*)

Section algebraic_operation_interface.
Variables (E : functor) (M : monad) (op : aoperation E M).
Lemma algebraic : forall A B (f : A -> M B) (t : E (M A)),
   (op A t >>= f) = op B ((E # (fun m => m >>= f)) t).
Proof. by case: op => ? [? []]. Qed.
End algebraic_operation_interface.

Section proposition17.
Section psi.
Variables (E : functor) (M : monad).

Definition psi_g (op' : E ~~> M) : E \O M ~~> M :=
  fun X m => (@Join _ X \o @op' _) m.

Lemma natural_psi (op' : E ~> M) : naturality (E \O M) M (psi_g op').
Proof.
move=> A B h; rewrite {}/psi_g.
rewrite (compA (M # h)) compfid.
rewrite (compA (M # h)).
rewrite join_naturality.
rewrite -compA.
rewrite FCompE.
by rewrite (natural op').
Qed.

Definition psi (op' : E ~> M) : operation E M :=
  Natural.Pack (@Natural.Class _ _ _ (natural_psi op')).

Lemma algebraic_psi (op' : E ~> M) : algebraic_def (psi op').
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
rewrite join_naturality.
rewrite functor_o.
rewrite -[in RHS]FCompE.
rewrite -[RHS]compE.
rewrite [in RHS]compA.
by rewrite joinA.
Qed.
End psi.
Section phi.
Variables (E : functor) (M : monad).

Definition phi_g (op : operation E M) : E ~~> M := fun X => op X \o (E # Ret).

Lemma natural_phi (op : operation E M) : naturality E M (phi_g op).
Proof.
move=> A B h; rewrite /phi_g.
rewrite compA.
rewrite (natural op).
rewrite -2!compA.
congr (_ \o _).
rewrite FCompE.
rewrite -2!(functor_o E).
rewrite ret_naturality.
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
rewrite -(compfid Ret).
by rewrite joinretM functor_id compfid.
Qed.
End bijection.
End proposition17.

Lemma Hget_aop S : algebraic_def (get_operation S).
Proof.
move=> A B /= f t.
by rewrite /get_op /= boolp.funeqE.
Qed.

Program Definition get_aop S : aoperation (get_fun S) (ModelMonad.state S) :=
  AOperation.Pack (AOperation.Class _ (AOperation.Mixin (@Hget_aop S))).
Next Obligation. by []. Qed.

Lemma Hcallcc_aop R : algebraic_def (callcc_operation R).
Proof.
move=> A B /= f t.
by rewrite /callcc_op /= boolp.funeqE.
Qed.

Program Definition callcc_aop R : aoperation (callcc_fun R) (ModelCont.cm R) :=
  AOperation.Pack (AOperation.Class _ (AOperation.Mixin (@Hcallcc_aop R))).
Next Obligation. by []. Qed.

Definition mk_natural_monadM (M N : monad) (f : monadM M N) : M ~> N :=
  Natural.Pack (@Natural.Class _ _ _ (natural_monadM f)).

Section theorem19.
Variables (E : functor) (M : monad) (op : aoperation E M).
Variables (N : monad) (e : monadM M N).

Definition alifting : E \O N ~~> N := fun X =>
  locked (Join \o e (N X) \o phi op (N X)).

Lemma aliftingE : alifting = psi (VComp (mk_natural_monadM e) (phi op)).
Proof. rewrite /alifting; unlock; by []. Qed.

Lemma natural_alifting : @naturality (E \O N) N alifting.
Proof. rewrite aliftingE; exact: natural_psi.
(* direct proof:
move=> A B h; rewrite /alifting.
unlock.
rewrite -(compA Join) -compA (compA _ Join) join_naturality.
rewrite -2![in RHS]compA -(compA Join) -[in RHS](compA Join).
congr (_ \o _).
rewrite FCompE 2!(compA (N # (N # h))) (natural_monad_morphism e).
rewrite -(compA (e (N B))) (NatTrans.H (AOperation.op op)).
rewrite -2!compA -[in RHS]compA -(compA _ (E # Ret)).
congr (_ \o (_ \o _)).
by rewrite FCompE -functor_o -(functor_o E) ret_naturality FIdf.
*)
Qed.

Lemma theorem19a : algebraic_def alifting.
Proof.
move=> A B /= f t.
rewrite aliftingE.
rewrite {1}/Bind.
Abort.

Lemma theorem19b : lifting_def op e alifting.
Proof.
move=> A /=.
Abort.

End theorem19.

Section theorem19_example_X.
Variable (S Z : Type).
Let M : monad := ModelState.state S.
Let X : monadT := exceptionmonad_transformer Z.
Let XM : monad := X M.

(* Let m : M S := Get. *)

(* Let xm : XM S := (MonadT.liftT X) _ _ m. *)

Let lift_getX : ((get_fun S) \O XM) ~~> XM :=
  alifting (get_aop S) (LiftT X M).

Goal forall X, forall k : S -> XM X, lift_getX k = (fun s => k s s).
move=> X0 k.
by rewrite /lift_getX aliftingE.
Abort.

Goal lift_getX Ret = @liftX  _ M _ (@ModelState.get S).
Proof.
by rewrite /lift_getX aliftingE.
Abort.

End theorem19_example_X.

Section theorem19_example_C.
Variable (S : Type).
Let C R : monad := ModelCont.cm R.
Let ST : monadT := statemonad_transformer S.
Let STC R : monad := ST (C R).
(* STC : S -> ((A * S) -> R) -> R *)

Let lift_callccS R : ((callcc_fun R) \O (STC R)) ~~> (STC R) :=
  alifting (callcc_aop R) (LiftT ST (C R)).

Goal forall A R (f : ((STC R) A -> R) -> (STC R) A) , lift_callccS f = (fun s k => f (fun m => m s k) s k) :> (STC R) A.
Proof.
move=> A f.
by rewrite /lift_callccS aliftingE.
Abort.

Definition callccS_ A B R (f : (A -> (STC R) B) -> (STC _) A) : (STC _) A := fun s k => f (fun x s' _ => k (x, s)) s k.

Lemma callccS_E A B R f :
  @callccS_ A B R f =
  @lift_callccS _ _ (fun (k : STC R A -> R) => f (fun a => (fun (_ : S) (_ : B * S -> R) => k (fun s' x => x (a, s'))) : STC R B)).
Proof. by rewrite /lift_callccS aliftingE. Qed.

End theorem19_example_C.

(* Variable R : Type.
Let C : monadT := continuationmonad_transformer R.
Let CM : monad := C M.

Let lift_getC : ((get_fun S) \O CM) ~> CM :=
  alifting (get_aop S) (MonadT.liftT C M).

(* Goal forall A, forall f : S -> CM A, lift_getC k = fun k s => . *)

End theorem19_example. *)
