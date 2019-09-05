From mathcomp Require Import all_ssreflect.
From mathcomp Require Import finmap.
From mathcomp Require boolp.
From mathcomp Require Import classical_sets.
Require Import monae_lib monad fail_monad state_monad trace_monad.

(* Contents: sample models for the monads in monad.v, state_monad.v, trace_monad.v
   - Module ModelMonad
       identity monad
       list monad
       error monad
         option monad as a special case of the error monad
       set monad (using classical sets)
       state monad
       continuation monad.
   - Module ModelFail
       using ModelMonad.option
       using ModelMonad.list
       using ModelMonad.set.
   - Module ModelAlt
       using ModelMonad.list
       using ModelMonad.set
   - Module ModelAltCI.
       using ModelAlt.set
   - Module ModelNondet
       using ModelFail.list and ModelAlt.list
       using ModelFail.set and ModelAlt.set
   - ModelStateTrace
       using ModelMonad.state
   - Module ModelRun
       using ModelMonad.state.
   - ModelStateTraceRun
       using ModelStateTrace and ModelRun
   - Module ModelBacktrackableState
       from scratch using fsets, i.e., redefinition of
         monad
         state monad
         fail monad
         alt monad
         nondet monad
         nondetstate monad
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section classical_sets_extra.
Local Open Scope classical_set_scope.

Lemma bigset1U A B a (f : A -> set B) : bigsetU [set a] f = f a.
Proof.
rewrite boolp.funeqE => b; rewrite boolp.propeqE; split => [[a' <-] //| ?]; by exists a.
Qed.
Lemma bigsetU1 A (s : set A) : bigsetU s (@set1 A) = s.
Proof.
rewrite boolp.funeqE => b; rewrite boolp.propeqE; split.
- by move=> -[a ?]; rewrite /set1 => ->.
- by move=> ?; rewrite /bigsetU; exists b.
Qed.
Lemma bigsetUA A B C (s : set A) (f : A -> set B) (g : B -> set C) :
  bigsetU (bigsetU s f) g = bigsetU s (fun x => bigsetU (f x) g).
Proof.
rewrite boolp.funeqE => c; rewrite boolp.propeqE.
split => [[b [a' aa' ?] ?]|[a' aa' [b ? ?]]].
by exists a' => //; exists b.
by exists b => //; exists a'.
Qed.

Lemma setUDl : BindLaws.left_distributive (fun I A => @bigsetU A I) (@setU).
Proof.
move=> A B /= p q r; rewrite boolp.funeqE => b; rewrite boolp.propeqE; split.
move=> -[a [?|?] ?]; by [left; exists a | right; exists a].
rewrite /setU => -[[a ? ?]|[a ? ?]]; exists a; tauto.
Qed.

End classical_sets_extra.

Section PR.
Local Open Scope fset_scope.
Section ImfsetTh.
Variables (key : unit) (K V : choiceType).
Variable (f : K -> V).
Lemma imfset_set1 x : f @` [fset x] = [fset f x].
Proof.
apply/fsetP => y.
by apply/imfsetP/fset1P=> [[x' /fset1P-> //]| ->]; exists x; rewrite ?fset11.
Qed.
End ImfsetTh.
Section BigOps.
Variables (T : choiceType) (I : eqType) (r : seq I).
(* In order to avoid "&& true" popping up everywhere, *)
(*  we prepare a specialized version of bigfcupP *)
Lemma bigfcupP' x (F : I -> {fset T}) :
  reflect (exists2 i : I, (i \in r) & x \in F i)
          (x \in \bigcup_(i <- r | true) F i).
Proof.
apply: (iffP idP) => [|[i ri]]; last first.
  by apply: fsubsetP x; rewrite bigfcup_sup.
rewrite big_seq_cond; elim/big_rec: _ => [|i _ /andP[ri Pi] _ /fsetUP[|//]].
  by rewrite in_fset0.
by exists i; rewrite ?ri.
Qed.
End BigOps.
End PR.

Module ModelMonad.

Section identity.
Local Obligation Tactic := by [].
Program Definition identity := @Monad_of_ret_bind _ (fun A (a : A) => a)
  (fun A B (a : id A) (f : A -> id B) => f a) _ _ _.
End identity.

Section list.
Local Obligation Tactic := idtac.
Program Definition list := @Monad_of_ret_bind _ (fun A (a : A) => [:: a])
  (fun A B (a : seq A) (f : A -> seq B) => flatten (map f a)) _ _ _.
Next Obligation. move=> ? ? ? ? /=; by rewrite cats0. Qed.
Next Obligation. move=> ? ?; by rewrite flatten_seq1. Qed.
Next Obligation.
move=> A B C; elim=> // h t IH f g /=; by rewrite map_cat flatten_cat IH.
Qed.
End list.

Section error.
Variable Z : Type.
Local Obligation Tactic := idtac.
Let p := fun A B (a : (Z + A)%type) (f : A -> (Z + B)%type) =>
     match a with inl z => inl z | inr b => f b end.
Let H1 : BindLaws.left_neutral p (@inr Z). Proof. by []. Qed.
Let H2 : BindLaws.right_neutral p (@inr Z). Proof. by move=> ? []. Qed.
Let H3 : BindLaws.associative p. Proof. by move=> ? ? ? []. Qed.
Definition error := @Monad_of_ret_bind (fun X => (Z + X)%type) (@inr Z) p H1 H2 H3.
End error.

Definition option := error unit.

Section set.
Local Obligation Tactic := idtac.
Program Definition set := @Monad_of_ret_bind _ (@set1) (fun I A => @bigsetU A I) _ _ _.
Next Obligation. move=> ? ? ? ?; exact: bigset1U. Qed.
Next Obligation. move=> ? ?; exact: bigsetU1. Qed.
Next Obligation. move=> ? ? ? ? ? ?; exact: bigsetUA. Qed.
End set.

Module State.
Section state.
Variables S : Type.
Definition acto := fun A => S -> A * S.
Local Notation M := acto.
Definition bind := fun A B (m : M A) (f : A -> M B) => fun s => uncurry f (m s).
Definition ret : FId ~~> M := fun A a => fun s => (a, s).
Program Definition t : monad := @Monad_of_ret_bind M ret bind _ _ _.
Next Obligation. by []. Qed.
Next Obligation. by move=> A f; rewrite /bind boolp.funeqE => ?; case: f. Qed.
Next Obligation. by move=> A B C a b c; rewrite /bind boolp.funeqE => ?; case: a. Qed.
End state.
End State.

Module Cont.
Section cont.
(* https://qiita.com/suharahiromichi/items/f07f932103c28f36dd0e *)
Variable r : Type.
Definition acto := fun A => (A -> r) -> r.
Local Notation M := acto.
Program Definition t : monad := (@Monad_of_ret_bind M
  (fun A a => fun k => k a)
  (fun A B ma f => fun k => ma (fun a => f a k)) _ _ _).
Next Obligation. by []. Qed.
Next Obligation. by []. Qed.
Next Obligation. by []. Qed.
End cont.
End Cont.

End ModelMonad.

Module ModelFail.

Section option.
Local Obligation Tactic := by [].
Program Definition option_class := @MonadFail.Class _ _
  (@MonadFail.Mixin ModelMonad.option (fun B => @inl _ B tt) _).
Definition option := MonadFail.Pack option_class.
End option.

Section list.
Local Obligation Tactic := by [].
Program Definition list_class := @MonadFail.Class _ _
  (@MonadFail.Mixin ModelMonad.list (@nil) _).
Definition list := MonadFail.Pack list_class.
End list.

Section set.
Local Obligation Tactic := idtac.
Program Definition set_class := @MonadFail.Class _ _
  (@MonadFail.Mixin ModelMonad.set (@set0) _).
Next Obligation.
move=> A B f /=; rewrite boolp.funeqE => b; rewrite boolp.propeqE.
by split=> // -[a []].
Qed.
Definition set := MonadFail.Pack set_class.
End set.

End ModelFail.

Module ModelExcept.
Section except.
Program Definition except_class := @MonadExcept.Class _
  ModelFail.option_class (@MonadExcept.Mixin _
    (fun A m m' => if m is inr x then m else m') _ _ _ _).
Next Obligation. by case => //; case. Qed.
Next Obligation. by case. Qed.
Next Obligation. by case. Qed.
Next Obligation. by case. Qed.
Definition t := MonadExcept.Pack except_class.
End except.
End ModelExcept.

Module StateOps.
Section get_functor.
Variable S : Type.
Definition get_acto X := S -> X.
Definition get_actm X Y (f : X -> Y) (t : get_acto X) : get_acto Y := fun s => f (t s).
Program Definition get_fun := Functor.Pack (@Functor.Class get_acto get_actm _ _ ).
Next Obligation. by move=> A; rewrite /get_actm boolp.funeqE. Qed.
Next Obligation. by move=> A B C g h; rewrite /get_actm boolp.funeqE. Qed.
End get_functor.

Definition get S A (k : S -> ModelMonad.State.acto S A) : ModelMonad.State.acto S A :=
  fun s => k s s.

Program Definition get_op S : operation (get_fun S) (ModelMonad.State.t S) :=
  Natural.Pack (@Natural.Class _ _ (@get S) _).
Next Obligation.
move=> A B h; rewrite boolp.funeqE => /= m /=.
rewrite boolp.funeqE => s.
by rewrite FCompE Monad_of_ret_bind.MapE.
Qed.
Arguments get_op {S}.

Section put_functor.
Variable S : Type.
Definition put_acto X := (S * X)%type.
Definition put_actm X Y (f : X -> Y) (sx : put_acto X) : put_acto Y := (sx.1, f sx.2).
Program Definition put_fun := Functor.Pack (@Functor.Class put_acto put_actm _ _ ).
Next Obligation. by move=> A; rewrite /put_actm boolp.funeqE; case. Qed.
Next Obligation. by move=> A B C g h; rewrite /put_actm boolp.funeqE. Qed.
End put_functor.

Definition put S A (s : S) (m : ModelMonad.State.acto S A) : ModelMonad.State.acto S A :=
  fun _ => m s.

Program Definition put_op S : operation (put_fun S) (ModelMonad.State.t S) :=
  Natural.Pack (@Natural.Class _ _ (fun A => uncurry (@put S A)) _).
Next Obligation.
move=> A B h.
rewrite boolp.funeqE => /=; case => s m /=.
rewrite boolp.funeqE => s'.
by rewrite 2!Monad_of_ret_bind.MapE.
Qed.
Arguments put_op {S}.
End StateOps.

Module ModelState.
Section modelstate.
Variable S : Type.
Local Notation M := (ModelMonad.State.t S).
Definition get : M S := StateOps.get_op _ Ret.
Lemma getE : get = fun s => (s, s). Proof. by []. Qed.
Definition put : S -> M unit := fun s => StateOps.put_op _ (s, @Ret _ _ tt).
Lemma putE : put = fun s' _ => (tt, s').
Proof. by []. Qed.
Program Definition state : stateMonad S := MonadState.Pack (MonadState.Class
  (@MonadState.Mixin _ (ModelMonad.State.t S) get put _ _ _ _)).
End modelstate.
End ModelState.

Module ModelAlt.

Section list.
Local Obligation Tactic := idtac.
Program Definition list_class := @MonadAlt.Class _ _
  (@MonadAlt.Mixin ModelMonad.list (@cat) catA _).
Next Obligation.
move=> A B /= s1 s2 k.
rewrite !bindE /Join /= /Monad_of_ret_bind.join /=.
by rewrite Monad_of_ret_bind.MapE map_cat flatten_cat map_cat flatten_cat.
Qed.
Definition list := MonadAlt.Pack list_class.
End list.

Section set.
Local Obligation Tactic := idtac.
Program Definition set_class := @MonadAlt.Class _ _
  (@MonadAlt.Mixin ModelMonad.set (@setU) _ _).
Next Obligation. exact: setUA. Qed.
Next Obligation.
rewrite /BindLaws.left_distributive /= => A B m1 m2 k.
rewrite !bindE /Join /= /Monad_of_ret_bind.join /= Monad_of_ret_bind.MapE /=.
by rewrite setUDl // setUDl.
Qed.
Definition set := MonadAlt.Pack set_class.
End set.

End ModelAlt.

Module ModelAltCI.

Section set.
Local Obligation Tactic := idtac.
Program Definition set_class := @MonadAltCI.Class _
  ModelAlt.set_class (@MonadAltCI.Mixin _ (@setU) _ _).
Next Obligation. exact: setUid. Qed.
Next Obligation. exact: setUC. Qed.
Definition set := MonadAltCI.Pack set_class.
End set.

End ModelAltCI.

Module ModelNondet.

Section list.
Local Obligation Tactic := idtac.
Program Definition list_class := @MonadNondet.Class _
  ModelFail.list_class (MonadAlt.mixin ModelAlt.list_class) _.
Next Obligation. apply: MonadNondet.Mixin => //= A l; by rewrite cats0. Qed.
Definition list := MonadNondet.Pack list_class.
End list.

Section set.
Local Obligation Tactic := idtac.
Program Definition set_class := @MonadNondet.Class _
  ModelFail.set_class (MonadAlt.mixin ModelAlt.set_class) _.
Next Obligation.
apply: MonadNondet.Mixin => //= A p; rewrite boolp.funeqE => a;
  rewrite boolp.propeqE; rewrite /Fail /= /set0 /setU; split; tauto.
Qed.
Definition set := MonadNondet.Pack list_class.
End set.

End ModelNondet.

Module ModelStateTrace.

Section st.
Variables (S T : Type).
Local Obligation Tactic := idtac.
Program Definition mk : stateTraceMonad S T :=
let m := Monad.class (@ModelMonad.State.t (S * list T)) in
let stm := @MonadStateTrace.Class S T _ m
(@MonadStateTrace.Mixin _ _ (Monad.Pack m)
 (fun s => (s.1, s)) (* st_get *)
 (fun s' s => (tt, (s', s.2))) (* st_put *)
 (fun t s => (tt, (s.1, rcons s.2 t))) (* st_mark *)
 _ _ _ _ _ _) in
@MonadStateTrace.Pack S T _ stm.
Next Obligation. by []. Qed.
Next Obligation. by []. Qed.
Next Obligation. move=> *; by rewrite boolp.funeqE; case. Qed.
Next Obligation. by []. Qed.
Next Obligation. by []. Qed.
Next Obligation. by []. Qed.
End st.
End ModelStateTrace.

Module ContOps.
Section acallcc_functor.
Definition acallcc_acto r := fun A => (A -> r) -> A.
Local Notation M := acallcc_acto.
Definition acallcc_actm r X Y (f : X -> Y) (t : M r X) : M r Y :=
  fun (g : Y -> r) => f (t (fun x => g (f x))).
Program Definition acallcc_fun r := Functor.Pack (@Functor.Class _ (@acallcc_actm r) _ _ ).
Next Obligation. by move=> A; rewrite /acallcc_actm boolp.funeqE. Qed.
Next Obligation. by move=> A B D g h; rewrite /acallcc_actm boolp.funeqE. Qed.
End acallcc_functor.

(* alebgraic call/cc *)
Definition acallcc r A (f : (ModelMonad.Cont.acto r A -> r) -> ModelMonad.Cont.acto r A) : ModelMonad.Cont.acto r A :=
  fun k => f (fun m => m k) k.

Program Definition acallcc_op r : operation (acallcc_fun r) (ModelMonad.Cont.t r) :=
  Natural.Pack (@Natural.Class _ _ (@acallcc r) _).
Next Obligation. by []. Qed.
End ContOps.

Definition usual_callcc r (M := fun C => (C -> r) -> r) A B (f : (A -> M B) -> M A) : M A :=
  fun k : A -> r => f (fun a _ => k a) k.

Module ModelCont.
Section modelcont.
Variable r : Type.
Local Notation M := (ModelMonad.Cont.t r).
Definition callcc A B (f : (A -> M B) -> M A) : M A :=
  ContOps.acallcc_op _ _ (fun k => f (fun x _ => k (Ret x))).
Lemma callccE A B (f : (A -> M B) -> M A) : callcc f = usual_callcc f.
Proof. by []. Qed.
Program Definition t : contMonad := MonadContinuation.Pack (MonadContinuation.Class
  (@MonadContinuation.Mixin (ModelMonad.Cont.t r) callcc _ _ _ _)).
End modelcont.
End ModelCont.

Section continuation_examples.
Fixpoint fib (n : nat) : nat :=
  match n with
    | 0 => 1
    | 1 => 1
    | (m.+1 as sm).+1 => fib sm + fib m
  end.
Local Open Scope monae_scope.
Fixpoint fib_cps {M : monad} (n : nat) : M nat :=
  match n with
    | 0 => Ret 1
    | 1 => Ret 1
    | (m.+1 as sm).+1 =>
      fib_cps sm >>=
      fun a => fib_cps m >>=
      fun b => Ret (a + b)
  end.

Lemma fib_cpsE (M : monad) n :
  fib_cps n.+2 = (fib_cps n.+1 >>= fun a => fib_cps n >>= fun b => Ret (a + b)) :> M _.
Proof. by []. Qed.
Let nat_ind2 (P : nat -> Prop) (P0 : P O) (P1 : P 1) :
  (forall m, P m -> P m.+1 -> P m.+2) -> forall m, P m.
Proof.
move=> H n; suff : P n /\ P n.+1 by case.
elim: n => // n [] H1 H2; split => //; exact: H.
Qed.
Goal forall (M : monad) n, fib_cps n = Ret (fib n) :> M nat.
Proof.
move=> M; apply nat_ind2 => // n ih1 ih2.
by rewrite fib_cpsE ih2 bindretf ih1 bindretf.
Qed.
Local Close Scope monae_scope.

Definition oaddn (M : monad) (acc : nat) (x : option nat) : M nat :=
  if x is Some x then Ret (x + acc) else Ret acc.
Definition sum_just M (xs : seq (option nat)) := foldM (oaddn M) 0 xs.

Definition oaddn_break (M : monad) (break : nat -> M nat) (acc : nat) (x : option nat) : M nat :=
  if x is Some x then Ret (x + acc) else break acc.
Let M : contMonad := ModelCont.t nat.
Definition sum_break (xs : seq (option nat)) : M nat :=
  Callcc (fun break : nat -> M nat => foldM (oaddn_break break) 0 xs).
Compute (sum_break [:: Some 2; Some 6; None; Some 4]).

Goal Ret 1 +m (Callcc (fun f => Ret 10 +m (f 100)) : M _) =
     Ret (1 + 100).
Proof. by rewrite /addM bindretf boolp.funeqE. Abort.

(* https://xavierleroy.org/mpri/2-4/transformations.pdf *)
Local Open Scope monae_scope.

Fixpoint list_iter (M : monad) A (f : A -> M unit) (s : seq A) : M unit :=
  if s is h :: t then f h >> list_iter f t else Ret tt.
Compute (@list_iter ModelMonad.identity nat (fun a => Ret tt) [:: O; 1; 2]).

Definition list_find (M : contMonad) A (p : pred A) (s : seq A) : M _ :=
  Callcc (fun k => list_iter (fun x => if p x then (*Throw*) k (Some x) else Ret tt) s >> Ret None).

(* returns None if no such element exists *)
Compute (@list_find (@ModelCont.t bool) nat [pred x | odd x] [:: 2; 4; 6]).
(* returns the first element such that *)
Compute (@list_find (@ModelCont.t bool) nat [pred x | odd x] [:: 2; 4; 3; 6]).

End continuation_examples.

(* Work In Progress *)
Module ModelShiftReset.
Local Open Scope monae_scope.
(* Local Obligation Tactic := idtac. *)
Definition shift r : forall A, ((A -> ModelCont.t r r) -> ModelCont.t r r) -> ModelCont.t r A :=
 fun A h => fun c => h (fun v => Ret (c v)) ssrfun.id.

Definition reset r : ModelCont.t r r -> ModelCont.t r r :=
  fun m => fun c => c (m ssrfun.id).

Program Definition shiftresetM r : monad :=
  let M : contMonad := ModelCont.t r in
  @MonadShiftReset.Pack _ _ (@MonadShiftReset.Class _ r (MonadContinuation.class M)
 (@MonadShiftReset.Mixin _ _
 (@shift r)
 (@reset r) _ _ _ _ _)).

Section examples.
Let M : monad := shiftresetM nat.
Goal Ret 1 +m (Reset (Ret 10 +m (Shift (fun f : _ -> M nat => f (100) >>= f) : M _)) : M _) =
     Ret (1 + (10 + (10 + 100))).
Proof. by rewrite /addM bindretf boolp.funeqE. Abort.
Goal Ret 1 +m (Reset (Ret 10 +m (Shift (fun f : _ -> M nat => Ret 100) : M _)) : M _) =
     Ret (1 + 100).
Proof. by rewrite /addM bindretf boolp.funeqE. Abort.
Goal Ret 1 +m (Reset (Ret 10 +m (Shift (fun f : _ -> M nat => f 100 +m f 1000) : M _)) : M _) =
     Ret (1 + ((10 + 100) + (10 + 1000))).
Proof. by rewrite /addM bindretf boolp.funeqE. Abort.

Let N : monad := shiftresetM (seq nat).
Fixpoint perverse (l : seq nat) : N (seq nat) :=
  if l is h :: t then
    Shift (fun f : _ -> N _ => Ret h >>= (fun x => perverse t >>= f >>= (fun y => Ret (x :: y))))
  else Ret [::].
Goal Reset (perverse [:: 1; 2; 3]) = Ret [:: 3; 2; 1] :> shiftresetM _ (seq nat).
by [].
Abort.

Definition stranger :=
  let g b := Reset ((Shift (fun f : _ -> shiftresetM _ _ => f b) >>= (fun x => if x then Ret 2 else Ret 3)) : shiftresetM _ _) in
  g true +m g false.
Goal stranger = Ret 5. by []. Abort.
End examples.
End ModelShiftReset.

(* Work In Progress *)
Module ModelStateLoop.
Section modelstateloop.
Local Open Scope monae_scope.
Variable S : Type.
Local Notation M := (@ModelMonad.State.t S).
Fixpoint mforeach (it min : nat) (body : nat -> M unit) : M unit :=
  if it <= min then Ret tt
  else if it is it'.+1 then
      (body it') >>= (fun _ => mforeach it' min body)
      else Ret tt.
Program Definition mk : loopStateMonad S :=
let m := @ModelState.state S in
let slm := @MonadStateLoop.Class S _ (MonadState.class m)
  (@MonadStateLoop.Mixin _ m mforeach _ _ ) in
MonadStateLoop.Pack slm.
Next Obligation. by case: m => //= n; rewrite ltnS leqnn. Qed.
Next Obligation. by case: ifPn => //; rewrite ltnNge leq_addr. Qed.
End modelstateloop.
End ModelStateLoop.

Module ModelRun.

Definition mk {S T} : runMonad (S * seq T).
set m := @ModelMonad.State.t (S * seq T).
refine (@MonadRun.Pack _ _ (@MonadRun.Class _ _ (Monad.class m)
  (@MonadRun.Mixin _ m
  (fun A m (s : S * seq T) => m s) (* run *) _ _))).
by [].
move=> A B m0 f s.
rewrite !bindE /=.
rewrite Monad_of_ret_bind.MapE /= /Join /= /Monad_of_ret_bind.join /=.
rewrite /ModelMonad.State.bind /=.
by destruct (m0 s).
Defined.

End ModelRun.

Module ModelStateTraceRun.

Definition mk {S T} :
  stateTraceRunMonad S T.
refine (let stm := @ModelStateTrace.mk S T in
        let run := @ModelRun.mk S T in
@MonadStateTraceRun.Pack S T (fun A => S * seq T -> A * (S * seq T))
  (@MonadStateTraceRun.Class S T (fun A => S * seq T -> A * (S * seq T))
    (MonadStateTrace.class stm)
    (MonadRun.mixin (MonadRun.class run))
    (@MonadStateTraceRun.Mixin _ _ run _ _ _ _ _ _))).
by [].
by [].
by [].
Defined.

End ModelStateTraceRun.

Module ModelBacktrackableState.
Local Open Scope fset_scope.

Section monad.
Variable S : Type.
Local Obligation Tactic := try by [].

Definition _m : Type -> Type :=
  fun A => S -> {fset (choice_of_Type A * choice_of_Type S)}.

Program Definition _monad : monad := @Monad_of_ret_bind _m
(fun A (a : A) s => [fset (a : choice_of_Type A, s : choice_of_Type S)])
(fun A B m (f : A -> S -> {fset (choice_of_Type B * choice_of_Type S)}) =>
  fun s => \bigcup_(i <- (fun x : [choiceType of choice_of_Type A * choice_of_Type S] => f x.1 x.2) @` (m s)) i)
_ _ _.
Next Obligation.
move=> A B /= m f; rewrite boolp.funeqE => s; by rewrite imfset_set1 /= big_seq_fset1.
Qed.
Next Obligation.
move=> A B /=; rewrite boolp.funeqE => s.
apply/fsetP => /= x; apply/bigfcupP'; case: ifPn => xBs.
  set x' := (x : [choiceType of choice_of_Type A * choice_of_Type S]).
  exists [fset x']; last by rewrite inE.
    apply/imfsetP; exists x' => //=.
  by case: x'.
case => /= SA /imfsetP[] /= sa saBs ->{SA} /fset1P => Hx.
move: xBs; rewrite Hx; apply/negP; rewrite negbK; by case: sa saBs Hx.
Qed.
Next Obligation.
move=> A B C /= m f g; rewrite boolp.funeqE => s.
have @g' : choice_of_Type B -> choice_of_Type S -> {fset choice_of_Type C * choice_of_Type S}.
  move=> b' s'; exact: (g b' s').
apply/fsetP => /= x; apply/bigfcupP'/bigfcupP'; case => /= CS  /imfsetP[/=].
- move=> bs /bigfcupP'[/= BS]  /imfsetP[/= sa] sams ->{BS} bsfsa ->{CS} xgbs.
  exists (\bigcup_(i <- [fset g' x0.1 x0.2 | x0 in f sa.1 sa.2]) i).
    by apply/imfsetP => /=; exists sa.
  apply/bigfcupP'; exists (g bs.1 bs.2) => //; by apply/imfsetP => /=; exists bs.
- move=> sa sams ->{CS} /bigfcupP'[/= CS]  /imfsetP[/= bs] bsfsa ->{CS} xgbs.
  exists (g bs.1 bs.2) => //; apply/imfsetP => /=; exists bs => //.
  apply/bigfcupP' => /=; exists (f sa.1 sa.2) => //; by apply/imfsetP => /=; exists sa.
Qed.
Local Open Scope monae_scope.
Lemma BindE (A B : Type) m (f : A -> _monad B) :
  m >>= f = fun s => \bigcup_(i <- (fun x : [choiceType of choice_of_Type A * choice_of_Type S] => f x.1 x.2) @` (m s)) i.
Proof.
rewrite boolp.funeqE => s.
rewrite /Bind /Join /= /Monad_of_ret_bind.join /=.
set lhs := [fset _ _ | _ in _]. set rhs := [fset _ _ | _ in _].
rewrite (_ : lhs = rhs) //; apply/fsetP => x; rewrite {}/lhs {}/rhs.
apply/idP/imfsetP => /=.
- case/imfsetP => -[a1 a2] /=.
  rewrite /Fun /= /Monad_of_ret_bind.Map /=.
  case/bigfcupP' => /= b.
  by case/imfsetP => -[b1 b2] /= Hb ->{b} /fset1P[-> -> ->{x a1 a2}]; exists (b1, b2).
- case=> -[a1 s1] Ha /= ->{x}.
  apply/imfsetP => /=.
  rewrite /Fun /= /Monad_of_ret_bind.Map /=.
  eexists.
  + apply/bigfcupP' => /=.
    eexists.
      apply/imfsetP => /=.
      by exists (a1, s1).
    apply/fset1P; reflexivity.
  + by [].
Qed.

End monad.

Section state.
Variable S : Type.
Local Obligation Tactic := try by [].

Program Definition _state : stateMonad S :=
(@MonadState.Pack S (_m S)
  (@MonadState.Class S (_m S) (Monad.class (_monad S)) (@MonadState.Mixin S (_monad S)
((fun s => [fset (s : choice_of_Type S , s : choice_of_Type S)]) : (_monad S S)) (* get *)
((fun s => (fun _ => [fset (tt : choice_of_Type unit, s : choice_of_Type S)])) : S -> (_monad S unit)) (* put *)
_ _ _ _))).
Next Obligation.
move=> s s'; rewrite boolp.funeqE => s''.
rewrite BindE; apply/fsetP => /= x; apply/bigfcupP'/fset1P.
- by case => /= x0 /imfsetP[/= x1] /fset1P _ -> /fset1P.
- move=> -> /=.
  exists [fset ((tt, s') : [choiceType of choice_of_Type unit * choice_of_Type S])] => /=; last first.
    exact/fset1P.
  apply/imfsetP => /=; exists (tt, s) => //; exact/fset1P.
Qed.
Next Obligation.
move=> s; rewrite boolp.funeqE => s'.
rewrite 2!BindE /=; apply/fsetP => /= x; apply/bigfcupP'/bigfcupP'.
- case => /= x0 /imfsetP[/= x1] /fset1P -> -> /fset1P ->.
  exists [fset ((s, s) : [choiceType of choice_of_Type S * choice_of_Type S])]; last first.
    exact/fset1P.
  apply/imfsetP => /=; exists (tt, s) => //; exact/fset1P.
- case => /= x0 /imfsetP[/= x1] /fset1P -> -> /fset1P ->.
  exists [fset ((s ,s) : [choiceType of choice_of_Type S * choice_of_Type S])]; last first.
    exact/fset1P.
  apply/imfsetP => /=; exists (tt, s) => //; exact/fset1P.
Qed.
Next Obligation.
rewrite boolp.funeqE => s.
rewrite BindE /skip /= /Ret; apply/fsetP => /= x; apply/bigfcupP'/idP.
- case => /= x0 /imfsetP[/= x1] /fset1P -> -> /fset1P ->; exact/fset1P.
- move/fset1P => ->; exists [fset ((tt, s) : [choiceType of choice_of_Type unit * choice_of_Type S])]; last first.
    exact/fset1P.
  apply/imfsetP; exists (s, s) => //; by rewrite inE.
Qed.
Next Obligation.
move=> A k; rewrite boolp.funeqE => s.
rewrite 2!BindE; apply/fsetP => x; apply/bigfcupP'/bigfcupP'.
- case => /= x0 /imfsetP[/= x1] /fset1P -> ->.
  rewrite BindE => /bigfcupP'[/= x2] /imfsetP[/= x3] /fset1P -> -> xkss.
  exists (k s s s) => //; apply/imfsetP; exists (s, s) => //; by rewrite inE.
- case => /= x0 /imfsetP[/= x1] /fset1P -> -> /= xksss.
  have @k' : choice_of_Type S -> choice_of_Type S -> (choice_of_Type S -> {fset choice_of_Type A * choice_of_Type S}).
    move=> a b s'; exact: (k a b s').
  exists (\bigcup_(i <- [fset k' (s, s).1 x2.1 x2.2 | x2 in [fset (((s, s).2, (s, s).2) : [choiceType of choice_of_Type S * choice_of_Type S])]]) i).
    apply/imfsetP ; exists (s, s); by [rewrite inE | rewrite BindE].
  apply/bigfcupP'; exists (k s s s) => //;   apply/imfsetP; exists (s, s) => //=; exact/fset1P.
Qed.

End state.

Section fail.
Variable S : choiceType.
Program Definition _fail : failMonad := @MonadFail.Pack _
  (@MonadFail.Class _ (Monad.class (_monad S))
    (@MonadFail.Mixin _ (fun (A : Type) (_ : S) => fset0) _)).
Next Obligation.
move=> A B g; rewrite boolp.funeqE => s; apply/fsetP => x; rewrite inE BindE; apply/negbTE.
apply/bigfcupP'; case => /= x0 /imfsetP[/= sa].
by rewrite (@in_fset0 [choiceType of choice_of_Type A * choice_of_Type S]).
Qed.

End fail.

Section alt.

Variable S : choiceType.
Local Obligation Tactic := try by [].
Program Definition _alt : altMonad := @MonadAlt.Pack _
  (@MonadAlt.Class _ (@Monad.class (_monad S))
    (@MonadAlt.Mixin (_monad S)
      (fun (A : Type) (a b : S -> {fset [choiceType of choice_of_Type A * choice_of_Type S]}) (s : S) => a s `|` b s) _ _)).
Next Obligation. by move=> A a b c; rewrite boolp.funeqE => s; rewrite fsetUA. Qed.
Next Obligation.
move=> A B /= m1 m2 k; rewrite boolp.funeqE => s; rewrite !BindE /=.
apply/fsetP => /= bs; apply/bigfcupP'/fsetUP.
- case => /= BS /imfsetP[/= sa] /fsetUP[sam1s ->{BS} Hbs|sam2s ->{BS} Hbs].
  + left; apply/bigfcupP' => /=; exists (k sa.1 sa.2) => //; apply/imfsetP; by exists sa.
  + right; apply/bigfcupP' => /=; exists (k sa.1 sa.2) => //; apply/imfsetP; by exists sa.
- case => /bigfcupP'[/= BS /imfsetP[/= sa sams ->{BS} bsksa]].
  by exists (k sa.1 sa.2) => //; apply/imfsetP; exists sa => //; rewrite inE sams.
  by exists (k sa.1 sa.2) => //; apply/imfsetP; exists sa => //; rewrite inE sams orbT.
Qed.

End alt.

Section nondet.

Variable S : choiceType.
Local Obligation Tactic := try by [].
Program Definition nondetbase : nondetMonad :=
  @MonadNondet.Pack _ (@MonadNondet.Class _ (@MonadFail.class (_fail S))
    (@MonadAlt.mixin (_alt S) _) (@MonadNondet.Mixin _ _ _ _)).
Next Obligation. move=> A /= m; rewrite boolp.funeqE => s; by rewrite fset0U. Qed.
Next Obligation. move=> A /= m; rewrite boolp.funeqE => s; by rewrite fsetU0. Qed.
End nondet.

Section nondetstate.

Variable S : choiceType.
Local Obligation Tactic := try by [].
Program Definition nondetstate : nondetStateMonad S :=
  @MonadNondetState.Pack _ _
    (@MonadNondetState.Class _ _ (MonadNondet.class (nondetbase S))
      (MonadState.mixin (MonadState.class (_state S))) (@MonadNondetState.Mixin _ _ _)).
Next Obligation.
move=> A B /= g; rewrite !BindE /=; rewrite boolp.funeqE => s; apply/fsetP => /= sa.
apply/idP/idP/bigfcupP'.
case => /= SA /imfsetP[/= bs bsgs ->{SA}].
by rewrite (@in_fset0 [choiceType of choice_of_Type A * choice_of_Type S]).
Qed.
Next Obligation.
move=> A B /= m k1 k2; rewrite boolp.funeqE => s; rewrite !BindE /=; apply/fsetP => /= bs.
apply/bigfcupP'/idP.
- case => /= BS /imfsetP[/= sa sams ->{BS}] /fsetUP[bsk1|bsk2].
  + apply/fsetUP; left; apply/bigfcupP'; exists (k1 sa.1 sa.2) => //.
    apply/imfsetP; by exists sa.
  + apply/fsetUP; right; apply/bigfcupP'; exists (k2 sa.1 sa.2) => //.
    apply/imfsetP; by exists sa.
- move/fsetUP => [|] /bigfcupP'[/= BS] /imfsetP[/= sa sams ->{BS}] bsk.
  exists (k1 sa.1 sa.2 `|` k2 sa.1 sa.2).
    apply/imfsetP; by exists sa.
  by apply/fsetUP; left.
  exists (k1 sa.1 sa.2 `|` k2 sa.1 sa.2).
    apply/imfsetP; by exists sa.
  by apply/fsetUP; right.
Qed.

End nondetstate.

End ModelBacktrackableState.
