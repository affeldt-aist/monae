Require Import ssreflect ssrmatching ssrfun ssrbool.
From mathcomp Require Import eqtype ssrnat seq choice fintype tuple.
From mathcomp Require Import bigop finmap.
From mathcomp Require Import boolp classical_sets.
Require Import monad state_monad trace_monad model.

(* Contents: sample models for the monads in monad.v, state_monad.v, trace_monad.v
   - Module ModelMonad
       identity monad
       list monad
       option monad
       set monad (using classical sets)
       state monad
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
rewrite funeqE => b; rewrite propeqE; split => [[a' <-] //| ?]; by exists a.
Qed.
Lemma bigsetU1 A (s : set A) : bigsetU s (@set1 A) = s.
Proof.
rewrite funeqE => b; rewrite propeqE; split.
- by move=> -[a ?]; rewrite /set1 => ->.
- by move=> ?; rewrite /bigsetU; exists b.
Qed.
Lemma bigsetUA A B C (s : set A) (f : A -> set B) (g : B -> set C) :
  bigsetU (bigsetU s f) g = bigsetU s (fun x => bigsetU (f x) g).
Proof.
rewrite funeqE => c; rewrite propeqE.
split => [[b [a' aa' ?] ?]|[a' aa' [b ? ?]]].
by exists a' => //; exists b.
by exists b => //; exists a'.
Qed.

Lemma setUDl : BindLaws.left_distributive (fun I A => @bigsetU A I) (@setU).
Proof.
move=> A B /= p q r; rewrite funeqE => b; rewrite propeqE; split.
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
(* In order to avoid "&& true" popping up everywhere,
 we prepare a specialized version of bigfcupP *)
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
Program Definition identity := (@Monad_of_bind_ret _ (fun A B (a : id A) (f : A -> id B) => f a) (fun A (a : A) => a)_ _ _).
End identity.

Section list.
Local Obligation Tactic := idtac.
Program Definition list := @Monad_of_bind_ret _ (fun A B (a : seq A) (f : A -> seq B) => flatten (map f a)) (fun A (a : A) => [:: a]) _ _ _.
Next Obligation. move=> ? ? ? ? /=; by rewrite cats0. Qed.
Next Obligation. move=> ? ?; by rewrite flatten_seq1. Qed.
Next Obligation.
move=> A B C; elim=> // h t IH f g /=; by rewrite map_cat flatten_cat IH.
Qed.
End list.

Section option.
Local Obligation Tactic := idtac.
Program Definition option := @Monad_of_bind_ret option (fun A B (a : option A) (f : A -> option B) =>
    if a isn't Some x then None else f x) (@Some) _ _ _.
Next Obligation. by []. Qed.
Next Obligation. by []. Qed.
Next Obligation. move=> ?; by case. Qed.
Next Obligation. move=> ? ? ?; by case. Qed.
End option.

Section set.
Local Obligation Tactic := idtac.
Program Definition set := @Monad_of_bind_ret _ (fun I A => @bigsetU A I) (@set1) _ _ _.
Next Obligation. move=> ? ? ? ?; exact: bigset1U. Qed.
Next Obligation. move=> ? ?; exact: bigsetU1. Qed.
Next Obligation. move=> ? ? ? ? ? ?; exact: bigsetUA. Qed.
End set.

Section state.
Variables S : Type.
Let m0 := fun A => S -> A * S.
Definition state : monad.
refine (@Monad_of_bind_ret m0
  (fun A B m f => fun s => let (a, s') := m s in f a s') (* bind *)
  (fun A a => fun s => (a, s)) (* ret *)
   _ _ _).
by [].
move=> A f; rewrite funeqE => ?; by case: f.
move=> A B C a b c; rewrite funeqE => ?; by case: a.
Defined.
End state.

End ModelMonad.

Module ModelFail.

Section option.
Local Obligation Tactic := by [].
Program Definition option_class := @MonadFail.Class _ _
  (@MonadFail.Mixin ModelMonad.option (@None) _).
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
move=> A B f /=; rewrite funeqE => b; rewrite propeqE.
by split=> // -[a []].
Qed.
Definition set := MonadFail.Pack set_class.
End set.

End ModelFail.

Module ModelAlt.

Section list.
Local Obligation Tactic := idtac.
Program Definition list_class := @MonadAlt.Class _ _
  (@MonadAlt.Mixin ModelMonad.list (@cat) catA _).
Next Obligation.
move=> A B /= s1 s2 k.
rewrite !bindE /Join /= /Monad_of_bind_ret.join /=.
by rewrite Monad_of_bind_ret.fmapE map_cat flatten_cat map_cat flatten_cat.
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
rewrite !bindE /Join /= /Monad_of_bind_ret.join /= Monad_of_bind_ret.fmapE /=.
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
apply: MonadNondet.Mixin => //= A p; rewrite funeqE => a;
  rewrite propeqE; rewrite /Fail /= /set0 /setU; split; tauto.
Qed.
Definition set := MonadNondet.Pack list_class.
End set.

End ModelNondet.

Module ModelStateTrace.

Section st.
Variables (S T : Type).
Local Obligation Tactic := idtac.
Program Definition mk : stateTraceMonad S T :=
let m := Monad.class (@ModelMonad.state (S * list T)) in
let stm := @MonadStateTrace.Class S T _ m
(@MonadStateTrace.Mixin _ _ (Monad.Pack m)
 (fun s => (s.1, s)) (* st_get *)
 (fun s' s => (tt, (s', s.2))) (* st_put *)
 (fun t s => (tt, (s.1, rcons s.2 t))) (* st_mark *)
 _ _ _ _ _ _) in
@MonadStateTrace.Pack S T _ stm.
Next Obligation. by []. Qed.
Next Obligation. by []. Qed.
Next Obligation. move=> *; by rewrite funeqE; case. Qed.
Next Obligation. by []. Qed.
Next Obligation. by []. Qed.
Next Obligation. by []. Qed.
End st.
End ModelStateTrace.

Module ModelRun.

Definition mk {S T} : runMonad (S * seq T).
set m := @ModelMonad.state (S * seq T).
refine (@MonadRun.Pack _ _ (@MonadRun.Class _ _ (Monad.class m)
  (@MonadRun.Mixin _ m
  (fun A m (s : S * list T) => m s) (* run *) _ _))).
by [].
move=> A B m0 f s.
rewrite !bindE /=.
rewrite Monad_of_bind_ret.fmapE /= /Join /= /Monad_of_bind_ret.join /=.
by destruct (m0 s).
Defined.

End ModelRun.

Module ModelStateTraceRun.

Definition mk {S T} :
  stateTraceRunMonad S T.
refine (let stm := @ModelStateTrace.mk S T in
        let run := @ModelRun.mk S T in
@MonadStateTraceRun.Pack S T (fun A => S * list T -> A * (S * list T))
  (@MonadStateTraceRun.Class S T (fun A => S * list T -> A * (S * list T))
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

Program Definition _monad : monad := @Monad_of_bind_ret
_m
(fun A B m (f : A -> S -> {fset (choice_of_Type B * choice_of_Type S)}) =>
     fun s => \bigcup_(i <- (fun x : [choiceType of choice_of_Type A * choice_of_Type S] => f x.1 x.2) @` (m s)) i) (* bind *)
(fun A (a : A) s => [fset (a : choice_of_Type A, s : choice_of_Type S)]) (* ret *) _ _ _.
Next Obligation.
move=> A B /= m f; rewrite funeqE => s; by rewrite imfset_set1 /= big_seq_fset1.
Qed.
Next Obligation.
move=> A B /=; rewrite funeqE => s.
apply/fsetP => /= x; apply/bigfcupP'; case: ifPn => xBs.
  set x' := (x : [choiceType of choice_of_Type A * choice_of_Type S]).
  exists [fset x']; last by rewrite inE.
    apply/imfsetP; exists x' => //=.
  by case: x'.
case => /= SA /imfsetP[] /= sa saBs ->{SA} /fset1P => Hx.
move: xBs; rewrite Hx; apply/negP; rewrite negbK; by case: sa saBs Hx.
Qed.
Next Obligation.
move=> A B C /= m f g; rewrite funeqE => s.
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

Lemma BindE (A B : Type) m (f : A -> _monad B) :
  (m >>= f) = (fun s => \bigcup_(i <- (fun x : [choiceType of choice_of_Type A * choice_of_Type S] => f x.1 x.2) @` (m s)) i).
Proof.
rewrite funeqE => s.
rewrite /Bind /Join /= /Monad_of_bind_ret.join /=.
set lhs := [fset _ _ | _ in _]. set rhs := [fset _ _ | _ in _].
rewrite (_ : lhs = rhs) //; apply/fsetP => x; rewrite {}/lhs {}/rhs.
apply/idP/imfsetP => /=.
- case/imfsetP => -[a1 a2] /=.
  rewrite /Fun /= /Monad_of_bind_ret.fmap /=.
  case/bigfcupP' => /= b.
  by case/imfsetP => -[b1 b2] /= Hb ->{b} /fset1P[-> -> ->{x a1 a2}]; exists (b1, b2).
- case=> -[a1 s1] Ha /= ->{x}.
  apply/imfsetP => /=.
  rewrite /Fun /= /Monad_of_bind_ret.fmap /=.
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
move=> s s'; rewrite funeqE => s''.
rewrite BindE; apply/fsetP => /= x; apply/bigfcupP'/fset1P.
- by case => /= x0 /imfsetP[/= x1] /fset1P _ -> /fset1P.
- move=> -> /=.
  exists [fset ((tt, s') : [choiceType of choice_of_Type unit * choice_of_Type S])] => /=; last first.
    exact/fset1P.
  apply/imfsetP => /=; exists (tt, s) => //; exact/fset1P.
Qed.
Next Obligation.
move=> s; rewrite funeqE => s'.
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
rewrite funeqE => s.
rewrite BindE /skip /= /Ret; apply/fsetP => /= x; apply/bigfcupP'/idP.
- case => /= x0 /imfsetP[/= x1] /fset1P -> -> /fset1P ->; exact/fset1P.
- move/fset1P => ->; exists [fset ((tt, s) : [choiceType of choice_of_Type unit * choice_of_Type S])]; last first.
    exact/fset1P.
  apply/imfsetP; exists (s, s) => //; by rewrite inE.
Qed.
Next Obligation.
move=> A k; rewrite funeqE => s.
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
move=> A B g; rewrite funeqE => s; apply/fsetP => x; rewrite inE BindE; apply/negbTE.
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
Next Obligation. by move=> A a b c; rewrite funeqE => s; rewrite fsetUA. Qed.
Next Obligation.
move=> A B /= m1 m2 k; rewrite funeqE => s; rewrite !BindE /=.
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
Next Obligation. move=> A /= m; rewrite funeqE => s; by rewrite fset0U. Qed.
Next Obligation. move=> A /= m; rewrite funeqE => s; by rewrite fsetU0. Qed.
End nondet.

Section nondetstate.

Variable S : choiceType.
Local Obligation Tactic := try by [].
Program Definition nondetstate : nondetStateMonad S :=
  @MonadNondetState.Pack _ _
    (@MonadNondetState.Class _ _ (MonadNondet.class (nondetbase S))
      (MonadState.mixin (MonadState.class (_state S))) (@MonadNondetState.Mixin _ _ _)).
Next Obligation.
move=> A B /= g; rewrite !BindE /=; rewrite funeqE => s; apply/fsetP => /= sa.
apply/idP/idP/bigfcupP'.
case => /= SA /imfsetP[/= bs bsgs ->{SA}].
by rewrite (@in_fset0 [choiceType of choice_of_Type A * choice_of_Type S]).
Qed.
Next Obligation.
move=> A B /= m k1 k2; rewrite funeqE => s; rewrite !BindE /=; apply/fsetP => /= bs.
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
