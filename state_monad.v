Require Import FunctionalExtensionality Coq.Program.Tactics ProofIrrelevance.
Require Classical.
Require Import ssreflect ssrmatching ssrfun ssrbool.
From mathcomp Require Import eqtype ssrnat seq choice fintype tuple.
Require Import monad.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*
Contents:
- Module MonadState.
    n-queens example
- Module MonadStateNondet.
    state + nondeterminism
    eight queens puzzle
- Module MonadFresh.
- Module MonadFreshFail.
    example of tree relabelling
*)

Module MonadState.
Record mixin_of S (M : monad) : Type := Mixin {
  get : M S ;
  put : S -> M unit ;
  _ : forall s s', put s >> put s' = put s' ;
  _ : forall s, put s >> get = put s >> Ret s ;
  _ : get >>= put = skip ;
  _ : forall k : S -> S -> M S,
    get >>= (fun s => get >>= k s) = get >>= fun s => k s s
}.
Record class_of S (m : Type -> Type) := Class {
  base : Monad.class_of m ; mixin : mixin_of S (Monad.Pack base) }.
Structure t S : Type := Pack { m : Type -> Type ; class : class_of S m }.
Definition op_get S (M : t S) : m M S :=
  let: Pack _ (Class _ (Mixin x _ _ _ _ _)) := M return m M S in x.
Arguments op_get {S M} : simpl never.
Definition op_put S (M : t S) : S -> m M unit :=
  let: Pack _ (Class _ (Mixin _ x _ _ _ _)) := M return S -> m M unit in x.
Arguments op_put {S M} : simpl never.
(* inheritance *)
Definition baseType S (M : t S) := Monad.Pack (base (class M)).
Module Exports.
Notation Get := op_get.
Notation Put := op_put.
Notation stateMonad := t.
Coercion baseType : stateMonad >-> monad.
Canonical baseType.
End Exports.
End MonadState.
Export MonadState.Exports.

Section state_lemmas.
Variables (S : Type) (M : stateMonad S).
Lemma putget s : Put s >> Get = Put s >> Ret s :> M _.
Proof. by case: M => m [[? ? ? ? ? []] ]. Qed.

Lemma getputskip : Get >>= Put = skip :> M _.
Proof. by case: M => m [[? ? ? ? ? []] ]. Qed.

Lemma putput s s' : Put s >> Put s' = Put s' :> M _.
Proof. by case: M => m [[? ? ? ? ? []] ]. Qed.

Lemma getget (k : S -> S -> M S ) :
 (Get >>= (fun s => Get >>= k s)) = (Get >>= fun s => k s s).
Proof. by case: M k => m [[? ? ? ? ? []] ]. Qed.
End state_lemmas.

Lemma putgetput S {M : stateMonad S} x {B} (k : _ -> M B) :
  Put x >> Get >>= (fun x' => k x') = Put x >> k x :> M _.
Proof. by rewrite putget bindA bindretf. Qed.

Definition place n {B} (rs : seq B) := zip (iota 1 n) rs.

Definition empty {B} : (seq B * seq B):= ([::] , [::]).

Section nqueens.

(* input: queen position, already threatened up/down diagonals
   output: safe or not, update up/down diagonals *)
Definition test : nat`2 -> (seq nat)`2 -> bool * (seq nat)`2 :=
  fun '(c, r) '(upds, downs) =>
    let (u, d) := (r - c, r + c) in
    ((u \notin upds) && (d \notin downs), (u :: upds, d :: downs)).

Section purely_functional.

Definition start1 : (seq nat)`2 -> bool * (seq nat)`2 :=
  fun updowns => (true, updowns).

Definition step1 : nat`2 -> (bool * (seq nat)`2) -> bool * (seq nat)`2 :=
  fun cr '(restOK, updowns) =>
    let (thisOK, updowns') := test cr updowns in
    (thisOK && restOK, updowns').

(* over the list of column-row pairs
   bool * (seq nat)`2: queens to the right safe or not,
                       up/down diagonals under threat from the queens so far *)
Definition safe1 : (seq nat)`2 -> seq nat`2 -> bool * (seq nat)`2 :=
  foldr step1 \o start1.

Definition queens {M : nondetMonad} n : M (seq nat) :=
  Do{ rs <- perms (iota 1 n) ;
      (guard (safe1 empty (place n rs)).1 >> Ret rs)}.

End purely_functional.

Section statefully.
(* statefully constructing the sets of up/down diagonals threatened by the queens so far *)

Context {M : stateMonad (seq nat)`2}.

Definition start2 : M bool := Ret true.

Definition step2 (cr : nat`2) (k : M bool) : M bool :=
  Do{ b' <- k ;
    Do{ uds <- Get;
      let (b, uds') := test cr uds in
      Put uds' >> Ret (b && b')}}.

Definition safe2 : seq nat`2 -> M bool :=
  foldr step2 start2.

Lemma safe2E crs :
  safe2 crs = Do{ uds <- Get; let (ok, uds') := safe1 uds crs in
                                (Put uds' >> Ret ok)} :> M _.
Proof.
(* TODO(rei): how to write this proof w.o. the "set" and "transitivity"'s? *)
apply/esym; rewrite /safe2.
set f := fun x => Do{ uds <- Get; let (ok, uds') := safe1 uds x in Put uds' >> Ret ok} : M _.
rewrite -(@foldr_universal_ext _ _ _ _ f) //;
  [apply/esym|move=> cr {crs}crs; apply/esym].
  by rewrite /start2 /f /= -bindA getputskip bindskipf.
(* definition of safe1 *)
transitivity
  (Do{ uds <- Get;
  let (ok, uds') := step1 cr (safe1  uds crs) in Put uds'>> Ret ok} : M _); last first.
  by [].
(* introduce a let *)
transitivity
  (Do{ uds <- Get;
  let (b', uds'') := safe1 uds crs in
  let (ok, uds') := step1 cr (b', uds'') in Put uds' >> Ret ok} : M _); last first.
  bind_ext => x.
  by case: safe1.
(* definition of step1 *)
transitivity
  (Do{ uds <- Get;
  let (b', uds'') := safe1 uds crs in
  let (b, uds''') := test cr uds'' in
  let (ok, uds') := (b && b', uds''') in Put uds' >> Ret ok} : M _); last first.
  bind_ext => x.
  case: safe1 => // h t.
  rewrite /step1 /=.
  by case: test.
transitivity
  (Do{ uds <- Get;
  let (b', uds'') := safe1 uds crs in
  let (b, uds''') := test cr uds'' in
  let (ok, uds') := (b && b', uds''') in (Put uds'' >> Put uds' >> Ret ok)} : M _); last first.
  bind_ext => x.
  case: safe1 => // h t.
  case: test => // a b.
  by rewrite putput.
(* move two of the lets *)
transitivity
  (Do{ uds <- Get;
  let (b', uds'') := safe1 uds crs in
  Put uds'' >>
  let (b, uds''') := test cr uds'' in
  let (ok, uds') := (b && b', uds''') in Put uds' >> Ret ok} : M _); last first.
  bind_ext => x.
  case: safe1 => // h t.
  case: test => // a b.
  by rewrite bindA.
transitivity
  (Do{ uds <- Get;
  let (b', uds'') := safe1 uds crs in
  Put uds'' >>
  Do{ uds'''' <- Get ;
  let (b, uds''') := test cr uds'''' in
  let (ok, uds') := (b && b', uds''') in Put uds' >> Ret ok}} : M _); last first.
  bind_ext => x.
  case: safe1 => // h t.
  by rewrite -bindA putgetput.
transitivity
  (Do{
   b' <- Do{uds <- Get ; let (ok, uds'') := safe1 uds crs in Put uds'' >> Ret ok} ;
   Do{ uds'''' <- Get;
   let (b, uds''') := test cr uds'''' in
   let (ok, uds') := (b && b', uds''') in Put uds' >> Ret ok}} : M _); last first.
  rewrite bindA; bind_ext => x.
  case: safe1 => // h t.
  by rewrite bindA; rewrite_ bindretf.
by [].
Qed.

End statefully.

End nqueens.

Definition test_nonce0 (M : stateMonad nat) : M nat :=
  Get >>= (fun s => Put s.+1 >> Ret s).
Reset test_nonce0.
Fail Check test_nonce0.

(* mu (wip) *)

(* TODO: move *)
Lemma skip_fapp (M : monad) A B (m : M B) (f : A -> B) g :
  (m >> (f ($) g)) = (f ($) (m >> g)) :> M _.
Proof. by rewrite fapp_bind. Qed.

Section scanl.

Variables A B : Type.

Fixpoint scanlp (op : B -> A -> B) (b : B) (s : seq A) : seq B :=
  if s isn't x :: xs then [::] else (op b x) :: scanlp op (op b x) xs.

End scanl.

Definition overwrite {A S} {M : stateMonad S} s a : M A :=
  Put s >> Ret a .

Section loop.

Variables (A S : Type) (M : stateMonad S).

Definition loopp (op : S -> A -> S) (s : S) (xs : seq A) : M (seq S) :=
  let mul x m := Get >>= fun st => let st' := op st x in cons st' ($) (Put st' >> m) in
  Put s >> foldr mul (Ret [::]) xs.

Lemma loopp_nil (op : S -> A -> S) (s : S) : loopp op s [::] = Put s >> Ret [::].
Proof. by []. Qed.

Lemma loop_of_scanl' (s : S) (ms : M S) (mu mu' : M unit) (g : M (seq S)) (f : S -> M unit) :
  Do{ x0 <- ms; mu >> Do{ xs <- cons s ($) (mu' >> g); f x0 >> Ret xs}} =
  cons s ($) Do{ x0 <- ms; mu >> mu' >> Do{ xs <- g; f x0 >> Ret xs}}.
Proof.
rewrite /fapp /fmap !bindA.
rewrite_ bindA.
bind_ext => x.
rewrite !bindA; bind_ext; case.
bind_ext; case.
rewrite_ bindretf.
rewrite_ bindA.
With (rewrite_ bindretf) Open (X in _ = _ >>= X).
  reflexivity.
by [].
Qed.

Lemma loop_of_scanl (op : S -> A -> S) (s : S) (xs : seq A) :
  Ret (scanlp op s xs) = Do{ ini <- Get; loopp op s xs >>= overwrite ini}.
Proof.
elim: xs s => [/=|x xs IH] s.
  rewrite loopp_nil.
  rewrite_ bindA.
  rewrite_ bindretf.
  rewrite /overwrite.
  Inf rewrite -bindA.
  rewrite_ putput.
  rewrite -bindA.
  rewrite getputskip.
  by rewrite bindskipf.
rewrite /loopp /overwrite [in RHS]/=.
set mul := fun (x0 : A) m => _.
Inf rewrite !bindA.
(* TODO(rei): tactic for nested function bodies? *)
transitivity (Do{ x0 <- Get;
  (Put s >>
  Get) >>= fun x1 =>
  Do{ a <- cons (op x1 x) ($) (Put (op x1 x) >> foldr mul (Ret [::]) xs); Put x0 >> Ret a}}); last first.
  by Inf rewrite !bindA.
rewrite_ putget.
rewrite_ bindA.
rewrite_ bindretf.
rewrite loop_of_scanl'.
transitivity (cons (op s x)
  ($) Do{ x0 <- Get; Put (op s x) >> Do{ a <- foldr mul (Ret [::]) xs; Put x0 >> Ret a}}); last first.
  congr (_ ($) _).
  by rewrite_ putput.
transitivity (cons (op s x) ($) Do{ x0 <- Get; loopp op (op s x) xs >>= overwrite x0}); last first.
  congr (_ ($) _).
  by Inf rewrite -bindA.
by rewrite -IH fapp_ret.
Qed.

End loop.

(* end of mu (wip) *)

(* NB(rei): not used yet *)
Module MonadStateRun.
Record mixin_of S (M : stateMonad S) : Type := Mixin {
  run0 : forall A, M A -> S -> A * S ;
  _ : forall A (a : A) s, run0 (Ret a) s = (a, s) ;
  _ : forall A B (m : M A) (f : A -> M B) s,
      run0 (Do{ a <- m ; f a}) s =
      let: (a', s') := run0 m s in run0 (f a') s' ;
  _ : forall s, run0 Get s = (s, s) ;
  _ : forall s s', run0 (Put s') s = (tt, s') ;
}.
Record class_of S (m : Type -> Type) := Class {
  base : MonadState.class_of S m ;
  mixin : mixin_of (MonadState.Pack base)
}.
Structure t S : Type := Pack { m : Type -> Type ;
  class : class_of S m }.
Definition op_run0 S (M : t S) : forall A, m M A -> S -> A * S :=
  let: Pack _ (Class _ (Mixin x _ _ _ _)) := M
  return forall A, m M A -> S -> A * S in x.
Arguments op_run0 {S M A} : simpl never.
Definition baseType S (M : t S) := MonadState.Pack (base (class M)).
Module Exports.
Notation Run0 := op_run0.
Coercion baseType : MonadStateRun.t >-> stateMonad.
Canonical baseType.
End Exports.
End MonadStateRun.
Export MonadStateRun.Exports.

Section staterun_lemmas.
Variables (S : Type) (M : MonadStateRun.t S).
Lemma runret : forall A (a : A) s, Run0 (Ret a : M _) s = (a, s).
Proof. by case: M => m [? []]. Qed.
Lemma runbind : forall A B (ma : M A) (f : A -> M B) s,
  Run0 (Do{ a <- ma ; f a}) s = let: (a'', s'') := Run0 ma s in Run0 (f a'') s''.
Proof. by case: M => m [? []]. Qed.
Lemma runget : forall s, Run0 (Get : M _) s = (s, s).
Proof. by case: M => m [? []]. Qed.
Lemma runput : forall s s', Run0 (Put s' : M _) s = (tt, s').
Proof. by case: M => m [? []]. Qed.
End staterun_lemmas.

Module MonadNondetState.
Record mixin_of (M : nondetMonad) : Type := Mixin {
  (* backtrackable state *)
  _ : Laws.right_zero (@Bind M) (@Fail _) ;
  (* composition distributes rightwards over choice *)
  _ : Laws.bind_right_distributive (@Bind M) [~p]
}.
Record class_of S (m : Type -> Type) : Type := Class {
  base : MonadNondet.class_of m ;
  mixin : MonadState.mixin_of S (MonadFail.baseType (MonadNondet.baseType (MonadNondet.Pack base))) ;
  ext : mixin_of (MonadNondet.Pack base)
}.
Structure t S : Type := Pack { m : Type -> Type ; class : class_of S m }.
Definition baseType S (M : t S) := MonadNondet.Pack (base (class M)).
Module Exports.
Notation nondetStateMonad := t.
Coercion baseType : nondetStateMonad >-> nondetMonad.
Canonical baseType.
Definition nondetstate_is_state S (M : nondetStateMonad S) :=
  MonadState.Pack (MonadState.Class (mixin (class M))).
Canonical nondetstate_is_state.
End Exports.
End MonadNondetState.
Export MonadNondetState.Exports.

Section nondetstate_lemmas.
Variables (S : Type) (M : nondetStateMonad S).
Lemma bindmfail : Laws.right_zero (@Bind M) (@Fail _).
Proof. by case: M => m [? ? [? ?]]. Qed.
Lemma alt_bindDr : Laws.bind_right_distributive (@Bind M) [~p].
Proof. by case: M => m [? ? []]. Qed.
End nondetstate_lemmas.

(* guards commute with anything *)
Lemma guardsC (M : failMonad) (HM : Laws.right_zero (@Bind M) (@Fail _)) b B (m : M B) :
  (guard b >> m) = (m >>= fun x => guard b >> Ret x).
Proof.
rewrite /guard; case: ifPn => Hb.
  rewrite bindskipf.
  rewrite_ bindskipf.
  by rewrite bindmret.
rewrite_ bindfailm.
by rewrite bindfailm HM.
Qed.

Lemma putselectC S (M : nondetStateMonad S) (x : S) A (s : seq A) B (f : _ -> M B) :
  Put x >> Do{ rs <- select s; f rs} =
  Do{ rs <- select s; Put x >> f rs}.
Proof.
elim: s f => [|h t IH] f.
  by rewrite select_nil 2!bindfailm bindmfail.
case: t IH f => [|h' t] IH f.
  by rewrite select_singl_statement !bindretf.
rewrite select_cons // => H.
rewrite [in LHS]alt_bindDl [in RHS]alt_bindDl.
rewrite alt_bindDr.
congr (_ [~i] _).
  by rewrite 2!bindretf.
rewrite 2!bindA IH.
bind_ext => y.
by rewrite !bindretf.
Qed.

(* perms is independent of the state and so commutes with put *)
Lemma putpermsC S (M : nondetStateMonad S) (x : S) A (s : seq A) B (f : _ -> M B) :
  Put x >> Do{ rs <- perms s; f rs} =
  Do{ rs <- perms s; Put x >> f rs}.
Proof.
move Hn : (size s) => n.
elim: n s Hn x f => [|n IH] s Hn x f.
  case: s Hn => // _; by rewrite perms_nil 2!bindretf.
case: s Hn => // h t [Hn].
rewrite perms_cons 2!bindA putselectC; bind_ext; case=> a b.
rewrite 2!bindA.
have bn : size b = n by rewrite size_tuple.
rewrite (IH _ bn x (fun z => Do{ rs <- Ret ((a, b).1 :: z); f rs})).
by do 2! rewrite_ bindretf.
Qed.

Lemma getput_prepend S (M : nondetStateMonad S) A (m : M A) :
  m = Do{x <- Get; (Put x >> m)} :> M _.
Proof. by rewrite -{2}(bindskipf m) -bindA getputskip 2!bindskipf. Qed.

Section queens_statefully_nondeterministically.

Context {M : nondetStateMonad (seq nat)`2}.

Definition queens_state_nondeter n : M (seq nat) :=
  Do{s <- Get ;
    Do{rs <- perms (iota 1 n);
      Put empty >>
        (Do{ ok <- safe2 (place n rs) ;
             (Put s >> guard ok)}) >> Ret rs }}.

Lemma queensE n : queens n = queens_state_nondeter n :> M _.
Proof.
rewrite (getput_prepend (queens n)) /queens_state_nondeter; bind_ext => x.
rewrite {1}/queens putpermsC; bind_ext => y.
rewrite safe2E.
set f := (Do{ ok <- Do{_ <- _; _}; _ >> guard ok} in RHS).
rewrite (_ : f =
  Do{ uds <- Get; Put (safe1 uds (place n y)).2 >> Ret (safe1 uds (place n y)).1 >>
      Put x >> guard (safe1 uds (place n y)).1}); last first.
  rewrite {}/f bindA; bind_ext => u.
  case: (safe1 _ _) => a b.
  rewrite 2!bindA bindretf bindA.
  by rewrite_ bindretf.
rewrite -bindA; congr (_ >> _).
rewrite -bindA.
rewrite putgetput.
rewrite 2!bindA.
rewrite bindretf.
rewrite -2!bindA.
by rewrite 2!putput.
Qed.

End queens_statefully_nondeterministically.

Section queens_exploratively.

Context {M : nondetStateMonad (seq nat)`2}.

Definition queens_explor n : M _ :=
  Do{s <- Get;
    Do{rs <- perms (iota 1 n);
      Put empty >>
        (Do{ ok <- safe2 (place n rs) ;
             (guard ok >> Put s)}) >> Ret rs }}.

Lemma queens_explorE n : queens_explor n = queens_state_nondeter n.
Proof.
rewrite /queens_explor /queens_state_nondeter.
bind_ext => x.
bind_ext => y.
rewrite 2!bindA.
bind_ext => z.
rewrite 2!bindA.
bind_ext => u.
rewrite guardsC; last exact: bindmfail.
rewrite 2!bindA.
rewrite_ bindA.
by rewrite_ bindretf.
Qed.

Definition safe3 crs : M _ := safe2 crs >>= fun b => guard b.

Definition queens_safe3 n : M _ :=
  Do{s <- Get;
    Do{rs <- perms (iota 1 n);
      Put empty >> safe3 (place n rs) >> Put s >> Ret rs}}.

Lemma queens_safe3E n : queens_safe3 n = queens_explor n :> M _.
Proof.
rewrite /queens_safe3 /queens_explor; bind_ext => x.
bind_ext => y.
rewrite 3!bindA.
bind_ext; case.
rewrite !bindA.
by rewrite_ bindA.
Qed.

Definition step3 B cr (m : M B) := m >>
  Do{ uds <- Get ; let (b, uds') := test cr uds in Put uds' >> guard b}.

Lemma safe3E crs :
  safe3 crs = foldr (@step3 unit) skip crs :> M _.
Proof.
(* TODO(rei): how to write this proof w.o. the "set" and "transitivity"'s? *)
transitivity (((fun x => x >>= (guard : _ -> M _)) \o
               (foldr step2 start2))
              crs).
  by [].
apply foldr_fusion_ext => [|cr {crs}k].
  by rewrite /= /safe3 /= /start2 /= bindretf.
transitivity (Do{ b' <- k ;
                  Do{ uds <- Get ;
                      let (b, uds') := test cr uds in
                      Put uds' >> Ret (b && b')}} >>= guard).
  by rewrite /step2.
transitivity (Do{ b' <- k ;
                  Do{ uds <- Get ;
                      let (b, uds') := test cr uds in
                      Put uds' >> guard (b && b')}}).
  (* by "do-notation" *)
  rewrite bindA; bind_ext => x.
  rewrite bindA; bind_ext => y.
  case: (test cr y) => a b.
  by rewrite bindA bindretf.
transitivity (Do{ b' <- k ;
                  Do{ uds <- Get ;
                      let (b, uds') := test cr uds in
                      Put uds' >> guard b >> guard b'}}).
  bind_ext => x.
  bind_ext => y.
  case: (test cr y) => a b.
  by rewrite bindA guard_and.
transitivity (Do{ b' <- k ;
                  guard b' >> Do{ uds <- Get ;
                      let (b, uds') := test cr uds in
                      Put uds' >> guard b}}).
  bind_ext => b'.
  rewrite guardsC; last exact: bindmfail.
  rewrite bindA.
  bind_ext => x.
  case: test => h t.
  rewrite 2!bindA.
  bind_ext; case.
  rewrite -guard_and andbC guard_and guardsC //.
  exact: bindmfail.
transitivity ((k >>= guard) >>
               Do{ uds <- Get ;
                 let (b, uds') := test cr uds in
                  Put uds' >> guard b}).
  by rewrite bindA.
by [].
Qed.

End queens_exploratively.

(* tree-relabelling example *)

Definition intersect (A : eqType) (s t : seq A) : seq A := filter (mem s) t.

Lemma nilp_intersect (A : eqType) (s t : seq A) :
  nilp (intersect s t) = ~~ has (mem s) t.
Proof. by rewrite /intersect /nilp size_filter has_count lt0n negbK. Qed.

Definition seq_disjoint (A : eqType) : pred [eqType of (seq A)`2] :=
  (@nilp _) \o uncurry (@intersect _).

Lemma intersect0s (A : eqType) (s : seq A) : intersect [::] s = [::].
Proof. by elim: s. Qed.

Module MonadFresh.
Record mixin_of (S : eqType) (m : Type -> Type) : Type := Mixin {
  fresh : m S }.
Record class_of S (m : Type -> Type) : Type := Class {
  base : Monad.class_of m ;
  mixin : mixin_of S m }.
Structure t S := Pack { m : Type -> Type ; class : class_of S m }.
Definition op_fresh S (M : t S) : m M S :=
  let: Pack _ (Class _ (Mixin x)) := M return m M S in x.
Arguments op_fresh {S M} : simpl never.
Definition baseType S (M : t S) := Monad.Pack (base (class M)).
Module Exports.
Notation Fresh := op_fresh.
Notation freshMonad := t.
Coercion baseType : freshMonad >-> monad.
Canonical baseType.
End Exports.
End MonadFresh.
Export MonadFresh.Exports.

Definition promotable A (p : pred (seq A)) (q : pred (seq A * seq A)) :=
  forall s t, p s -> p t -> p (s ++ t) = q (s, t).

Module segment_closed.
Record t A := mk {
  p : pred (seq A) ;
  H : forall a b, p (a ++ b) -> p a /\ p b }.
End segment_closed.
Definition segment_closed_p A := @segment_closed.p A.
Coercion segment_closed_p : segment_closed.t >-> pred.

Lemma segment_closed_suffix A (p : segment_closed.t A) s :
  ~~ p s -> forall t, ~~ p (s ++ t).
Proof. move=> ps t; apply: contra ps; by case/segment_closed.H. Qed.

Lemma segment_closed_prefix A (p : segment_closed.t A) s :
  ~~ p s -> forall t, ~~ p (t ++ s).
Proof. move=> ps t; apply: contra ps; by case/segment_closed.H. Qed.

(* assert p distributes over concatenation *)
Definition promote_assert (M : failMonad) A
  (p : pred (seq A)) (q : pred (seq A * seq A)) :=
  (assert p) \o (fmap ucat) \o pair =
  (fmap ucat) \o (assert q) \o pair \o (assert p)`^2 :> (_ -> M _).

Lemma promote_assert_sufficient_condition (M : failMonad) A :
  Laws.right_zero (@Bind M) (@Fail _) ->
  forall (p : segment_closed.t A) q, promotable p q ->
  promote_assert M p q.
Proof.
move=> right_z p q promotable_pq.
rewrite /promote_assert.
rewrite [fmap]lock; apply functional_extensionality => -[x1 x2] /=; rewrite -lock.
rewrite {1}/assert [in RHS]/fmap !bindA.
bind_ext => s.
rewrite 2!bindA bindretf 2!bindA.
rewrite {1}[in RHS]/guard.
case: ifPn => ps; last first.
  rewrite bindfailm.
  Inf (rewrite 2!bindretf).
  With (idtac) Open (X in _ >>= X).
    rewrite /guard /= (negbTE (segment_closed_suffix ps x)) bindfailm.
    reflexivity.
  by rewrite right_z.
rewrite bindskipf; bind_ext => t.
rewrite 2![in LHS]bindretf.
rewrite bindA {1}[in RHS]/guard.
case: ifPn => pt; last first.
  by rewrite bindfailm /guard /= (negbTE (segment_closed_prefix pt s)) bindfailm.
by rewrite bindskipf 2!bindretf bindA bindretf promotable_pq.
Qed.

Section examples_promotable_segment_closed.

Lemma promotable_uniq_seq_disjoint A : promotable (@uniq A) (@seq_disjoint A).
Proof.
move=> s t ps pt.
by rewrite cat_uniq ps pt /= andbT -nilp_intersect /seq_disjoint.
Qed.

Program Definition uniq_is_segment_closed (A : eqType) : segment_closed.t A :=
  @segment_closed.mk _ (@uniq A) _.
Next Obligation. by move=> A a b; rewrite cat_uniq => /and3P[]. Qed.

(* is a contiguous segment of the enumeration *)
(* TODO(rei): generalize to any enumeration *)
Definition is_iota : pred (seq nat) := [pred x | x == iota (head O x) (size x) ].

Lemma is_iota_head_last s : is_iota s -> 0 < size s -> head 0 s + size s = (last 0 s).+1.
elim: s => //= a [_ /=|c d IH].
  by rewrite addn1.
rewrite /is_iota /= => /eqP[] ?; subst c => Hd _.
rewrite /= in IH.
by rewrite -IH // -?addSnnS // /is_iota /= -Hd.
Qed.

(* predicate "are adjacent segments" *)
Definition are_adjacent : pred (seq nat * seq nat)%type :=
  [pred xy | [|| xy.1 == [::] , xy.2 == [::] | (last O xy.1).+1 == head O xy.2]].

Lemma promotable_enum : promotable is_iota are_adjacent.
Proof.
move=> s t Hs Ht.
rewrite /is_iota /= size_cat iota_add.
case/boolP : (nilp s) => [/nilP ->{Hs s} /=|s0]; first by rewrite addn0 /are_adjacent.
rewrite /nilp -lt0n in s0.
have -> : head 0 (s ++ t) = head 0 s by rewrite -nth0 nth_cat sub0n s0.
rewrite -(eqP Hs) /are_adjacent /= -size_eq0 -(negbK (size s == _)) -lt0n s0 /=.
rewrite eqseq_cat // eqxx /=.
case/boolP : (nilp t) => [/nilP {Ht} ->{t} //|t0].
rewrite /nilp -lt0n in t0.
rewrite -(size_eq0 t) -(negbK (size t == _)) -lt0n t0 /=.
case: t Ht t0 => // a b Hab _.
rewrite [head _ (_ :: _)]/=.
rewrite is_iota_head_last //= eqseq_cons eq_sym andb_idr // => /eqP Ha.
move: Hab.
by rewrite /is_iota /= => /eqP[] {1}->; rewrite -Ha.
Qed.

Program Definition is_iota_is_segment_closed : segment_closed.t nat :=
  @segment_closed.mk _ is_iota _.
Next Obligation.
move=> a b.
rewrite /is_iota /= /= size_cat => /eqP Hab.
apply/andP; rewrite -eqseq_cat ?size_iota //; apply/eqP.
case/boolP : (nilp a) => [/nilP a0|a0]; first by move: Hab; rewrite a0.
case/boolP : (nilp b) => [/nilP b0|b0].
  by move: Hab; rewrite b0 /= !cats0 addn0.
have -> : head 0 b = head 0 a + size a.
  move/(congr1 (fun x => nth 0 x (size a))) : Hab.
  rewrite nth_cat ltnn subnn nth0 => ->; rewrite -nth0 nth_cat lt0n.
  by rewrite a0 nth0 nth_iota // -{1}(addn0 (size a)) ltn_add2l lt0n.
suff <- : head 0 (a ++ b) = head 0 a by rewrite -iota_add.
by rewrite -nth0 nth_cat lt0n a0.
Qed.

End examples_promotable_segment_closed.

Module MonadFailFresh.
Record mixin_of S (M : failMonad) (fresh : M S) : Type := Mixin {
  symbols := fun n => sequence (nseq n fresh);
  (* generated symbols are indeed fresh (specification of fresh) *)
  distinct : segment_closed.t S ;
  _ : assert distinct \o symbols = symbols ;
  (* failure is a right zero of composition (backtracking interpretation) *)
  _ : Laws.right_zero (@Bind M) (@Fail _)
}.
Record class_of S (m : Type -> Type) := Class {
  base : MonadFail.class_of m ;
  mixin : MonadFresh.mixin_of S m ;
  ext : @mixin_of S (MonadFail.Pack base) (MonadFresh.fresh mixin)
}.
Structure t S : Type := Pack { m : Type -> Type ; class : class_of S m }.
Definition op_symbols S (M : t S) :=
  let: Pack _ (Class _ _ (Mixin x _ _ _)) := M return nat -> m M (seq S) in x.
Arguments op_symbols {S M} : simpl never.
Definition op_distinct S (M : t S) :=
  let: Pack _ (Class _ _ (Mixin _ x _ _)) := M return segment_closed.t S in x.
Arguments op_distinct {S} M : simpl never.
Definition baseType S (M : t S) := MonadFail.Pack (base (class M)).
Module Exports.
Notation Symbols := op_symbols.
Notation distinct := op_distinct.
Notation failFreshMonad := t.
Coercion baseType : failFreshMonad >-> failMonad.
Canonical baseType.
Definition fresh_of_failfresh S (M : failFreshMonad S) : MonadFresh.t S :=
  @MonadFresh.Pack _ (MonadFailFresh.m M)
  (MonadFresh.Class (Monad.class (MonadFail.baseType (baseType M)))
                    (mixin (class M))).
Canonical fresh_of_failfresh.
End Exports.
End MonadFailFresh.
Export MonadFailFresh.Exports.

Section failfresh_lemmas.
Variables (S : eqType) (M : failFreshMonad S).
Lemma failfresh_bindmfail : Laws.right_zero (@Bind M) (@Fail _).
Proof. by case: M => m [? ? []]. Qed.
Lemma assert_symbols : assert (distinct M) \o Symbols = Symbols :> (nat -> M _).
Proof. by case: M => m [? ? []]. Qed.
End failfresh_lemmas.

Definition wrap {A} (a : A) := [:: a].

Section properties_of_Symbols.
Variables (A : eqType) (M : failFreshMonad A).

Lemma SymbolsE : Symbols = (fun n => sequence (nseq n Fresh)) :> (_ -> M _).
Proof. by case: M => m [? ? [? ? ? ?]]. Qed.

Lemma Symbols0 : Symbols 0 = Ret [::] :> M _.
Proof. by rewrite SymbolsE. Qed.

Lemma SymbolsS n : Symbols n.+1 =
  Do{ x <- Fresh ; Do{ xs <- Symbols n : M _; Ret (x :: xs)}}.
Proof. by rewrite SymbolsE. Qed.

Lemma Symbols_prop1 :
  Symbols \o const 1 = fmap wrap \o const Fresh :> (A -> M _).
Proof.
apply functional_extensionality => n.
transitivity (@Symbols _ M 1) => //.
rewrite SymbolsE sequence_cons sequence_nil.
by rewrite_ bindretf.
Qed.

Lemma Symbols_prop2 :
  Symbols \o uaddn = fmap ucat \o pair \o (Symbols : _ -> M _)`^2.
Proof.
apply functional_extensionality => -[n1 n2].
rewrite [fmap]lock /= -lock.
elim: n1 => [|n1 IH].
  rewrite add0n Symbols0 bindretf.
  rewrite /fmap bindA.
  With (rewrite bindretf) Open (X in _ >>= X).
  reflexivity.
  by rewrite bindmret.
rewrite addSn SymbolsS {}IH SymbolsS /fmap !bindA.
bind_ext => a.
rewrite !bindA.
(* TODO(rei): use bind_ext *)
congr Monad.op_bind; apply functional_extensionality => s.
rewrite bindretf 3!bindA.
by do 3 rewrite_ bindretf.
Qed.

End properties_of_Symbols.

Section Tree.
Variable A : Type.

Inductive Tree := Tip (a : A) | Bin of Tree & Tree.

Fixpoint foldt B (f : A -> B) (g : B * B -> B) (t : Tree) : B :=
  match t with
  | Tip a => f a
  | Bin t u => g (foldt f g t, foldt f g u)
  end.

Section foldt_universal.
Variables B : Type.
Variables (h : Tree -> B) (f : A -> B) (g : B * B -> B).
Hypothesis H1 : h \o Tip = f.
Hypothesis H2 : h \o uncurry Bin = g \o (fun x => (h x.1, h x.2)).
Lemma foldt_universal : h = foldt f g.
Proof.
apply functional_extensionality; elim => [a|]; first by rewrite -H1.
move=> t1 IH1 t2 IH2 /=;
rewrite -IH1 -IH2.
transitivity ((h \o uncurry Bin) (t1, t2)); first by [].
by rewrite H2.
Qed.
End foldt_universal.

Definition size_Tree (t : Tree) := foldt (const 1%nat) uaddn t.

Lemma size_Tree_Bin :
  size_Tree \o uncurry Bin = uncurry addn \o size_Tree`^2.
Proof. by apply functional_extensionality => -[x1 x2]. Qed.

Fixpoint labels (t : Tree) : seq A :=
  match t with
  | Tip a => [:: a]
  | Bin t u => labels t ++ labels u
  end.

End Tree.

Section tree_relabelling.

Variable Symbol : eqType. (* TODO: ideally, we would like a generic type here with a succ function *)
Variable M : failFreshMonad Symbol.
Variable q : pred (seq Symbol * seq Symbol).
Hypothesis promotable_q : promotable (distinct M) q.

Definition relabel : Tree Symbol -> M (Tree Symbol) :=
  foldt (fmap (@Tip _) \o const Fresh) (fmap (uncurry (@Bin _)) \o pair).

Let drTip {A} : A -> M _ :=
  fmap wrap \o const Fresh.
Let drBin {N : failMonad} : (N _ * N _ -> N _) :=
  fmap ucat \o assert q \o pair.

(* extracting the distinct symbol list *)
Definition dlabels {N : failMonad} : Tree Symbol -> N (seq Symbol) :=
  foldt (Ret \o wrap) drBin.

Lemma dlabelsC t u (m : _ -> _ -> M (seq Symbol * seq Symbol)%type) :
  Do{ x <- dlabels t; Do{ x0 <- relabel u; m x0 x}} =
  Do{ x0 <- relabel u; Do{ x <- dlabels t; m x0 x}}.
Proof.
elim: t u m => [a u /= m|t1 H1 t2 H2 u m].
  rewrite /dlabels /= bindretf.
  bind_ext => u'.
  by rewrite bindretf.
rewrite (_ : dlabels _ = drBin (dlabels t1, dlabels t2)) //.
rewrite {2}/drBin.
rewrite {1}/fmap /=.
rewrite {1}/assert /=.
rewrite ![in RHS]bindA.
transitivity (
  Do{ x0 <- relabel u;
    Do{ x <- dlabels t1;
    Do{ x <-
    Do{ x1 <- Do{ y <- dlabels t2; Ret (x, y)}; Do{ x <- guard (q x1) >> Ret x1; (Ret \o ucat) x}};
  m x0 x}}}); last first.
  bind_ext => u'.
  by rewrite !bindA.
rewrite -H1 {1}/drBin {1}/fmap /= {1}/assert /= !bindA.
bind_ext => s.
rewrite !bindA.
transitivity (Do{ x0 <- relabel u;
  Do{ x <- dlabels t2; Do{ x <-
    Do{ x1 <- Ret (s, x); Do{ x3 <- guard (q x1) >> Ret x1; Ret (ucat x3)}};
    m x0 x}}}); last first.
  bind_ext => y2; by rewrite bindA.
rewrite -H2.
bind_ext => s'.
rewrite !bindretf.
rewrite !bindA.
transitivity (guard (q (s, s')) >>
  Do{ x1 <- (Ret \o ucat) (s, s'); Do{ x3 <- relabel u; m x3 x1}}).
  bind_ext => tt_unit; by rewrite bindretf.
rewrite guardsC; last exact: failfresh_bindmfail.
rewrite !bindA.
rewrite !bindretf.
rewrite !bindA.
bind_ext => u'.
rewrite bindA.
rewrite guardsC; last exact: failfresh_bindmfail.
by rewrite bindA bindretf.
Qed.

Lemma join_and_pairs :
  ((@join _ _ \o fmap pair) \o pair) \o (fmap dlabels \o relabel)`^2 =
  (pair \o (@join _ _)`^2) \o (fmap dlabels \o relabel)`^2.
Proof.
apply functional_extensionality => -[x1 x2].
rewrite /join /= /fmap /=. (* TODO: lock join and fmap? *) (*NB: notation breaks*)
rewrite 5!bindA; bind_ext => {x1}x1.
rewrite 2!bindretf 3!bindA.
transitivity (Do{ x0 <- relabel x2; Do{ x <- dlabels x1;
  Do{ y <- Do{ x3 <- (Ret \o dlabels) x0; x3}; Ret (x, y)}}}).
  bind_ext => {x2}x2; by rewrite !bindretf.
transitivity (
  Do{ x <- dlabels x1; Do{ x0 <- relabel x2;
    Do{ y <- Do{ x3 <- (Ret \o dlabels) x0; x3}; Ret (x, y)}}}); last first.
  bind_ext => y1; by rewrite bindA.
by rewrite dlabelsC.
Qed.

(* first property of Sect. 9.3 *)
Lemma dlabels_relabel_is_fold :
  dlabels >=> relabel = foldt drTip drBin :> (Tree _ -> M (seq _)).
Proof.
apply foldt_universal.
  (* dlabels >=> relabel \o Tip = drTip *)
  rewrite /kleisli /= -3!compA.
  rewrite (_ : relabel \o _ = fmap (@Tip _) \o const Fresh); last by [].
  rewrite (compA (fmap dlabels) (fmap (@Tip _)) (const Fresh)) -fmap_o.
  rewrite (_ : dlabels \o _ = Ret \o wrap); last by [].
  rewrite compA /drTip; congr (_ \o _).
  rewrite fmap_o compA.
  by rewrite (@join_fmap_return M).
(* dlabels >=> relabel \o Bin = drBin \o _ *)
rewrite /kleisli -2![in LHS]compA.
rewrite (_ : relabel \o uncurry _ = fmap (uncurry (@Bin _)) \o (pair \o relabel`^2)); last first.
  by apply functional_extensionality; case.
rewrite (compA (fmap dlabels)) -fmap_o.
rewrite (_ : dlabels \o _ = fmap ucat \o assert q \o pair \o dlabels`^2); last first.
  by apply functional_extensionality; case.
transitivity (fmap ucat \o @join _ _ \o fmap (assert q \o pair) \o pair \o
    (fmap dlabels \o relabel)`^2).
  rewrite -2![in LHS](compA (fmap ucat)).
  rewrite [in LHS]fmap_o.
  rewrite -[in LHS](compA (fmap _)) [in LHS](compA _ (fmap _)).
  rewrite -join_naturality.
  rewrite -2![in RHS]compA; congr (_ \o _).
  rewrite fmap_o -[in LHS]compA; congr (_ \o _).
  by rewrite naturality_pair.
rewrite fmap_o (compA _ (fmap (assert q))) -(compA _ _ (fmap (assert q))).
rewrite commutativity_of_assertions. (* first non-trivial step (sic) *)
rewrite (compA _ (assert q)) -(compA _ _ (fmap pair)) -(compA _ _ pair) -(compA _ _ (_`^2)).
rewrite join_and_pairs. (* second non-trivial step *)
by [].
Qed.

(* second property of Sect. 9.3 *)
Lemma symbols_size_is_fold : Symbols \o (@size_Tree Symbol) =
  foldt (@drTip Symbol) drBin :> (Tree _ -> M (seq _)).
Proof.
apply foldt_universal.
  transitivity (Symbols \o (@size_Tree Symbol \o (@Tip _)) : (_ -> M _)).
    by [].
  transitivity (Symbols \o (const 1%nat : Symbol -> _) : (_ -> M _)).
    by [].
  by rewrite Symbols_prop1.
pose p := distinct M.
transitivity (assert p \o Symbols \o @size_Tree Symbol \o uncurry (@Bin Symbol)
  : (_ -> M _)).
  by rewrite assert_symbols.
transitivity ((assert p) \o Symbols \o uaddn \o (@size_Tree Symbol)`^2
  : (_ -> M _)).
  rewrite -[in LHS]compA -[in RHS]compA; congr (_ \o _).
  by rewrite size_Tree_Bin.
transitivity (assert p \o fmap ucat \o pair \o (Symbols \o (@size_Tree Symbol))`^2
  : (_ -> M _)).
  rewrite -2!compA (compA Symbols) Symbols_prop2.
  by rewrite -(compA (_ \o pair)) (compA (assert p)).
transitivity (fmap ucat \o (assert q) \o pair \o (assert p \o Symbols \o (@size_Tree Symbol))`^2
  : (_ -> M _)).
  (* assert p distributes over concatenation *)
  by rewrite (@promote_assert_sufficient_condition _ _ (@failfresh_bindmfail _ M) p q).
transitivity (fmap ucat \o (assert q) \o pair \o (Symbols \o (@size_Tree Symbol))`^2
  : (_ -> M _)).
  by rewrite assert_symbols.
by [].
Qed.

(* main claim *)
Lemma dlabels_relabel_never_fails :
  dlabels >=> relabel = Symbols \o @size_Tree Symbol :> (_ -> M _).
Proof. by rewrite dlabels_relabel_is_fold symbols_size_is_fold. Qed.

End tree_relabelling.
