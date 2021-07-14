(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2020 monae authors, license: LGPL-2.1-or-later               *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require boolp.
Require Import monae_lib hierarchy monad_lib fail_lib state_lib.
From infotheo Require Import ssr_ext.
(* Require Import Classical. *)

(******************************************************************************)
(*                            Quicksort example                               *)
(*                                                                            *)
(* wip!                                                                       *)
(******************************************************************************)

(* TODO: shouldn't prePlusMonad be plusMonad (like list monad) and
    plusMonad be plusCIMonad (like set monad) *)

Reserved Notation "A `<=` B" (at level 70, no associativity).
Reserved Notation "A `>=` B" (at level 70, no associativity).
Reserved Notation "A `<.=` B" (at level 70, no associativity).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope order_scope.
Import Order.TTheory.
Local Open Scope monae_scope.
Local Open Scope tuple_ext_scope.

(* TODO: move *)
Lemma kleisliE (M : monad) (A B C : UU0) (g : B -> M C) (f : A -> M B) (a : A) :
  (f >=> g) a = (f a) >>= g.
Proof. by rewrite /kleisli /= join_fmap. Qed.

Definition refin (M : altMonad) A (m1 m2 : M A) : Prop := m1 [~] m2 = m2.

Notation "m1 `<=` m2" := (refin m1 m2) : monae_scope.
Notation "m1 `>=` m2" := (refin m2 m1) : monae_scope.

Section refin_lemmas.
  Variable M : altCIMonad.
  Lemma refin_refl A (a : M A) : a `<=` a.
  Proof. by rewrite /refin altmm. Qed.

  Lemma refin_trans A (b a c : M A) :
  a `<=` b -> b `<=` c -> a `<=` c.
  Proof. by rewrite /refin => h1 <-; rewrite altA h1. Qed.

  Lemma refin_antisym A (a b : M A) :
  a `<=` b -> b `<=` a -> a = b.
  Proof. by rewrite /refin => h1 <-; rewrite altC. Qed.
End refin_lemmas.

Definition lrefin {M : altMonad} A B (f g : A -> M B) : Prop := 
  forall x, f x `<=`g x.

Notation "f `<.=` g" := (lrefin f g) : monae_scope.

Section lrefin_lemmas.
  Variable M : altCIMonad.
  Lemma lrefin_refl A B (a : A -> M B) : a `<.=` a.
  Proof. move => ?; exact: refin_refl. Qed.

  Lemma lrefin_trans A B (b a c : A -> M B) :
  a `<.=` b -> b `<.=` c -> a `<.=` c.
  Proof. move => ? ? ?; exact: refin_trans. Qed.

  Lemma lrefin_antisym A B (a b : A -> M B) :
  a `<.=` b -> b `<.=` a -> a = b.
  Proof. move => ? ?; rewrite boolp.funeqE => ?; exact: refin_antisym. Qed.
End lrefin_lemmas.

Lemma bind_monotonic_refin (M : altMonad) A B (m1 m2 : M A) (f : A -> M B) :
  (m1 `<=` m2) -> (m1 >>= f `<=` m2 >>= f).
Proof. by move=> m12; rewrite /refin -alt_bindDl m12. Qed.

Lemma bind_monotonic_lrefin (M : prePlusMonad) A B (m : M A) (f1 f2 : A -> M B) :
  (f1 `<.=` f2) -> (m >>= f1 `<=` m >>= f2).
Proof. 
  move=> f12; rewrite /refin -alt_bindDr.
  by bind_ext => a; apply f12.
Qed.

Section splits.
  Variable M : plusMonad.
  Variables (d : unit) (T : porderType d).

  Fixpoint splits {M : plusMonad} A (s : seq A) : M (seq A * seq A)%type :=
  if s isn't x :: xs then Ret ([::], [::]) else
    splits xs >>= (fun yz => Ret (x :: yz.1, yz.2) [~] Ret (yz.1, x :: yz.2)).

  Program Fixpoint tsplits {M : plusMonad} A (s : seq A) : M ((size s).-bseq A * (size s).-bseq A)%type :=
    if s isn't x :: xs then Ret (bseq0 _  _, bseq0 _ _) (*TODO: try to use [bseq of [::]]*) else
      tsplits xs >>= (fun '(ys, zs) => Ret (@Bseq _ _ (x :: ys) _ , @Bseq _ _ zs _) [~]
                                      Ret (@Bseq _ _  ys _, @Bseq _ _ (x :: zs) _)).
  Next Obligation. by rewrite (leq_ltn_trans (size_bseq b)). Qed.
  Next Obligation. by rewrite (leq_trans (size_bseq b0)). Qed.
  Next Obligation. by rewrite (leq_trans (size_bseq b)). Qed.
  Next Obligation. by rewrite (leq_ltn_trans (size_bseq b0)). Qed.

  (* Goal forall M, @splits M nat [::] = Ret ([::], [::]). by []. Abort. *)

  (* Goal forall M, @splits M _ [:: O; 1]%nat = Ret ([::], [::]).
  move=> M.
  rewrite /= bindretf alt_bindDl !bindretf.
  Abort. *)

  Local Open Scope mprog.
  Lemma splitsE A (s : seq A) :
    splits s = fmap (fun xy => (bseqval xy.1, bseqval xy.2)) (tsplits s) :> M _.
  Proof.
  elim: s => /= [|h t ih]; first by rewrite fmapE bindretf.
  rewrite {}ih /= !fmapE 2!bindA; bind_ext => -[a b] /=.
  by rewrite bindretf alt_bindDl 2!bindretf.
  Qed.
  
  Local Close Scope mprog.
End splits.

Section qperm.
  Variables (M : plusMonad) (A : UU0).
  Variables (d : unit) (T : porderType d).

  Local Obligation Tactic := idtac.
  Program Definition qperm' (s : seq A)
      (f : forall s', size s' < size s -> M (seq A)) : M (seq A) :=
    if s isn't x :: xs then Ret [::] else
      tsplits xs >>= (fun a => let: (ys, zs) := a in liftM2 (fun a b => a ++ [:: x] ++ b) (f ys _) (f zs _)).
  Next Obligation.
  move=> [|h t] // ht x xs [xh xst] [a b ys zs] [-> zsb].
  by apply: (leq_ltn_trans (size_bseq a)); rewrite xst.
  Qed.
  Next Obligation.
  move=> [|h t] // ht x xs [xh xst] [a b ys zs] [ysa ->].
  by apply: (leq_ltn_trans (size_bseq b)); rewrite xst.
  Qed.
  Next Obligation. by move=> /= s _ x xs. Qed.

  Definition qperm : seq A -> M (seq A) :=
    Fix (@well_founded_size _) (fun _ => M _) qperm'.

  Lemma qperm'_Fix (s : seq A) (f g : forall y, (size y < size s)%N -> M (seq A)) :
    (forall y (p : (size y < size s)%N), f y p = g y p) -> qperm' f = qperm' g.
  Proof.
    move=> H; rewrite /qperm'; case: s f g H => // h t f g H.
    bind_ext => -[a b] /=; rewrite /liftM2 H (_ : f = g) //.
    apply fun_ext_dep => s.
    by rewrite boolp.funeqE=> p; exact: H.
  Qed.

  Lemma qperm_nil : qperm [::] = Ret [::].
  Proof. by rewrite /qperm (Fix_eq _ _ _ qperm'_Fix). Qed.

  Lemma qperm_cons x xs :
    qperm (x :: xs) = splits xs >>= (fun a => let: (ys, zs) := a in
                      liftM2 (fun a b => a ++ [:: x] ++ b) (qperm ys) (qperm zs)).
  Proof.
  rewrite {1}/qperm {1}(Fix_eq _ _ _ qperm'_Fix) /=.
  rewrite splitsE /= fmapE bindA; bind_ext => -[s1 s2] /=.
  by rewrite bindretf.
  Qed.

  Lemma qperm_consE x xs :
    qperm (x :: xs) = splits xs >>= (fun z =>
    liftM2 (fun a b => a ++ [:: x] ++ b) (qperm z.1) (qperm z.2)).
  Proof. by rewrite qperm_cons; bind_ext => -[]. Qed.
    
  Definition qpermE := (qperm_nil, qperm_cons).
    
End qperm.

Arguments qperm {M} {A}.

Section guard_commute.
  Variable M : plusMonad.
  Variables (d : unit) (T : porderType d).

  Definition nondet_plusMonad (M : plusMonad) A (n : M A) :=
    {m | ndDenote m = n}.

  Lemma commute_plusMonad
    A (m : M A) B (n : M B) C (f : A -> B -> M C) :
    nondet_plusMonad m -> commute m n f.
  Proof.
  case => x.
  elim: x m n f => [{}A a m n f <-| B0 {}A n0 H0 n1 H1 m n2 f <- |
    A0 m n f <- | A0 n0 H0 n1 H1 m n2 f <-].
  - rewrite /commute bindretf.
    by under [RHS] eq_bind do rewrite bindretf.
  - rewrite /commute /= !bindA.
    transitivity (do x <- ndDenote n0; do y <- n2; ndDenote (n1 x) >>= f^~ y)%Do.
      bind_ext => s.
      by rewrite (H1 s).
    rewrite H0 //.
    bind_ext => b.
    by rewrite bindA.
  - rewrite /commute /= bindfailf.
    transitivity (n >> fail : M C).
      by rewrite (@bindmfail M).
    bind_ext => b.
    by rewrite (@bindfailf M).
  - rewrite /commute /= alt_bindDl.
    transitivity (do y <- n2; ndDenote n0 >>= f^~ y [~]
                            ndDenote n1 >>= f^~ y)%Do; last first.
      bind_ext => a.
      by rewrite alt_bindDl.
    by rewrite alt_bindDr H0 // H1.
  Qed.

  Lemma commute_guard_n
    (b : bool) B (n : M B) C (f : unit -> B -> M C) :
    commute (guard b) n f.
    (* guard b >>  *)
  Proof.
    rewrite /commute.
    rewrite commute_plusMonad => [//|]; exists (if b then ndRet tt else @ndFail _).
    by case: ifP; rewrite (guardT, guardF).
  Qed.

  (*Definition invariant_by_qperm (p : pred (seq T)) :=
    forall s, p s -> qperm s >>= (fun x => guard (p x)) = Ret true.*)

  Lemma guard_splits A (p : pred T) (t : seq T) (f : seq T * seq T -> M A) :
    guard (all p t) >> (splits t >>= f)
    =
    splits t >>= (fun x => guard (all p x.1) >>
                           guard (all p x.2) >> f x).
  Proof.
    elim: t p A f => [p A f|h t ih p A f].
    by rewrite /= 2!bindretf /= guardT bindmskip.
    rewrite /= guard_and !bindA ih -bindA.
    rewrite (@guardsC M (@bindmfail M) _) bindA.
    (* bind_ext => -[a b].
    rewrite assertE bindA bindretf bindA /=.
    rewrite [in RHS]alt_bindDl /=.
    do 2 rewrite bindretf /= guard_and !bindA.
    rewrite -!bindA.
    rewrite [in RHS](@guardsC M (@bindmfail M) (all p a)).
    rewrite !bindA -alt_bindDr.
    bind_ext; case; rewrite assertE bindmskip -[in RHS]alt_bindDr.
    by bind_ext; case; rewrite alt_bindDl /= 2!bindretf -alt_bindDr. *)
  Admitted.

  Lemma guard_splits' A (p : pred T) (t : seq T) (f : seq T * seq T -> M A) :
    splits t >>= (fun x => guard (all p t) >> f x) =
    splits t >>= (fun x => (guard (all p x.1) >> guard (all p x.2)) >> f x).
  Proof.
    rewrite -guard_splits (@guardsC M (@bindmfail M) _) bindA.
    by bind_ext => -[a b]; rewrite guardsC; last exact : (@bindmfail M).
  Abort.

  Lemma guard_splits_cons A h (p : pred T) (t : seq T) (f : seq T * seq T -> M A) :
    guard (all p (h :: t)) >> (splits t >>= f)
    =
    splits t >>= (fun x => guard (all p x.1) >>
                           guard (all p x.2) >>
                           guard (p h) >> f x).
  Proof.
    rewrite /= guard_and bindA guard_splits commute_guard_n.
    bind_ext => -[a b] /=.
    by rewrite -bindA -!guard_and andbC.
  Qed.

  Lemma guard_qperm_eq B (p : pred T) (a : seq T) (f : seq T -> M B) :
    guard (all p a) >>= (fun _ => qperm a >>= f) =
    qperm a >>= (fun x => guard (all p x) >> f x).
  Proof.
    move: p.
    have [n leMn] := ubnP (size a); elim: n => // n ih in a f leMn *.
    move: a leMn.
    case.
    by move=> _ p; rewrite /= qperm_nil 2!bindretf /=.
    move => h t.
    rewrite ltnS => tn p.
    rewrite qperm_consE {1}/liftM2 !bindA /= guard_and [in LHS]bindA.
    rewrite -bindA -guard_and.
    rewrite guard_splits_cons /liftM2.
    rewrite splitsE /= fmapE !bindA /=.
    bind_ext => -[a b] /=.
    rewrite 2!bindretf /=.
    (* transitivity (
      ((guard (all p b) >> guard (p h)) >> guard (all p a) >>
      (do x <- do x1 <- qperm a; do x2 <- qperm b; Ret (x1 ++ h :: x2); f x)%Do)
      ). *)
    rewrite -2!guard_and andbC andbA andbC andbA 2!guard_and !bindA.
    rewrite ih; last by rewrite (leq_trans _ tn) //= ltnS size_bseq.
    (* transitivity (
      (do x0 <- qperm a; ((guard (p h) >> guard (all p x0)) >> guard (all p b))
      >> (do x1 <- do x2 <- qperm b; Ret (x0 ++ h :: x2); f x1)%Do)%Do
    ). *)
    rewrite -bindA -guard_and commute_guard_n.
    bind_ext => ?.
    rewrite -bindA -guard_and andbC andbA andbC andbA 2!guard_and !bindA.
    rewrite ih; last by rewrite (leq_trans _ tn) //= ltnS size_bseq.
    (* transitivity (
      (do x2 <- qperm b; ((guard (p h) >> guard (all p x0)) >> guard (all p x2)) >>
      (do x3 <- Ret (x0 ++ h :: x2); f x3)%Do)%Do
    ). *)
    rewrite -bindA -guard_and commute_guard_n.
    bind_ext => ?.
    by rewrite -bindA -!guard_and 2!bindretf -all_rcons -cat_rcons all_cat.
  Qed.

  Lemma guard_qperm_neq (B : Type) (b a : seq T) (r : pred T) (f : seq T -> M B) :
    guard (all r b) >> (qperm a >>= f) =
    qperm a >>= (fun x => (guard (all r b) >> f x)).
  Proof. by rewrite commute_guard_n. Qed.

End guard_commute.

Lemma guard_neg (M : plusMonad) A (p : bool) (m1 m2 : M A) :
  (if p then m1 else m2) `<=` (guard p >> m1) [~] (guard (~~ p) >> m2).
Proof.
rewrite /refin; case: ifPn => /= [pT|pF]; rewrite !(guardT,guardF).
by rewrite bindskipf bindfailf altA altmm.
by rewrite bindfailf bindskipf altCA altmm.
Qed.

Section sorted.
  Variables M : plusMonad.
  Variables (d : unit) (T : porderType d).
  (* Variables (r : rel T) (r_trans : transitive r). *)

  Lemma sorted_cons (r : rel T) (r_trans : transitive r) x (xs : seq T) :
  sorted r (x :: xs) = sorted r xs && all (r x) xs.
  Proof.
    apply/idP/idP => [ /= xxs |/andP[ _ /path_min_sorted /= ->//]].
    rewrite (order_path_min r_trans xxs) ?andbT//.
    exact: path_sorted xxs.
  Qed.

  Lemma sorted_rcons (r : rel T) (r_trans : transitive r) x (xs : seq T) :
    sorted r (rcons xs x) = sorted r xs && all (r^~ x) xs.
  Proof.
    rewrite -rev_sorted rev_rcons sorted_cons.
    by rewrite rev_sorted all_rev.
    apply /rev_trans /r_trans.
  Qed.

  Local Notation sorted := (sorted <=%O).

  Lemma sorted_cons' : forall (x : T) (xs : seq T),
    sorted (x :: xs) = sorted xs && all (<=%O x) xs.
  Proof. move => x xs. by rewrite sorted_cons //; apply le_trans. Qed.

  Lemma sorted_rcons' (x : T) (xs : seq T) :
  sorted (rcons xs x) = sorted xs && all (>=%O x) xs.
  Proof. by rewrite sorted_rcons //; apply le_trans. Qed.

  Lemma sorted_cat' (a b : seq T) : sorted (a ++ b) -> sorted a && sorted b.
  Proof.
  elim: a b => //= h t ih b; rewrite cat_path => /andP[-> /=].
  exact: path_sorted.
  Qed.

  Lemma sorted_cat_cons' (x : T) (ys zs : seq T) : 
    sorted (ys ++ x :: zs) = [&& sorted ys, sorted zs, all (<= x) ys & all (>= x) zs].
  Proof.
    apply/idP/idP => [|].
    rewrite -cat1s => H; apply/and4P; split; move: H.
    by move/sorted_cat' => /andP[].
    by move/sorted_cat'; rewrite sorted_cons' => /and3P[]. 
    by rewrite -cat_rcons => /sorted_cat'/andP[]; rewrite sorted_rcons' => /andP[].
    by move/sorted_cat' => /andP[_]; rewrite sorted_cons' => /andP[].
    case/and4P => ss ss' ps ps'; apply sorted_cat => //.
    by rewrite sorted_cons' ss' ps'.
    move => a ain b bin; apply (@le_trans _ _ x).
    by move: ps => /allP; apply.
    by move: bin ps'; rewrite inE => /orP[/eqP ->//|] => /allP; apply.
  Qed.

End sorted.

Local Notation sorted := (sorted <=%O).

Section slowsort.
  Variable M : plusMonad.
  Variables (d : unit) (T : porderType d).

  Definition is_partition p (yz : seq T * seq T) := all (<= p) yz.1 && all (>= p) yz.2.

  Definition slowsort : seq T -> M (seq T) :=
    (qperm >=> assert sorted)%monae.
  
  Lemma slowsort_nil : slowsort [::] = Ret [::].
  Proof. 
    rewrite /slowsort.
    by rewrite kleisliE qpermE bindretf assertE guardT bindskipf. 
  Qed.

  Lemma refin_slowsort_inductive_case (p : T) (xs : seq T) :
    slowsort (p :: xs) =
    splits xs >>= (fun yz => guard (is_partition p yz) >>
      (qperm yz.1 >>= assert sorted) >>= (fun ys' =>
      (qperm yz.2 >>= assert sorted) >>= (fun zs' =>
      Ret (ys' ++ [:: p] ++ zs')))).
  Proof.
  transitivity (
    splits xs >>= (fun '(ys, zs) =>
    qperm ys >>= (fun ys' => qperm zs >>= (fun zs' =>
    assert sorted (ys' ++ [:: p] ++ zs')))) : M _
  ).
    rewrite /slowsort kleisliE qperm_cons !bindA.
    bind_ext => -[a b] /=.
    rewrite /liftM2 bindA; bind_ext => s.
    by rewrite bindA; bind_ext => s'; rewrite bindretf.
  transitivity (
    splits xs >>= (fun '(ys, zs) =>
    qperm ys >>= (fun ys' => qperm zs >>= (fun zs' =>
    guard ([&& sorted ys', sorted zs', all (<= p) ys' & all (>= p) zs']) >>
    Ret (ys' ++ [:: p] ++ zs')))) : M _
  ).
    bind_ext => -[a b]; bind_ext => s; bind_ext => s'; rewrite assertE /=.
    by rewrite -sorted_cat_cons'.
    bind_ext=> {xs} -[a b].
    rewrite guard_and 2!bindA (bindA (qperm a)).
    rewrite guard_qperm_neq.
    rewrite guard_qperm_eq.
    bind_ext => s.
    under [LHS]eq_bind do rewrite 3!guard_and.
  transitivity (
    qperm b >>= (fun x =>
    guard (all (>= p) x) >> (guard (all (<= p) s) >>
    (guard (sorted x) >> ((guard (sorted s)) >> Ret (s ++ [:: p] ++ x)))) : M _)
).
    bind_ext => s'.
    rewrite -!bindA -!guard_and.
    by rewrite andbC (andbC _ (all (<= p) s)) (andbC (sorted s)) !andbA.
    rewrite -guard_qperm_eq.
    rewrite -[in RHS]bindA -guard_and andbC guard_and bindA.
    congr (_ >> _).
    rewrite boolp.funeqE => ?.
    rewrite -guard_qperm_neq.
    bind_ext; case.
    under [RHS]eq_bind do rewrite bindA.
    rewrite assertE bindA bindretf (@guardsC M (@bindmfail M)) bindA.
    bind_ext => ?.
    by rewrite assertE !bindA 2!bindretf assertE.
  Qed.

  Lemma is_partition_consL p x (ys zs : seq T) :
    is_partition p (x :: ys, zs) = (x <= p) && is_partition p (ys, zs).
  Proof. by rewrite /is_partition /= andbA. Qed.

  Lemma is_partition_consR p x (ys zs : seq T) :
    is_partition p (ys, x :: zs) = (x >= p) && is_partition p (ys, zs).
  Proof. by rewrite /is_partition /= andbCA. Qed.

  Definition is_partition_consE := (is_partition_consL, is_partition_consR).                            

  Fixpoint partition p (s : seq T) : seq T * seq T :=
    if s isn't x :: xs then ([::], [::]) else
    let: yz := partition p xs in
    if x <= p then (x :: yz.1, yz.2) else (yz.1, x :: yz.2).

  Lemma size_partition p (s : seq T) :
    size (partition p s).1 + size (partition p s).2 = size s.
  Proof.
    elim: s p => //= x xs ih p; have {ih} := ih p.
    move H : (partition p xs) => h; case: h H => a b ab /= abxs.
    by case: ifPn => xp /=; rewrite ?(addSn,addnS) abxs.
  Qed.

  Lemma refin_guard_le (x y : T) : total (<=%O : rel T) -> guard (x <= y) `>=` (guard (~~ (y <= x)) : M _).
  Proof.
    case: guardPn => [nyx|_ _].
    rewrite /total => /(_ x y).
    rewrite (negbTE nyx) orbF => ->; rewrite guardT; exact:refin_refl.
    by rewrite /refin altfailm.
  Qed.

  Tactic Notation "rInf" tactic(tac) :=
  (With (tac; reflexivity) Open (X in @bind _ _ _ _ X `>=` _ )) ||
  (With (tac; reflexivity) Open (X in _ `>=` @bind _ _ _ _ X)).

  Tactic Notation "rrewrite_" constr(lem) :=
    (With (rewrite lem; reflexivity) Open (X in @bind _ _ _ _ X `>=` _ )) ||
    (With (rewrite lem; reflexivity) Open (X in _ `>=` @bind _ _ _ _ X)).

  Lemma refin_nondet A (m1 m1' m2 m2' : M A) : 
    m1 `<=` m1' -> m2 `<=` m2' -> m1 [~] m2 `<=` m1' [~] m2'.
  Proof.
    move=> h1 h2.
    by rewrite /refin altACA h1 h2.
  Qed.

  Lemma mybind_ext (A B : UU0) (m : M A) (f1 f2 : A -> M B) :
  (forall a, f1 a = f2 a) ->
  (m >>= f1) = (m >>= f2).
  Proof.
  move=> f12.
  congr (@bind _ _).
  by rewrite boolp.funeqE.
  Qed.

  Lemma bind_ifr A B {b : bool} {m : M A} {f g : A -> M B} : 
    m >>= (fun x => if b then f x else g x)
    = (if b then (m >>= (fun x => f x))
            else (m >>= (fun x => g x))).
  Proof.
    case: ifPn => //.
  Qed.
  
  Lemma refin_partition(p : T) (xs : seq T) :
    total (<=%O : rel T) ->
    (Ret (partition p xs) : M (seq T * seq T)%type (*TODO: :> notation for `<=`?*))
    `<=`
    splits xs >>= assert (is_partition p).
  Proof.
    move => t.
    elim: xs p => [p /=|x xs ih p].
    by rewrite /is_partition bindretf /refin /= !assertE !all_nil /= guardT bindskipf altmm.
    rewrite /=.
    rewrite bindA.
    under mybind_ext do rewrite alt_bindDl 2!bindretf 2!assertE.
    under mybind_ext do rewrite 2!is_partition_consE 2!guard_and 2!bindA.
    apply: (@refin_trans _ _ _); last first.
    apply: bind_monotonic_lrefin => x0.
    apply: refin_nondet.
    apply: refin_refl.
    apply: bind_monotonic_refin.
    apply: refin_guard_le.
    assumption.
    apply: (@refin_trans _ _ _); last first.
    apply: bind_monotonic_lrefin => x1.
    apply: guard_neg.
    under mybind_ext do rewrite -bind_ifr.
    apply: (@refin_trans _ _ (
      (do a <- splits xs;
      guard (is_partition p a) >> (Ret a >>= (fun a =>
      (if x <= p then Ret (x :: a.1, a.2) else Ret (a.1, x :: a.2)))))%Do
    )); last first.
    rewrite /refin -alt_bindDr.
    bind_ext => -[? ?] /=.
    by rewrite bindretf /= (altmm (_ : M _)).
    under mybind_ext do rewrite -bindA -assertE.
    rewrite -bindA.
    apply: (@refin_trans _ _ _); last first.
    apply: bind_monotonic_refin.
    apply: ih.
    rewrite bindretf.
    case: ifPn => xp; exact: refin_refl.
  Qed.

  Lemma refin_slowsort (p : T) (xs : seq T) :
    (total (<=%O : rel T)) ->
    slowsort (p :: xs) `>=`
    Ret (partition p xs) >>= (fun '(ys, zs) =>
      slowsort ys >>= (fun ys' => slowsort zs >>= (fun zs' => Ret (ys' ++ [:: p] ++ zs'))) : M _).
  Proof.
    move => hyp.
    rewrite [X in X `>=` _]refin_slowsort_inductive_case.
    rewrite [X in X `>=` _](_ : _ = splits xs >>=
      (fun yz => guard (is_partition p yz) >> Ret yz) >>=
      fun '(ys, zs) => (qperm ys >>= assert sorted) >>=
      (fun ys' => (qperm zs >>= assert sorted) >>= (fun zs'=> Ret (ys' ++ [:: p] ++ zs')))); last first.
    rewrite bindA; bind_ext => -[s1 s2];rewrite !bindA; congr (_ >> _).
    by rewrite boolp.funeqE => -[]; rewrite bindretf bindA.
  (* apply: bind_monotonic_refin. (* TODO *)
  have := refin_partition p xs.
  by rewrite /assert; unlock.
  Qed. *)
  Admitted.

End slowsort.

Arguments slowsort {M} {_} {_}.

Section qsort.
  Variable M : plusMonad.
  Variables (d : unit) (T : porderType d).

  Program Fixpoint qsort' (s : seq T)
      (f : forall s', (size s' < size s)%N -> seq T) : seq T :=
    if s isn't p :: xs then [::] else
    let: (ys, zs) := partition p xs in
    f ys _ ++ [:: p] ++ f zs _.
  Next Obligation.
  have := size_partition p xs.
  by rewrite -Heq_anonymous /= => <-; rewrite ltnS leq_addr.
  Qed.
  Next Obligation.
  have := size_partition p xs.
  by rewrite -Heq_anonymous /= => <-; rewrite ltnS leq_addl.
  Qed.

  Definition qsort : seq T -> seq T :=
    Fix (@well_founded_size _) (fun _ => _) qsort'.

  Lemma qsort'_Fix (x : seq T)
    (f g : forall y : seq T, (size y < size x)%N -> seq T) :
    (forall (y : seq T) (p : (size y < size x)%N), f y p = g y p) ->
    qsort' f = qsort' g.
  Proof.
  by move=> ?; congr qsort'; apply fun_ext_dep => ?; rewrite boolp.funeqE.
  Qed.

  Lemma qsort_nil : qsort [::] = [::].
  Proof. by rewrite /qsort Fix_eq //; exact: qsort'_Fix. Qed.

  Lemma qsort_cons p (xs : seq T) :
    qsort (p :: xs) = let: (ys, zs) := partition p xs in
                      qsort ys ++ [:: p] ++ qsort zs.
  Proof.
  rewrite [in LHS]/qsort Fix_eq /=; last exact: qsort'_Fix.
  by move s12 : (partition p xs) => h; case: h s12.
  Qed.

  Definition qsortE := (qsort_nil, qsort_cons).

  Lemma quicksort_on_lists : total (<=%O : rel T) -> Ret \o qsort `<.=` (slowsort : _ -> M _).
  Proof.
    move=> hyp s.
    have [n sn] := ubnP (size s); elim: n => // n ih in s sn *.
    case: s => [|h t] in sn *.
      rewrite /= qsort_nil slowsort_nil. exact: refin_refl.
    rewrite /= qsort_cons.
    move pht : (partition h t) => ht.
    case: ht => ys zs in pht *.
    apply: (refin_trans _ (refin_slowsort M h t hyp)).
    rewrite bindretf pht.
    rewrite -(ih ys).
    rewrite -(ih zs).
    repeat rewrite alt_bindDl bindretf.
    by rewrite /refin !altA altmm.
    move: sn; rewrite ltnS /=.
    have := (size_partition h t); rewrite pht /= => <-.
    have: (size zs <= size ys + size zs)%N. by rewrite leq_addl.
    apply: leq_ltn_trans.
    move: sn; rewrite ltnS /=.
    have := (size_partition h t); rewrite pht /= => <-.
    have: (size ys <= size ys + size zs)%N. by rewrite leq_addr.
    apply: leq_ltn_trans.
  Qed.

  (* TODO: Ret \o qsort `<.=` slowsort by induction on the length of the input list *)

End qsort.

Goal qsort [:: 3; 42; 230; 1; 67; 2]%N = [:: 1; 2; 3; 42; 67; 230]%N.
by repeat rewrite qsortE /=. Abort.

Goal let s := [:: 3; 42; 230; 1; 67; 2]%N in qsort s = sort ltn s.
move=> s; rewrite /s sortE /=.
by repeat rewrite qsortE /=.
Abort.

Definition size_preserving (M : monad) (A : UU0) (f : seq A -> M (seq A)) :=
  forall xs, f xs >>= (fun ys => Ret (ys, size ys)) = f xs >>= (fun ys => Ret (ys, size xs)).

Lemma size_preserving_qperm (M : plusMonad) (A : UU0) :
  size_preserving (@qperm M A).
Proof.
move=> s; move sn : (size s) => n.
elim/ltn_ind: n s sn => n ih [/= <-{ih n}| h t].
  by rewrite qperm_nil 2!bindretf.
case: n ih => // n ih [tn].
rewrite qperm_consE /liftM2 !bindA.
rewrite splitsE /=.
Admitted.
(* 
Definition preserves A B (M : monad) (f : A -> M A) (g : A -> B):= 
  forall xs, (f xs >>= fun x' => Ret (x' , g x')) = (f xs >>= fun x' => Ret (x' , g xs)).

Section qsort.
  Variable M : plusMonad.
  Variables (d : unit) (T : porderType d).

  Lemma guard_qperm_eq' B (p : pred T) (a : seq T) (f : seq T -> M B) :
    guard (all p a) >>= (fun _ => qperm a >>= f) =
    qperm a >>= (fun x => guard (all p x) >> f x).
  Proof.
    move: p.
    have [n leMn] := ubnP (size a); elim: n => // n ih in a f leMn *.
    move: a leMn.
    case.
    by move=> _ p; rewrite /= qperm_nil 2!bindretf /=.
    move => h t.
    rewrite ltnS => tn p.
    rewrite qperm_consE {1}/liftM2. !bindA /= guard_and [in LHS]bindA.
    rewrite -bindA -guard_and.
    rewrite guard_splits_cons /liftM2.
    rewrite splitsE /= fmapE !bindA /=.
    bind_ext => -[a b] /=.
    rewrite 2!bindretf /=.
    (* transitivity (
      ((guard (all p b) >> guard (p h)) >> guard (all p a) >>
      (do x <- do x1 <- qperm a; do x2 <- qperm b; Ret (x1 ++ h :: x2); f x)%Do)
      ). *)
    rewrite -2!guard_and andbC andbA andbC andbA 2!guard_and !bindA.
    rewrite ih; last by rewrite (leq_trans _ tn) //= ltnS size_bseq.
    (* transitivity (
      (do x0 <- qperm a; ((guard (p h) >> guard (all p x0)) >> guard (all p b))
      >> (do x1 <- do x2 <- qperm b; Ret (x0 ++ h :: x2); f x1)%Do)%Do
    ). *)
    rewrite -bindA -guard_and commute_guard_n.
    bind_ext => ?.
    rewrite -bindA -guard_and andbC andbA andbC andbA 2!guard_and !bindA.
    rewrite ih; last by rewrite (leq_trans _ tn) //= ltnS size_bseq.
    (* transitivity (
      (do x2 <- qperm b; ((guard (p h) >> guard (all p x0)) >> guard (all p x2)) >>
      (do x3 <- Ret (x0 ++ h :: x2); f x3)%Do)%Do
    ). *)
    rewrite -bindA -guard_and commute_guard_n.
    bind_ext => ?.
    by rewrite -bindA -!guard_and 2!bindretf -all_rcons -cat_rcons all_cat.
  Qed.

  Lemma qperm_preserves_guard_all (p : pred T):
    preserves (@qperm M T) (fun x => @guard M (all p x)).
  Proof.
    rewrite /preserves => xs.
    move: p.
    have [n leMn] := ubnP (size xs); elim: n => // n ih in xs leMn *.
    move: xs leMn.
    case.
    by move=> _ p; rewrite /= qperm_nil 2!bindretf /=.
    move => h t.
    rewrite ltnS => tn p.
    rewrite qperm_consE {1}/liftM2 !bindA /= guard_and.
    rewrite -guard_and.
    rewrite /liftM2.
    rewrite splitsE /= fmapE !bindA /=.
    bind_ext => -[a b] /=.
    rewrite 2!bindretf /= !bindA.
    bind_ext => x.
    rewrite !bindA.
    rewrite_ bindretf.
    rewrite_ bindretf.
    bind_ext => y.
    (* transitivity (
      ((guard (all p b) >> guard (p h)) >> guard (all p a) >>
      (do x <- do x1 <- qperm a; do x2 <- qperm b; Ret (x1 ++ h :: x2); f x)%Do)
      ). *)
    rewrite -2!guard_and andbC andbA andbC andbA 2!guard_and !bindA.
    rewrite ih; last by rewrite (leq_trans _ tn) //= ltnS size_bseq.
    (* transitivity (
      (do x0 <- qperm a; ((guard (p h) >> guard (all p x0)) >> guard (all p b))
      >> (do x1 <- do x2 <- qperm b; Ret (x0 ++ h :: x2); f x1)%Do)%Do
    ). *)
    rewrite -bindA -guard_and commute_guard_n.
    bind_ext => ?.
    rewrite -bindA -guard_and andbC andbA andbC andbA 2!guard_and !bindA.
    rewrite ih; last by rewrite (leq_trans _ tn) //= ltnS size_bseq.
    (* transitivity (
      (do x2 <- qperm b; ((guard (p h) >> guard (all p x0)) >> guard (all p x2)) >>
      (do x3 <- Ret (x0 ++ h :: x2); f x3)%Do)%Do
    ). *)
    rewrite -bindA -guard_and commute_guard_n.
    bind_ext => ?.
    by rewrite -bindA -!guard_and 2!bindretf -all_rcons -cat_rcons all_cat.
    rewrite /preserves. *)
