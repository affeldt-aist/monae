Require Import ZArith ssreflect ssrmatching ssrfun ssrbool.
From mathcomp Require Import eqtype ssrnat seq choice fintype tuple.
From mathcomp Require Import boolp.
From infotheo Require Import ssrZ.
Require Import monad state_monad.

(* from gibbons2011icfp and mu2017 *)

Definition place n {B} (rs : seq B) := zip (map Z_of_nat (iota 0 n)) rs.

Definition empty {B} : (seq B * seq B):= ([::] , [::]).

Section nqueens.

(* input: queen position, already threatened up/down diagonals
   output: safe or not, update up/down diagonals *)
Definition test : Z`2 -> (seq Z)`2 -> bool * (seq Z)`2 :=
  fun '(c, r) '(upds, downs) =>
    let (u, d) := (r - c, r + c)%Z in
    ((u \notin upds) && (d \notin downs), (u :: upds, d :: downs)).

Section purely_functional.

Definition start1 : (seq Z)`2 -> bool * (seq Z)`2 :=
  fun updowns => (true, updowns).

Definition step1 : Z`2 -> (bool * (seq Z)`2) -> bool * (seq Z)`2 :=
  fun cr '(restOK, updowns) =>
    let (thisOK, updowns') := test cr updowns in
    (thisOK && restOK, updowns').

(* over the list of column-row pairs
   bool * (seq Z)`2: queens to the right safe or not,
                       up/down diagonals under threat from the queens so far *)
Definition safe1 : (seq Z)`2 -> seq Z`2 -> bool * (seq Z)`2 :=
  foldr step1 \o start1.

Definition queens {M : nondetMonad} n : M (seq Z) :=
  do rs <- perms (map Z_of_nat (iota 0 n)) ;
     (guard (safe1 empty (place n rs)).1 >> Ret rs).

End purely_functional.

Section statefully.
(* statefully constructing the sets of up/down diagonals threatened by the queens so far *)

Variable M : stateMonad (seq Z)`2.

Definition start2 : M bool := Ret true.

Definition step2 (cr : Z`2) (k : M bool) : M bool :=
  do b' <- k ;
  do uds <- Get;
  let (b, uds') := test cr uds in
  Put uds' >> Ret (b && b').

Definition safe2 : seq Z`2 -> M bool :=
  foldr step2 start2.

Lemma safe2E crs :
  safe2 crs = do uds <- Get; let (ok, uds') := safe1 uds crs in
                             (Put uds' >> Ret ok).
Proof.
(* TODO(rei): how to write this proof w.o. the "set" and "transitivity"'s? *)
apply/esym; rewrite /safe2.
set f := fun x => do uds <- Get; let (ok, uds') := safe1 uds x in Put uds' >> Ret ok : M _.
rewrite -(@foldr_universal_ext _ _ _ _ f) //;
  [apply/esym|move=> cr {crs}crs; apply/esym].
  by rewrite /start2 /f /= -bindA getputskip bindskipf.
(* definition of safe1 *)
transitivity
  (do uds <- Get;
  let (ok, uds') := step1 cr (safe1  uds crs) in Put uds'>> Ret ok : M _); last first.
  by [].
(* introduce a let *)
transitivity
  (do uds <- Get;
  let (b', uds'') := safe1 uds crs in
  let (ok, uds') := step1 cr (b', uds'') in Put uds' >> Ret ok : M _); last first.
  bind_ext => x.
  by case: safe1.
(* definition of step1 *)
transitivity
  (do uds <- Get;
  let (b', uds'') := safe1 uds crs in
  let (b, uds''') := test cr uds'' in
  let (ok, uds') := (b && b', uds''') in Put uds' >> Ret ok : M _); last first.
  bind_ext => x.
  case: safe1 => // h t.
  rewrite /step1 /=.
  by case: test.
transitivity
  (do uds <- Get;
  let (b', uds'') := safe1 uds crs in
  let (b, uds''') := test cr uds'' in
  let (ok, uds') := (b && b', uds''') in (Put uds'' >> Put uds' >> Ret ok) : M _); last first.
  bind_ext => x.
  case: safe1 => // h t.
  case: test => // a b.
  by rewrite putput.
(* move two of the lets *)
transitivity
  (do uds <- Get;
  let (b', uds'') := safe1 uds crs in
  Put uds'' >>
  let (b, uds''') := test cr uds'' in
  let (ok, uds') := (b && b', uds''') in Put uds' >> Ret ok : M _); last first.
  bind_ext => x.
  case: safe1 => // h t.
  case: test => // a b.
  by rewrite bindA.
transitivity
  (do uds <- Get;
  let (b', uds'') := safe1 uds crs in
  Put uds'' >>
  do uds'''' <- Get ;
  let (b, uds''') := test cr uds'''' in
  let (ok, uds') := (b && b', uds''') in Put uds' >> Ret ok : M _); last first.
  bind_ext => x.
  case: safe1 => // h t.
  by rewrite -bindA putgetput.
transitivity
  (do
   b' <- (do uds <- Get ; let (ok, uds'') := safe1 uds crs in Put uds'' >> Ret ok) ;
   (do uds'''' <- Get;
   let (b, uds''') := test cr uds'''' in
   let (ok, uds') := (b && b', uds''') in Put uds' >> Ret ok) : M _); last first.
  rewrite bindA; bind_ext => x.
  case: safe1 => // h t.
  by rewrite bindA; rewrite_ bindretf.
by [].
Qed.

End statefully.

End nqueens.
Arguments step2 {M}.
Arguments safe2 {M}.
Arguments start2 {M}.

Section safe_reification.

Variable M : stateRunMonad (seq Z)`2.

Lemma run_safe2 crs updowns : Run (safe2 crs : M _) updowns = safe1 updowns crs.
Proof.
rewrite safe2E runbind runget; case: safe1 => a b.
by rewrite runbind runput runret.
Qed.

End safe_reification.

Section queens_statefully_nondeterministically.

Variable M : nondetStateMonad (seq Z)`2.

Definition queens_state_nondeter n : M (seq Z) :=
  do s <- Get ;
    do rs <- perms (map Z_of_nat (iota 0 n));
      Put empty >>
        (do ok <- safe2 (place n rs) ;
             (Put s >> guard ok)) >> Ret rs.

Lemma queensE n : queens n = queens_state_nondeter n.
Proof.
rewrite (getput_prepend (queens n)) /queens_state_nondeter; bind_ext => x.
rewrite {1}/queens putpermsC; bind_ext => y.
rewrite safe2E.
set f := (do ok <- (do _ <- _; _); _ >> guard ok in RHS).
rewrite (_ : f =
  do uds <- Get; Put (safe1 uds (place n y)).2 >> Ret (safe1 uds (place n y)).1 >>
      Put x >> guard (safe1 uds (place n y)).1); last first.
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
Arguments queens_state_nondeter {M}.

Section queens_exploratively.

Variable M : nondetStateMonad (seq Z)`2.

Definition queens_explor n : M _ :=
  do s <- Get;
    do rs <- perms (map Z_of_nat (iota 0 n));
      Put empty >>
        (do ok <- safe2 (place n rs) ;
             (guard ok >> Put s)) >> Ret rs.

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
  do s <- Get;
    (do rs <- perms (map Z_of_nat (iota 0 n)) ;
      Put empty >> safe3 (place n rs) >> Put s >> Ret rs).

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
  do uds <- Get ; let (b, uds') := test cr uds in Put uds' >> guard b.

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
transitivity ((do b' <- k ;
               do uds <- Get ;
               let (b, uds') := test cr uds in
               Put uds' >> Ret (b && b')) >>= guard).
  by rewrite /step2.
transitivity (do b' <- k ;
              do uds <- Get ;
              let (b, uds') := test cr uds in
              Put uds' >> guard (b && b')).
  (* by "do-notation" *)
  rewrite bindA; bind_ext => x.
  rewrite bindA; bind_ext => y.
  case: (test cr y) => a b.
  by rewrite bindA bindretf.
transitivity (do b' <- k ;
              do uds <- Get ;
              let (b, uds') := test cr uds in
              Put uds' >> guard b >> guard b').
  bind_ext => x.
  bind_ext => y.
  case: (test cr y) => a b.
  by rewrite bindA guard_and.
transitivity (do b' <- k ;
              guard b' >> (do uds <- Get ;
                           let (b, uds') := test cr uds in
                           Put uds' >> guard b)).
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
               do uds <- Get ;
                 let (b, uds') := test cr uds in
                 Put uds' >> guard b).
  by rewrite bindA.
by [].
Qed.

End queens_exploratively.

Section mu2017.

Section queens_definition.

Local Open Scope mu_scope.

Definition ups s i := zipWith Zplus (map Z_of_nat (iota i (size s))) s.
Definition downs s i := zipWith Zminus (map Z_of_nat (iota i (size s))) s.
Definition safe s := uniq (ups s 0) && uniq (downs s 0).

Definition queens_example := [:: 3; 5; 7; 1; 6; 0; 2; 4]%Z.
Eval compute in safe queens_example.

Definition mu_queens {M : nondetMonad} n : M (seq Z) :=
  perms (map Z_of_nat (iota 0 n)) >>= assert safe.

Definition safeAcc i (us ds : seq Z) (xs : seq Z) :=
  let us' := ups xs i in let ds' := downs xs i in
  uniq us' && uniq ds' && all (fun x => x \notin us) us' && all (fun x => x \notin ds) ds'.

Lemma safeE : safe =1 safeAcc 0 [::] [::].
Proof.
move=> s; rewrite /safe /safeAcc.
by rewrite (sub_all _ (@all_predT _ _)) // (sub_all _ (@all_predT _ _)) // !andbT.
Qed.

Definition queens_ok (i_xus_yds : Z * seq Z * seq Z) :=
  let: (_, xus, yds) := i_xus_yds in
  match xus, yds with
  | x :: us, y :: ds => (x \notin us) && (y \notin ds)
  | _, _ => false
  end.

Definition queens_next i_us_ds x :=
  let: (i, us, ds) := i_us_ds in (i + 1, (i + x) :: us, (i - x) :: ds)%Z.

Definition safeAcc_scanl i (us ds : seq Z) :=
  let ok i_xus_yds := queens_ok i_xus_yds in
  let op i_us_ds x := queens_next i_us_ds x in
  all ok \o scanl op (i, us, ds).

Lemma safeAccE i a b : safeAcc i a b =1 safeAcc_scanl (Z_of_nat i) a b.
Proof.
move=> s; elim: s i a b => // h t IH i a b.
rewrite /safeAcc_scanl /=.
move: (IH i.+1 ((Z.of_nat i + h) :: a) ((Z.of_nat i - h) :: b))%Z.
rewrite (_ : Z.of_nat i.+1 = (Z.of_nat i) + 1)%Z; last by rewrite -addn1 Nat2Z.inj_add.
rewrite /safeAcc_scanl => /= <-.
rewrite /safeAcc /= !andbA /zipWith /=.
set A := uniq _. set B := uniq _. set sa := map _ _. set sb := map _ _.
rewrite -![in LHS]andbA [in LHS]andbC.
do 2 rewrite -![in RHS]andbA [in RHS]andbC.
rewrite -!andbA; congr andb.
rewrite -[in LHS]andbC -!andbA; congr andb.
do 2 rewrite ![in RHS]andbA [in RHS]andbC.
congr andb.
rewrite [in LHS]andbCA -![in RHS]andbA; congr andb.
have H : forall (op : Z -> Z -> Z) y s, all (fun x : Z => x \notin op (Z_of_nat i) h :: y) s =
  all (fun x : Z => x \notin y) s && (op (Z_of_nat i) h \notin s).
  move=> op y; elim => //= s1 s2 ih /=; rewrite ih !inE !negb_or.
  rewrite -andbA andbCA !andbA; congr (_ && _); rewrite -!andbA; congr(_ && _).
  by rewrite andbC eq_sym.
by rewrite andbA andbCA -!andbA andbCA !andbA -H -andbA -H.
Qed.

Lemma mu_queensE {M : nondetMonad} n : mu_queens n =
  perms (map Z_of_nat (iota 0 n)) >>= assert (safeAcc_scanl 0 [::] [::]) :> M _.
Proof.
rewrite /mu_queens; bind_ext => s; by rewrite /assert (safeE s) safeAccE.
Qed.

End queens_definition.

Section section_52.

Variable M : nondetStateMonad (Z * seq Z * seq Z).

Definition opdot_queens : Z -> M (seq Z) -> M (seq Z) := opdot queens_next queens_ok.

Local Open Scope mu_scope.

Definition queensBody (xs : seq Z) : M (seq Z) :=
  perms xs >>= foldr opdot_queens (Ret [::]).

Lemma mu_queens_state_nondeter n : mu_queens n = Get >>=
  (fun ini => Put (0, [::], [::])%Z >> queensBody (map Z_of_nat (iota 0 n)) >>= overwrite ini).
Proof.
rewrite mu_queensE.
transitivity (perms (map Z.of_nat (iota 0 n)) >>= (fun xs => Get >>=
  (fun ini => Put (0, [::], [::])%Z >> foldr opdot_queens (Ret [::]) xs >>= overwrite ini))).
  bind_ext => s /=.
  rewrite assert_all_scanl. (* NB: uses theorem 4.1 *)
  bind_ext => st.
  rewrite 2!bindA.
  bind_ext; case.
  by rewrite -theorem_53 bindA.
transitivity (Get >>= (fun ini => Put (0, [::], [::])%Z >>
  perms (map Z.of_nat (iota 0 n)) >>= (fun xs => (foldr opdot_queens (Ret [::]) xs >>= overwrite ini)))).
  rewrite -getpermsC.
  bind_ext => s.
  rewrite !bindA putpermsC.
  by rewrite_ bindA.
bind_ext => st.
by rewrite !bindA.
Qed.

End section_52.

Definition seed_select {M : nondetStateMonad (Z * seq Z * seq Z)%type} :=
  fun (p : pred (seq Z)) (f : seq Z -> M (Z * seq Z)%type)
  (a b : seq Z) => size a < size b.

(* direct proof of theorem 4.2 *)
Section theorem_42.
Variables (M : nondetStateMonad (Z * seq Z * seq Z)%type).

Local Open Scope mu_scope.

Notation unfoldM := (unfoldM (@well_founded_size _)).

Let op := @opdot_queens M.
Let p := @nilp Z.

Lemma base_case y : p y -> (foldr op (Ret [::]) >=> unfoldM p select) y = Ret [::].
Proof.
move=> py.
transitivity (Ret [::] >>= foldr op (Ret [::])).
  rewrite /kleisli bindretf /= join_fmap unfoldME; last exact: decr_size_select.
  by rewrite py bindretf.
by rewrite bindretf.
Qed.

Lemma theorem_42 :
  (foldr op (Ret [::]) >=> unfoldM p select) =1
  @hyloM _ _ _ _ op [::] p select seed_select (@well_founded_size _).
Proof.
apply: (well_founded_induction (@well_founded_size _)) => y IH.
rewrite hyloME; last exact: decr_size_select.
case/boolP : (p y) => py.
  by rewrite base_case.
rewrite /kleisli /= join_fmap.
rewrite unfoldME; last exact: decr_size_select.
rewrite (negbTE py) bindA.
rewrite(@decr_size_select _ _) /bassert !bindA; bind_ext => -[b a] /=.
rewrite /assert /guard /=.
case: ifPn => ay; last by rewrite !bindfailf.
rewrite bindskipf !bindretf /= -IH // bind_fmap /kleisli /= join_fmap.
suff : do x <- unfoldM p select a; op b (foldr op (Ret [::]) x) =
  op b (do x <- unfoldM p select a; foldr op (Ret [::]) x) by done.
rewrite {ay}.
move: a b.
apply: (well_founded_induction (@well_founded_size _)) => a IH' b.
destruct a as [|u v] => //.
  rewrite unfoldME /=; last exact: decr_size_select.
  by rewrite !bindretf.
rewrite unfoldME; last exact: decr_size_select.
rewrite !bindA.
transitivity (do x <- Ret (u, v) [~] (do y_ys <- select v; Ret (y_ys.1, u :: y_ys.2));
  op b (do x0 <- fmap (cons x.1) (unfoldM p select x.2); foldr op (Ret [::]) x0)); last first.
  apply/esym.
  rewrite {1}/op /opdot_queens /opdot fmap_bind.
  transitivity (do st <- Get;
  (guard (queens_ok (queens_next st b)) >> do x <- Ret (u, v) [~] (do y_ys <- select v; Ret (y_ys.1, u :: y_ys.2));
   (Put (queens_next st b)) >>
  ((cons b
    (o) (fun x : Z * seq Z => do x0 <- fmap (cons x.1) (unfoldM p select x.2); foldr op (Ret [::]) x0)) x))).
    bind_ext => st.
    rewrite !bindA.
    bind_ext; case.
    rewrite -commute_nondetState //.
    case: (@select_is_nondetState _ M _ v) => x /= <-.
    by exists (ndAlt (ndRet (u, v)) (ndBind x (fun y => ndRet (y.1, u :: y.2)))).
  transitivity (do st <- Get;
  (do x <- Ret (u, v) [~] (do y_ys <- select v; Ret (y_ys.1, u :: y_ys.2)) : M _;
  guard (queens_ok (queens_next st b)) >>
   Put (queens_next st b) >>
   (cons b
    (o) (fun x0 : Z * seq Z => do x1 <- fmap (cons x0.1) (unfoldM p select x0.2); foldr op (Ret [::]) x1))
     x)).
    bind_ext => st.
    rewrite -bindA guardsC; last exact: bindmfail.
    rewrite !bindA.
    bind_ext => x.
    rewrite !bindA.
    bind_ext; case.
    by rewrite bindretf.
  rewrite -commute_nondetState; last first.
    case: (@select_is_nondetState _ M _ v) => x <-.
    by exists (ndAlt (ndRet (u, v)) (ndBind x (fun y => ndRet (y.1, u :: y.2)))).
  by rewrite fcomp_def.
bind_ext => x.
rewrite {1}/op /opdot_queens /opdot.
rewrite commute_nondetState; last first.
  rewrite fmapE.
  case: (unfoldM_is_nondetState (@select_is_nondetState _ M Z) (@decr_size_select M _) x.2).
  move=> m <-.
  by exists (ndBind m (fun y => ndRet (x.1 :: y))).
rewrite {2}/op /opdot_queens /opdot.
bind_ext => st.
rewrite commute_nondetState //; last first.
  rewrite fmapE.
  case: (unfoldM_is_nondetState (@select_is_nondetState _ M Z) (@decr_size_select _ _) x.2).
  move=> m <-.
  by exists (ndBind m (fun y => ndRet (x.1 :: y))).
bind_ext; case.
rewrite !bind_fmap !fmap_bind.
by rewrite_ fcomp_def.
Qed.

End theorem_42.

Section section_52_contd.

Variables (M : nondetStateMonad (Z * seq Z * seq Z)%type).

Local Open Scope mu_scope.

Lemma queensBodyE : queensBody M =
  hyloM (@opdot_queens M) [::] (@nilp _) select seed_select (@well_founded_size _).
Proof.
rewrite /queensBody funeqE => -[|h t].
- rewrite /= permsE /= hyloME ?bindretf //; exact: decr_size_select.
- by rewrite [h :: t]lock -theorem_42 /kleisli /= join_fmap perms_mu_perm.
Qed.

Lemma queensBodyE' xs : queensBody M xs = if xs is [::] then Ret [::] else
  select xs >>= (fun xys =>
  Get >>= (fun st => guard (queens_ok (queens_next st xys.1)) >>
  Put (queens_next st xys.1) >> (fmap (cons xys.1) (queensBody M xys.2)))).
Proof.
case: xs => [|h t].
  rewrite queensBodyE // hyloME //; exact: decr_size_select.
rewrite {1}queensBodyE hyloME; last exact: decr_size_select.
rewrite {-1}[h :: t]lock decr_size_select /bassert 2!bindA.
rewrite (_ : nilp _ = false) //.
bind_ext => -[x ys].
rewrite /assert /guard.
case: ifPn => ysht; last by rewrite !bindfailf.
rewrite bindskipf !bindretf /opdot_queens /opdot.
bind_ext => st.
rewrite !bindA; bind_ext; case.
bind_ext; case.
by rewrite queensBodyE.
Qed.

End section_52_contd.

End mu2017.

Arguments opdot_queens {M}.
