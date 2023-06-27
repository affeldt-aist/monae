From mathcomp Require Import all_ssreflect.
From mathcomp Require Import finmap.
From mathcomp Require boolp.
#[local] Remove Hints boolp.Prop_irrelevance : core.
Require Import monae_lib.
From HB Require Import structures.
Require Import hierarchy monad_lib fail_lib state_lib trace_lib.
Require Import monad_transformer monad_model.
Require Import JMeq.

(******************************************************************************)
(*                       Models for typed store                               *)
(*   (separate file as it requires disabling various sanity checks)           *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.

Module Type MLTYdef.
Parameter ml_type : eqType.
Variant loc : ml_type -> Type := mkloc T : nat -> loc T.
Parameter coq_type : forall M : Type -> Type, ml_type -> Type.
Parameter ml_undef : ml_type.
Parameter undef : forall M, coq_type M ml_undef.
End MLTYdef.

Module ModelTypedStore (MLtypes : MLTYdef).
Import MLtypes.
Module MLtypes'.
Include MLtypes.
Definition locT := [eqType of nat].
Definition loc_id {T} (l : loc T) := let: mkloc _ n := l in n.
End MLtypes'.
Module MTypedStore := MonadTypedStore (MLtypes').
Import MLtypes'.
Import MLtypes.
Import MTypedStore.

Record binding (M : Type -> Type) :=
  mkbind { bind_type : ml_type; bind_val : coq_type M bind_type }.
Arguments mkbind {M bind_type}.

Definition M0 Env (T : UU0) := MS Env option_monad T.

#[bypass_check(positivity)]
Inductive Env := mkEnv : seq (binding (M0 Env)) -> Env.
Definition ofEnv '(mkEnv e) := e.
Definition sizeEnv '(mkEnv e) := size e.

Definition acto : UU0 -> UU0 := MS Env option_monad.
Local Notation M := acto.
Local Notation coq_type := (coq_type M).

Definition def := mkbind (undef M).
Local Notation nth_error := List.nth_error.

Definition extend_env T (v : coq_type T) (e : Env) :=
  mkEnv (rcons (ofEnv e) (mkbind v)).
Definition fresh_loc (T : ml_type) (e : Env) := mkloc T (sizeEnv e).

Definition cnew T (v : coq_type T) : M (loc T) :=
  fun e => inr (fresh_loc T e, extend_env v e).

Definition coerce T1 T2 (v : coq_type T1) : option (coq_type T2) :=
  if eqVneq T1 T2 is EqNotNeq H then Some (eq_rect _ _ v _ H) else None.

Lemma coerce_sym (T T' : ml_type) (s : coq_type T) (s' : coq_type T') :
  coerce T' s -> coerce T s'.
Proof.
by rewrite /coerce; case: eqVneq => //= h; case: eqVneq => //; rewrite h eqxx.
Qed.

Lemma coerce_eq (T T' : ml_type) (s : coq_type T) : coerce T' s -> T = T'.
Proof. by rewrite /coerce; case: eqVneq. Qed.

Lemma coerce_Some (T : ml_type) (s : coq_type T) : coerce T s = Some s.
Proof.
by rewrite /coerce; case: eqVneq => /= [?|]; [rewrite -eq_rect_eq|rewrite eqxx].
Qed.

Definition cget T (r : loc T) : M (coq_type T) :=
  fun st =>
    if nth_error (ofEnv st) (loc_id r) is Some (mkbind T' v) then
      if coerce T v is Some u then inr (u, st) else inl tt
    else inl tt.

Definition cput T (r : loc T) (v : coq_type T) : M unit :=
  fun st =>
    let: mkEnv st := st in
    let n := loc_id r in
    if nth_error st n is Some (mkbind T' _) then
      if coerce T' v is Some u then
        let b := mkbind (u : coq_type T') in
        inr (tt, mkEnv (set_nth def st n b))
      else inl tt
    else inl tt.

Definition crun (A : UU0) (m : M A) : option A :=
  match m (mkEnv nil) with
  | inl _ => None
  | inr (a, _) => Some a
  end.

(* WIP *)
Lemma MS_bindE [S : UU0] [M : monad] [A B : UU0] (m : MS S M A) (f : A -> MS S M B) s :
  (m >>= f) s = m s >>= uncurry f.
Proof. by []. Qed.

Lemma bind_cnew T (s : coq_type T) A (k : loc T -> M A) e :
  (cnew s >>= k) e = k (fresh_loc T e) (extend_env s e).
Proof. by case: e. Qed.

Lemma Some_cget T (r : loc T) (s : coq_type T) e (A : UU0) (f : coq_type T -> M A) :
  nth_error (ofEnv e) (loc_id r) = Some (mkbind s) ->
  (cget r >>= f) e = f s e.
Proof. by move=> H; rewrite MS_bindE /cget H coerce_Some. Qed.
Arguments Some_cget {T r} s.

Lemma nocoerce_cget T (r : loc T) T' (s' : coq_type T') e :
  nth_error (ofEnv e) (loc_id r) = Some (mkbind s') ->
  ~ coerce T s' ->
  cget r e = fail.
Proof. by move=> H Ts'; rewrite /cget H; case: coerce Ts'. Qed.

Lemma None_cget T (r : loc T) e :
  nth_error (ofEnv e) (loc_id r) = None ->
  cget r e = fail.
Proof. by move=> H; rewrite /cget H. Qed.

(* Prove the laws *)
Lemma cnewget T (s : coq_type T) A (k : loc T -> coq_type T -> M A) :
  cnew s >>= (fun r => cget r >>= k r) = cnew s >>= (fun r => k r s).
Proof.
apply/boolp.funext => e.
rewrite bind_cnew (Some_cget s)//.
by destruct e as [e]; rewrite nth_error_rcons_size.
Qed.

Lemma nocoerce_cput T (r : loc T) (s : coq_type T) T' (s' : coq_type T') e :
  nth_error (ofEnv e) (loc_id r) = Some (mkbind s') ->
  ~ coerce T s' ->
  cput r s e = fail.
Proof.
move=> H Ts'; move: e H => [e] H; rewrite /cput H.
have {}Ts' : ~ coerce T' s by apply: contra_not Ts'; exact: coerce_sym.
by case: coerce Ts'.
Qed.

Lemma None_cput T (r : loc T) (s : coq_type T) e :
  nth_error (ofEnv e) (loc_id r) = None ->
  cput r s e = fail.
Proof. by move=> H; move: e H => [e] H; rewrite /cput H. Qed.

Lemma cnewput T (s t : coq_type T) A (k : loc T -> M A) :
  cnew s >>= (fun r => cput r t >> k r) = cnew t >>= k.
Proof.
apply/boolp.funext => -[st].
rewrite bind_cnew 2!MS_bindE /= nth_error_rcons_size coerce_Some.
by rewrite set_nth_rcons.
Qed.

(*
Definition permutable T1 T2 (A : UU0) (k : loc T1 -> loc T2 -> M A) :=
  forall (n1 n2 : nat) (b1 b2 : binding M) (st : seq (binding M)),
    k (mkloc T1 n1) (mkloc T2 n2)
      (mkEnv (set_nth def (set_nth def st n1 b1) n2 b2)) =
    k (mkloc T1 n2) (mkloc T2 n1)
      (mkEnv (set_nth def (set_nth def st n2 b1) n1 b2)).

Lemma cnewC T1 T2 (s : coq_type T1) (t : coq_type T2)
          A (k : loc T1 -> loc T2 -> M A) :
  permutable k ->
  cnew s >>= (fun r => cnew t >>= k r) =
  cnew t >>= (fun r => cnew s >>= k^~ r).
Proof.
move=> pmk.
apply/boolp.funext => -[st].
rewrite !bind_cnew /fresh_loc /extend_env /= size_rcons.
Abort.
*)

Variant nth_error_spec (T : ml_type) (e : Env) (r : loc T) : Type :=
  | NthError : forall s : coq_type T,
    nth_error (ofEnv e) (loc_id r) = Some (mkbind s) -> nth_error_spec e r
  | NthError_nocoerce : forall T' (s' : coq_type T'),
    nth_error (ofEnv e) (loc_id r) = Some (mkbind s') -> ~ coerce T s' ->
    nth_error_spec e r
  | NthError_None : nth_error (ofEnv e) (loc_id r) = None -> nth_error_spec e r.

Lemma ntherrorP (T : ml_type) (e : Env) (r : loc T) : nth_error_spec e r.
Proof.
case H : (nth_error (ofEnv e) (loc_id r)) => [[T' s']|].
  have [Ts'|Ts'] := boolp.pselect (coerce T s').
    have ? := coerce_eq Ts'; subst T'.
    exact: NthError H.
  exact: NthError_nocoerce H Ts'.
exact: NthError_None.
Qed.

Lemma cgetput T (r : loc T) (s : coq_type T) : cget r >> cput r s = cput r s.
Proof.
apply/boolp.funext => e.
have [s' H|T' s' H Ts'|H] := ntherrorP e r.
- by rewrite (Some_cget s').
- by rewrite MS_bindE (nocoerce_cget H)// (nocoerce_cput _ H).
- by rewrite MS_bindE None_cget// None_cput.
Qed.

Lemma Some_cput T (r : loc T) (s : coq_type T) e :
  nth_error (ofEnv e) (loc_id r) = Some (mkbind s) ->
  cput r s e = (@skip M) e.
Proof.
move=> H.
destruct e as [e].
rewrite /cput/= H coerce_Some/=.
by rewrite nth_error_set_nth_id.
Qed.

Lemma Some_cputget T (s' s : coq_type T) (r : loc T) A (k : coq_type T -> M A)
  (e : Env) :
  nth_error (ofEnv e) (loc_id r) = Some (mkbind s') ->
  (cput r s >> (cget r >>= k)) e = (cput r s >> k s) e.
Proof.
move=> H.
destruct e as [e].
rewrite {1}/cput/= !MS_bindE H.
rewrite coerce_Some.
rewrite bindE/=.
rewrite (Some_cget s); last first.
  by rewrite /= nth_error_set_nth.
by rewrite H coerce_Some.
Qed.
Arguments Some_cputget {T} s'.

Lemma cgetputskip T (r : loc T) : cget r >>= cput r = cget r >> skip.
Proof.
apply/boolp.funext => e /=.
have [s' H|T' s' H Ts'|H] := ntherrorP e r.
- by rewrite (Some_cget s')// (Some_cget s')// (Some_cput H).
- by rewrite !MS_bindE (nocoerce_cget H).
- by rewrite !MS_bindE None_cget.
Qed.

Lemma cgetget T (r : loc T) (A : UU0) (k : coq_type T -> coq_type T -> M A) :
  cget r >>= (fun s => cget r >>= k s) = cget r >>= fun s => k s s.
Proof.
apply/boolp.funext => e /=.
have [s' H|T' s' H Ts'|H] := ntherrorP e r.
- by do 3 rewrite (Some_cget s')//.
- by rewrite !MS_bindE (nocoerce_cget H).
- by rewrite !MS_bindE None_cget.
Qed.

Lemma cputget T (r: loc T) (s: coq_type T) (A: UU0) (k: coq_type T -> M A) :
  cput r s >> (cget r >>= k) = cput r s >> k s.
Proof.
apply/boolp.funext => e /=.
have [s' H|T' s' H Ts'|H] := ntherrorP e r.
- by rewrite (Some_cputget s').
- by rewrite !MS_bindE (nocoerce_cput _ H).
- by rewrite 2!MS_bindE None_cput.
Qed.

Lemma Some_cputput (T : ml_type) (r : loc T) (s s' : coq_type T)
  (e : Env) (s'' : coq_type T) :
  nth_error (ofEnv e) (loc_id r) = Some (mkbind s'') ->
  (cput r s >> cput r s') e = cput r s' e.
Proof.
move=> H.
destruct e as [e].
rewrite MS_bindE/=.
rewrite H !coerce_Some.
rewrite bindE/=.
rewrite nth_error_set_nth coerce_Some/=.
by rewrite set_set_nth eqxx.
Qed.

Lemma cputput T (r : loc T) (s s' : coq_type T) :
  cput r s >> cput r s' = cput r s'.
Proof.
apply/boolp.funext => e.
have [s'' H|T'' s'' H Ts''|H] := ntherrorP e r.
- by rewrite (Some_cputput _ _ H).
- by rewrite !MS_bindE (nocoerce_cput _ H)// (nocoerce_cput _ H).
- by rewrite MS_bindE !None_cput.
Qed.

Lemma cgetC T1 T2 (r1 : loc T1) (r2 : loc T2) (A : UU0)
           (k : coq_type T1 -> coq_type T2 -> M A) :
  cget r1 >>= (fun u => cget r2 >>= (fun v => k u v)) =
  cget r2 >>= (fun v => cget r1 >>= (fun u => k u v)).
Proof.
apply/boolp.funext => e /=.
have [u Hr1|u T1' Hr1 T1u|Hr1] := ntherrorP e r1.
- rewrite (Some_cget u)//.
  have [v Hr2|v T2' Hr2 T2v|Hr2] := ntherrorP e r2.
  + by rewrite (Some_cget v)// (Some_cget v)// (Some_cget u).
  + by rewrite 2!MS_bindE (nocoerce_cget Hr2)// bindfailf.
  + by rewrite !MS_bindE None_cget.
- rewrite MS_bindE (nocoerce_cget Hr1)// bindfailf.
  have [v Hr2|v T2' Hr2 T2v|Hr2] := ntherrorP e r2.
  + by rewrite (Some_cget v)// MS_bindE (nocoerce_cget Hr1).
  + by rewrite MS_bindE (nocoerce_cget Hr2).
  + by rewrite MS_bindE None_cget.
- rewrite MS_bindE None_cget// bindfailf.
  have [v Hr2|v T2' Hr2 T2v|Hr2] := ntherrorP e r2.
  + by rewrite (Some_cget v)// MS_bindE None_cget.
  + by rewrite MS_bindE (nocoerce_cget Hr2).
  + by rewrite MS_bindE !None_cget.
Qed.

(* NB: this is similar to the cnewget law *)
Lemma cnewgetD_helper e T T' r v (s : coq_type T') A (k : loc T' -> coq_type T -> M A) :
  nth_error (ofEnv e) (loc_id r) = Some (mkbind v) ->
  (cnew s >>= (fun r' => cget r >>= k r')) e = (cnew s >>= (fun r => k r v)) e.
Proof.
move=> H.
rewrite bind_cnew//.
by rewrite (Some_cget v) // (nth_error_rcons_some _ H).
Qed.

Lemma cgetnewD T T' (r : loc T) (s : coq_type T') A
           (k : loc T' -> coq_type T -> coq_type T -> M A) :
  cget r >>= (fun u => cnew s >>= fun r' => cget r >>= k r' u) =
  cget r >>= (fun u => cnew s >>= fun r' => k r' u u).
Proof.
apply/boolp.funext => e.
have [u Hr|u T1 Hr T1u|Hr] := ntherrorP e r.
- by rewrite (Some_cget u)// (Some_cget u)// (cnewgetD_helper _ _ Hr)//.
- by rewrite !MS_bindE (nocoerce_cget Hr).
- by rewrite !MS_bindE None_cget.
Qed.

Lemma cgetnewE T1 T2 (r1 : loc T1) (s : coq_type T2) (A : UU0)
    (k1 k2 : loc T2 -> M A) :
  (forall r2 : loc T2, loc_id r1 != loc_id r2 -> k1 r2 = k2 r2) ->
  cget r1 >> (cnew s >>= k1) = cget r1 >> (cnew s >>= k2).
Proof.
move=> Hk.
apply/boolp.funext => e.
have [u r1u|T' s' Hr1 T1s'|Hr] := ntherrorP e r1.
- rewrite (Some_cget u)// (Some_cget u)// !bind_cnew Hk// neq_ltn.
  by case: e r1u => /= e /nth_error_size ->.
- by rewrite !MS_bindE (nocoerce_cget Hr1).
- by rewrite !MS_bindE None_cget.
Qed.

Lemma Some_cputget' (T T' : ml_type) (r : loc T) (r' : loc T') (s s' : coq_type T)
  (e : Env) (s'' : coq_type T) :
  nth_error (ofEnv e) (loc_id r) = Some (mkbind s'') ->
  (cput r s >> cget r') e = cget r' (mkEnv (set_nth def (ofEnv e) (loc_id r) (mkbind s))).
Proof.
move=> ers''.
destruct e as [e].
rewrite MS_bindE/=.
by rewrite ers'' !coerce_Some//=.
Qed.

Lemma cgetputC T1 T2 (r1 : loc T1) (r2 : loc T2) (s : coq_type T2) :
  cget r1 >> cput r2 s = cput r2 s >> cget r1 >> skip.
Proof.
(*apply/boolp.funext => e.
have [u r1u|T' u r1u T1u|Hr1] := ntherrorP e r1.
- rewrite (Some_cget u)//.
  have [v r2v|T' v r2v T2v|r2v] := ntherrorP e r2.
  + rewrite bindA !MS_bindE.
    admit.
  + admit.
  + by rewrite !MS_bindE !None_cput.
- rewrite MS_bindE (nocoerce_cget r1u)// bindfailf.
  admit.
- rewrite MS_bindE None_cget// bindfailf.*)
apply/boolp.funext => -[st] /=.
rewrite bindE /= /bindS MS_mapE /= fmapE /= bindA /=.
rewrite [in RHS]bindE /= /bindS MS_mapE /= fmapE /= 2!bindA /= /cget /cput.
case Hr1 : (nth_error st (loc_id r1)) => [[T1' v1]|] /=; last first.
  rewrite bindfailf.
  case Hr2 : (nth_error st (loc_id r2)) => [[T2' v2]|] /=;
    last by rewrite bindfailf.
  case Hc: (coerce T2' s) => [u|]; last by rewrite bindfailf.
  rewrite bindE /= /bindS /= bindE /=.
  by rewrite (nth_error_set_nth_none _ _ Hr1 Hr2).
case Hr2 : (nth_error st (loc_id r2)) => [[T2' v2]|] /=; last first.
  rewrite bindfailf.
  case Hc: (coerce T1 v1) => [u|]; last by rewrite bindfailf.
  by rewrite bindE/= bindE/= Hr2.
rewrite {1 3}/coerce.
case: eqVneq => [HT1|]; last first.
  rewrite bindfailf.
  case: eqVneq => [HT2|]; last by rewrite bindfailf.
  subst T2'.
  rewrite -eq_rect_eq.
  rewrite bindE/= bindE/=.
  case/boolP: (loc_id r1 == loc_id r2) => [/eqP|] Hr.
    rewrite -Hr nth_error_set_nth /coerce.
    move: Hr2; rewrite -Hr Hr1 => -[] HT2.
    subst T1'.
    by case: eqVneq.
  rewrite (nth_error_set_nth_other _ _ Hr Hr1) /coerce.
  by case: eqVneq.
rewrite bindE /= bindE /= Hr2 {1}/coerce.
case: eqVneq => HT2 //.
subst T1' T2'.
rewrite -!eq_rect_eq.
rewrite bindE /= bindE /=.
case/boolP: (loc_id r1 == loc_id r2) => [/eqP|] Hr.
  rewrite -Hr nth_error_set_nth /coerce.
  move: Hr2; rewrite -Hr Hr1 => -[] HT2.
  subst T2.
  by case: eqVneq => //; rewrite eqxx.
by rewrite(nth_error_set_nth_other _ _ Hr Hr1) coerce_Some.
Qed.

Lemma cputC T1 T2 (r1 : loc T1) (r2 : loc T2) (s1 : coq_type T1)
    (s2 : coq_type T2) (A : UU0) :
  loc_id r1 != loc_id r2 \/ JMeq s1 s2 ->
  cput r1 s1 >> cput r2 s2 = cput r2 s2 >> cput r1 s1.
Proof.
move=> H.
apply/boolp.funext => -[st] /=.
rewrite bindE /= /bindS MS_mapE /= fmapE /= bindA /=.
rewrite [in RHS]bindE /= /bindS MS_mapE /= fmapE /= bindA /= /cput.
case Hr1: (nth_error _ _) => [[T1' u]|]; last first.
  rewrite bindfailf.
  case Hr2: (nth_error _ _) => [[T2' v]|]; last by rewrite bindfailf.
  case Hc: (coerce T2' s2) => [u|]; last by rewrite bindfailf.
  rewrite !bindE /=.
  rewrite !bindE /=.
  case/boolP: (loc_id r1 == loc_id r2) => Hr.
    by rewrite -(eqP Hr) Hr1 in Hr2.
  by rewrite (nth_error_set_nth_none _ _ Hr1 Hr2).
case/boolP: (loc_id r1 == loc_id r2) H => [/eqP|] Hr /= H.
  rewrite -Hr Hr1.
  case/boolP: (T1 == T2) => /eqP HT; last first.
    rewrite /coerce.
    case: eqVneq => [HT1|]; last first.
      rewrite bindfailf.
      case: eqVneq => HT2; last by rewrite bindfailf.
      subst T1'.
      rewrite -eq_rect_eq bindE /= bindE /= nth_error_set_nth.
      by case: eqVneq.
    subst T1'.
    rewrite -eq_rect_eq bindE /= bindE /= nth_error_set_nth.
    by case: eqVneq => [/esym|] //.
  subst T2.
  rewrite /coerce.
  case: eqVneq => [HT1|] //.
  subst T1'.
  rewrite -eq_rect_eq bindE /= bindE /= bindE /= bindE /= !nth_error_set_nth.
  case: eqVneq => HT1 //.
  rewrite -!eq_rect_eq.
  case: H => // H.
  by move: (JMeq_eq H) => <-.
case Hr2: (nth_error _ _) => [[T2' v]|]; last first.
  rewrite bindfailf.
  case Hc: (coerce T1' s1) => [v|]; last by rewrite bindfailf.
  rewrite !bindE /=.
  rewrite !bindE /=.
  by rewrite (nth_error_set_nth_none _ _ Hr2 Hr1).
rewrite {1 3}/coerce.
case: eqVneq => [HT1|]; last first.
  rewrite bindfailf.
  case: eqVneq => [HT2|]; last by rewrite bindfailf.
  subst T2'.
  rewrite -eq_rect_eq.
  rewrite bindE /=.
  rewrite !bindE /=.
  rewrite (nth_error_set_nth_other _ _ Hr Hr1) /coerce.
  by case: eqVneq.
subst T1'.
rewrite -eq_rect_eq /coerce.
rewrite bindE /= bindE /= (nth_error_set_nth_other _ _ _ Hr2);
  last by rewrite eq_sym.
case: eqVneq => HT2' //.
subst T2'.
rewrite -eq_rect_eq bindE /= bindE /= (nth_error_set_nth_other _ _ Hr Hr1).
case: eqVneq => [HT1|]; last by rewrite eqxx.
by rewrite -eq_rect_eq set_set_nth (negbTE Hr).
Qed.

Lemma cputgetC T1 T2 (r1 : loc T1) (r2 : loc T2) (s1 : coq_type T1)
    (A : UU0) (k : coq_type T2 -> M A) :
  loc_id r1 != loc_id r2 ->
  cput r1 s1 >> cget r2 >>= k = cget r2 >>= (fun v => cput r1 s1 >> k v).
Proof.
move=> Hr.
apply/boolp.funext => -[st] /=.
rewrite !bindA.
rewrite bindE /= /bindS MS_mapE /= fmapE /= bindA /=.
rewrite [in RHS]bindE /= /bindS MS_mapE /= fmapE /= bindA /= /cput /cget.
case Hr1: (nth_error _ _) => [[T1' u]|]; last first.
  rewrite bindfailf.
  case Hr2: (nth_error _ _) => [[T2' v]|]; last by rewrite bindfailf.
  case Hc: (coerce T2 v) => [u|]; last by rewrite bindfailf.
  by rewrite !bindE /= !bindE /= /bindS MS_mapE /= fmapE Hr1 bindfailf.
case Hr2: (nth_error _ _) => [[T2' v]|]; last first.
  rewrite bindfailf.
  case Hc: (coerce T1' s1) => [v|]; last by rewrite bindfailf.
  rewrite !bindE /= !bindE /= /bindS MS_mapE /= fmapE.
  by rewrite (nth_error_set_nth_none _ _ Hr2 Hr1) bindfailf.
rewrite {1 3}/coerce.
case: eqVneq => [HT1|]; last first.
  rewrite bindfailf.
  case: eqVneq => [HT2|]; last by rewrite bindfailf.
  subst T2'.
  rewrite -eq_rect_eq.
  rewrite bindE /= bindE /= bindE /= /bindS /= MS_mapE /= fmapE Hr1 /coerce.
  by case: eqVneq.
subst T1'.
rewrite -eq_rect_eq /coerce.
rewrite bindE /= bindE /= bindE /= /bindS /= MS_mapE /= fmapE.
rewrite (nth_error_set_nth_other _ _ _ Hr2); last by rewrite eq_sym.
case: eqVneq => HT2' //.
subst T2'.
rewrite -eq_rect_eq bindE /= bindE /= bindE /= bindE /=.
rewrite /bindS /= MS_mapE /= fmapE Hr1.
case: eqVneq => [HT1|]; last by rewrite eqxx.
by rewrite -eq_rect_eq bindE.
Qed.

Lemma cputnewC T T' (r : loc T) (s : coq_type T) (s' : coq_type T') A
    (k : loc T' -> M A) :
  cget r >> (cnew s' >>= fun r' => cput r s >> k r') =
  cput r s >> (cnew s' >>= k).
Proof.
apply/boolp.funext => -[st] /=.
rewrite bindE /= /bindS MS_mapE /= fmapE /= bindA /=.
rewrite [in RHS]bindE /= /bindS MS_mapE /= fmapE /= bindA /= /cget /cput.
case Hr: (nth_error _ _) => [[T1 u]|]; last by rewrite bindfailf.
rewrite {1 3}/coerce.
case: eqVneq => [H|] /=; last by case: eqVneq => H' //; elim H.
subst T1.
rewrite bindE /= /bindS /= bindE /= bindE /= /bindS /= MS_mapE /= fmapE /=.
rewrite bindE /= /bindS /= bindE /= bindE /= /bindS /= MS_mapE /= fmapE /=.
rewrite (nth_error_rcons_some _ Hr).
rewrite /coerce.
case: eqVneq => // H.
rewrite -eq_rect_eq.
rewrite bindE /= /bindS /= bindE /= bindE /= /bindS /= MS_mapE /= fmapE /=.
rewrite bindE /= /bindS /=.
rewrite /fresh_loc/=.
rewrite (nth_error_size_set_nth _ _ Hr).
by rewrite (nth_error_set_nth_rcons _ _ _ Hr).
Qed.

Lemma crunret (A B : UU0) (m : M A) (s : B) :
  crun m -> crun (m >> Ret s) = Some s.
Proof.
rewrite /crun /= bindE /= /bindS MS_mapE /= fmapE /= bindA /=.
by case Hm: (m (mkEnv [::])).
Qed.

Lemma crunskip : crun skip = Some tt.
Proof. by []. Qed.

Lemma crunnew (A : UU0) T (m : M A) (s : A -> coq_type T) :
  crun m -> crun (m >>= fun x => cnew (s x)).
Proof.
rewrite /crun /= bindE /= /bindS MS_mapE /= fmapE /= bindA /=.
by case Hm: (m _).
Qed.

Lemma crunnewget (A : UU0) T (m : M A) (s : A -> coq_type T) :
  crun m -> crun (m >>= fun x => cnew (s x) >>= @cget T).
Proof.
rewrite /crun /= bindE /= /bindS MS_mapE /= fmapE /= bindA /=.
case Hm: (m _) => [|[a b]] // _.
by rewrite bindE /= bindE /= -(bindmret (_ >>= _)) bindA cnewget bindE.
Qed.

Lemma crungetnew (A : UU0) T1 T2 (m : M A) (r : A -> loc T1)
  (s : A -> coq_type T2) :
  crun (m >>= fun x => cget (r x)) ->
  crun (m >>= fun x => cnew (s x) >> cget (r x)).
Proof.
rewrite /crun /= !bindE /= /bindS !MS_mapE /= !fmapE /= !bindA /=.
case Hm: (m _) => [|[a b]] //.
rewrite !bindE /= !bindE /= /bindS MS_mapE /= fmapE /= bindA.
rewrite !bindE /= !bindE /= /cget.
case Hnth: nth_error => [[]|] //.
rewrite (nth_error_rcons_some _ Hnth).
by case Hcoe: coerce.
Qed.

Lemma crungetput (A : UU0) T (m : M A) (r : A -> loc T) (s : A -> coq_type T) :
  crun (m >>= fun x => cget (r x)) ->
  crun (m >>= fun x => cput (r x) (s x)).
Proof.
rewrite /crun /= !bindE /= /bindS !MS_mapE /= !fmapE /= !bindA /=.
case Hm: (m _) => [|[a [b]]] //=.
rewrite !bindE /= !bindE /= /cget /cput /=.
case Hnth: nth_error => [[T' v]|] //.
case Hcoe: coerce => // _.
have /coerce_sym : is_true (coerce T v) by rewrite Hcoe.
move/(_ (s a)).
by case: coerce.
Qed.

Definition isMonadTypedStoreModel :=
  isMonadTypedStore.Build M cnewget cnewput cgetput cgetputskip
    cgetget cputget cputput cgetC cgetnewD cgetnewE cgetputC cputC
    cputgetC cputnewC
    crunret crunskip crunnew crunnewget crungetnew crungetput.
End ModelTypedStore.
