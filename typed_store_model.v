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
Parameter ml_type : Set.
Parameter ml_type_eq_dec : forall x y : ml_type, {x=y}+{x<>y}.
Variant loc : ml_type -> Type := mkloc T : nat -> loc T.
Parameter coq_type : forall M : Type -> Type, ml_type -> Type.
Parameter ml_undef : ml_type.
Parameter undef : forall M, coq_type M ml_undef.
End MLTYdef.

Module ModelTypedStore (MLtypes : MLTYdef).
Import MLtypes.
Module MLtypes'.
Definition ml_type := ml_type.
Definition ml_type_eq_dec := ml_type_eq_dec.
Definition coq_type := coq_type.
Definition loc := loc.
Definition locT := [eqType of nat].
Definition loc_id {T} (l : loc T) := let: mkloc _ n := l in n.
End MLtypes'.
Module MTypedStore := MonadTypedStore (MLtypes').
Import MLtypes'.
Import MLtypes.
Import MTypedStore.

Record binding (M : Type -> Type) :=
  mkbind { bind_type : ml_type; bind_val : coq_type M bind_type }.
Arguments mkbind {M}.

Definition M0 Env (T : UU0) := MS Env option_monad T.

#[bypass_check(positivity)]
Inductive Env := mkEnv : seq (binding (M0 Env)) -> Env.
Definition ofEnv '(mkEnv e) := e.
Definition sizeEnv '(mkEnv e) := size e.

Definition acto : UU0 -> UU0 := M0 Env.
Local Notation M := acto.
Local Notation coq_type := (coq_type M).

Definition def := mkbind ml_undef (undef M).
Local Notation nth_error := List.nth_error.

Definition extend_env T (v : coq_type T) (e : Env) :=
  mkEnv (rcons (ofEnv e) (mkbind T v)).
Definition fresh_loc (T : ml_type) (e : Env) := mkloc T (sizeEnv e).

Definition cnew T (v : coq_type T) : M (loc T) :=
  fun e => inr (fresh_loc T e, extend_env v e).

Definition coerce T1 T2 (v : coq_type T1) : option (coq_type T2) :=
  match ml_type_eq_dec T1 T2 with
  | left H => Some (eq_rect _ _ v _ H)
  | right _ => None
  end.

Lemma coerce_sym (T T' : ml_type) (s : coq_type T) (s' : coq_type T') :
  coerce T' s -> coerce T s'.
Proof.
rewrite /coerce.
case: ml_type_eq_dec => [h|h]; last by case: ml_type_eq_dec.
by case: ml_type_eq_dec => [//|g]; subst T'.
Qed.

Lemma coerce_eq (T T' : ml_type) (s : coq_type T) : coerce T' s -> T = T'.
Proof. by rewrite /coerce; case: ml_type_eq_dec. Qed.

Lemma coerce_Some (T : ml_type) (s : coq_type T) : coerce T s = Some s.
Proof. by rewrite /coerce; case: ml_type_eq_dec => // ?; rewrite -eq_rect_eq. Qed.

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
        let b := mkbind T' (u : coq_type _) in
        inr (tt, mkEnv (set_nth def st n b))
      else inl tt
    else inl tt.

Definition crun (A : UU0) (m : M A) : option A :=
  match m (mkEnv nil) with
  | inl _ => None
  | inr (a, _) => Some a
  end.

(* Make ml_type an eqType *)
Definition ml_type_eqb T1 T2 : bool := ml_type_eq_dec T1 T2.
Lemma ml_type_eqP : Equality.axiom ml_type_eqb.
Proof.
rewrite /ml_type_eqb => T1 T2.
by case: ml_type_eq_dec; constructor.
Qed.
Definition ml_type_eq_mixin := EqMixin ml_type_eqP.
Canonical ml_type_eqType := Eval hnf in EqType _ ml_type_eq_mixin.

(* WIP *)
Lemma MS_bindE [S : UU0] [M : monad] [A B : UU0] (m : MS S M A) (f : A -> MS S M B) s :
  (m >>= f) s = m s >>= uncurry f.
Proof. by []. Qed.

Lemma bind_cnew T (s : coq_type T) A (k : loc T -> coq_type T -> M A) e (f : loc T -> M (coq_type T)):
  let l := fresh_loc T e in
  (cnew s >>= (fun r => f r >>= k r)) e = (f l >>= k l) (extend_env s e).
Proof. by case: e. Qed.

Lemma bind_cnew' T (s : coq_type T) A B (k : loc T -> M A) e f :
  let l := fresh_loc T e in
  (cnew s >>= (fun r => f r >>= (fun (_ : B) => k r))) e =
    (f l >> k l) (extend_env s e).
Proof. by case: e. Qed.

Let Some_cget T (r : loc T) s e A (f : _ -> M A) :
  nth_error (ofEnv e) (loc_id r) = Some (mkbind T s) ->
  (cget r >>= f) e = f s e.
Proof. by move=> H; rewrite MS_bindE /cget H coerce_Some. Qed.
Arguments Some_cget {T r} s.

Let nocoerce_cget T (r : loc T) T' s' e :
  nth_error (ofEnv e) (loc_id r) = Some (mkbind T' s') ->
  ~ coerce T s' ->
  cget r e = fail.
Proof. by move=> H Ts'; rewrite /cget H; case: coerce Ts'. Qed.

Let None_cget T (r : loc T) e :
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

Let nocoerce_cput T (r : loc T) (s : coq_type T) T' s' e :
  nth_error (ofEnv e) (loc_id r) = Some (mkbind T' s') ->
  ~ coerce T s' ->
  cput r s e = fail.
Proof.
move=> H Ts'; move: e H => [e] H; rewrite /cput H.
have {}Ts' : ~ coerce T' s by apply: contra_not Ts'; exact: coerce_sym.
by case: coerce Ts'.
Qed.

Let None_cput T (r : loc T) (s : coq_type T) e :
  nth_error (ofEnv e) (loc_id r) = None ->
  cput r s e = fail.
Proof. by move=> H; move: e H => [e] H; rewrite /cput H. Qed.

Let cnewput T (s t : coq_type T) A (k : loc T -> M A) :
  cnew s >>= (fun r => cput r t >> k r) = cnew t >>= k.
Proof.
apply/boolp.funext => -[st].
rewrite bind_cnew' 2!MS_bindE /= nth_error_rcons_size coerce_Some.
by rewrite set_nth_rcons.
Qed.

Let cgetput T (r : loc T) (s : coq_type T) : cget r >> cput r s = cput r s.
Proof.
apply/boolp.funext => e.
move H : (nth_error (ofEnv e) (loc_id r)) => h; move: h H => [[T' s']|] H.
  have [Ts'|Ts'] := boolp.pselect (coerce T s').
    have ? := coerce_eq Ts'; subst T'.
    by rewrite (Some_cget _ _ _ _ H).
  by rewrite MS_bindE (nocoerce_cget H)// (nocoerce_cput _ H).
by rewrite MS_bindE None_cget// None_cput.
Qed.

Let Some_cput T (r : loc T) s e :
  nth_error (ofEnv e) (loc_id r) = Some (mkbind T s) ->
  cput r s e = (@skip M) e.
Proof.
move=> H.
destruct e as [e].
rewrite /cput/= H coerce_Some/=.
by rewrite nth_error_set_nth_id.
Qed.

Let Some_cputget T (r : loc T) (s : coq_type T) A (k : coq_type T -> M A)
  (e : Env) (s' : coq_type T) :
  nth_error (ofEnv e) (loc_id r) = Some (mkbind T s') ->
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

Let cgetputskip T (r : loc T) : cget r >>= cput r = cget r >> skip.
Proof.
apply/boolp.funext => e /=.
move H : (nth_error (ofEnv e) (loc_id r)) => h; move: h H => [[T' s']|] H.
  have [Ts'|Ts'] := boolp.pselect (coerce T s').
    have ? := coerce_eq Ts'; subst T'.
    rewrite (Some_cget _ _ _ _ H)//.
    rewrite (Some_cget _ _ _ _ H)//.
    by rewrite (Some_cput H).
  by rewrite !MS_bindE (nocoerce_cget H).
by rewrite !MS_bindE None_cget.
Qed.

Let cgetget T (r : loc T) (A : UU0) (k : coq_type T -> coq_type T -> M A) :
  cget r >>= (fun s => cget r >>= k s) = cget r >>= fun s => k s s.
Proof.
apply/boolp.funext => e /=.
move H : (nth_error (ofEnv e) (loc_id r)) => h; move: h H => [[T' s']|] H.
  have [Ts'|Ts'] := boolp.pselect (coerce T s').
    have ? := coerce_eq Ts'; subst T'.
    by do 3 rewrite (@Some_cget _ _ s')//.
  by rewrite !MS_bindE (nocoerce_cget H).
by rewrite !MS_bindE None_cget.
Qed.

Let cputget T (r: loc T) (s: coq_type T) (A: UU0) (k: coq_type T -> M A) :
  cput r s >> (cget r >>= k) = cput r s >> k s.
Proof.
apply/boolp.funext => e /=.
move H : (nth_error (ofEnv e) (loc_id r)) => h; move: h H => [[T' s']|] H.
  have [Ts'|Ts'] := boolp.pselect (coerce T s').
    have ? := coerce_eq Ts'; subst T'.
    by rewrite (Some_cputget _ _ H).
  by rewrite !MS_bindE (nocoerce_cput _ H).
by rewrite 2!MS_bindE None_cput.
Qed.

Lemma Some_cputput (T : ml_type) (r : loc T) (s s' : coq_type T)
  (e : Env) (s'' : coq_type T) :
  nth_error (ofEnv e) (loc_id r) = Some (mkbind T s'') ->
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

Let cputput T (r : loc T) (s s' : coq_type T) :
  cput r s >> cput r s' = cput r s'.
Proof.
apply/boolp.funext => e.
move H : (nth_error (ofEnv e) (loc_id r)) => h; move: h H => [[T'' s'']|] H.
  have [Ts''|Ts''] := boolp.pselect (coerce T s'').
    have ? := coerce_eq Ts''; subst T''.
    by rewrite (Some_cputput _ _ H).
  by rewrite !MS_bindE (nocoerce_cput _ H)// (nocoerce_cput _ H).
by rewrite MS_bindE !None_cput.
Qed.

Let cgetC T1 T2 (r1 : loc T1) (r2 : loc T2) (A : UU0)
           (k : coq_type T1 -> coq_type T2 -> M A) :
  cget r1 >>= (fun u => cget r2 >>= (fun v => k u v)) =
  cget r2 >>= (fun v => cget r1 >>= (fun u => k u v)).
Proof.
apply/boolp.funext => -[st] /=.
rewrite bindE /= /bindS MS_mapE /= fmapE /= bindA /=.
rewrite [in RHS]bindE /= /bindS MS_mapE /= fmapE /= bindA /= /cget.
case Hr1: (nth_error _ _) => [[T1' u]|]; last first.
  rewrite bindfailf.
  case Hr2: (nth_error _ _) => [[T2' v]|]; last by rewrite bindfailf.
  case Hc: (coerce T2 v) => [u|]; last by rewrite bindfailf.
  rewrite !bindE /=.
  by rewrite !bindE /= /bindS MS_mapE /= fmapE Hr1 bindfailf.
case Hr2: (nth_error _ _) => [[T2' v]|]; last first.
  rewrite bindfailf.
  case Hc: (coerce T1 u) => [v|]; last by rewrite bindfailf.
  rewrite !bindE /=.
  by rewrite !bindE /= /bindS MS_mapE /= fmapE Hr2 bindfailf.
rewrite {1 3}/coerce.
case: (ml_type_eq_dec _ _) => HT1; last first.
  rewrite bindfailf.
  case: (ml_type_eq_dec _ _) => HT2; last by rewrite bindfailf.
  subst T2'.
  rewrite -eq_rect_eq.
  rewrite bindE /=.
  rewrite 2!bindE /= /bindS MS_mapE /= fmapE /= bindA /= Hr1 {1}/coerce.
  case: (ml_type_eq_dec _ _) => //; by rewrite bindfailf.
subst T1'.
rewrite -eq_rect_eq.
rewrite bindE /=.
rewrite 2!bindE /= /bindS MS_mapE /= fmapE /= bindA /= Hr2 {1}/coerce.
case: (ml_type_eq_dec T2' T2) => HT2; last by rewrite !bindfailf.
subst T2'.
rewrite -eq_rect_eq.
rewrite !bindE /=.
rewrite !bindE /=.
rewrite /bindS MS_mapE /= fmapE /= bindA /= Hr1 /coerce.
case: (ml_type_eq_dec T1 T1) => // H.
by rewrite -eq_rect_eq.
Qed.

Let cgetnewD T T' (r : loc T) (s : coq_type T') A
           (k : loc T' -> coq_type T -> coq_type T -> M A) :
  cget r >>= (fun u => cnew s >>= fun r' => cget r >>= k r' u) =
  cget r >>= (fun u => cnew s >>= fun r' => k r' u u).
Proof.
apply/boolp.funext => -[st] /=.
rewrite bindE /= /bindS MS_mapE /= fmapE /= bindA /=.
rewrite [in RHS]bindE /= /bindS MS_mapE /= fmapE /= bindA /= /cget.
case Hr: (nth_error _ _) => [[T1 u]|]; last by rewrite bindfailf.
rewrite {1 3}/coerce.
case: ml_type_eq_dec => H /=; last by rewrite bindfailf.
subst T1.
rewrite bindE /= /bindS /= bindE /= bindE /= /bindS /= MS_mapE /= fmapE /=.
rewrite bindE /= /bindS /= bindE /= bindE /= /bindS /= MS_mapE /= fmapE /=.
rewrite (nth_error_rcons_some _ Hr).
rewrite /coerce.
case: ml_type_eq_dec => // H.
by rewrite -eq_rect_eq.
Qed.

Let cgetnewE T1 T2 (r1 : loc T1) (s : coq_type T2) (A : UU0)
    (k1 k2 : loc T2 -> M A) :
  (forall r2 : loc T2, loc_id r1 != loc_id r2 -> k1 r2 = k2 r2) ->
  cget r1 >> (cnew s >>= k1) = cget r1 >> (cnew s >>= k2).
Proof.
move=> Hk.
apply/boolp.funext => -[st] /=.
rewrite bindE /= /bindS MS_mapE /= fmapE /= bindA /=.
rewrite [in RHS]bindE /= /bindS MS_mapE /= fmapE /= bindA /= /cget.
case Hr1 : (nth_error st (loc_id r1)) => [[T1' v1]|] //=.
case Hc: (coerce T1 v1) => [u1|] //.
rewrite bindE /= bindE /= bindE /= /bindS MS_mapE /= fmapE /= bindA /=.
rewrite [in RHS]bindE /= [in RHS]bindE /= [in RHS]bindE /= /bindS MS_mapE /=.
rewrite fmapE /= bindA /= 2!bindE /=.
by rewrite Hk // neq_ltn /= (nth_error_size Hr1).
Qed.

Let cgetputC T1 T2 (r1 : loc T1) (r2 : loc T2) (s : coq_type T2) :
  cget r1 >> cput r2 s = cput r2 s >> cget r1 >> skip.
Proof.
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
case: (ml_type_eq_dec T1' T1) => HT1; last first.
  rewrite bindfailf.
  case: (ml_type_eq_dec T2 T2') => HT2; last by rewrite bindfailf.
  subst T2'.
  rewrite -eq_rect_eq.
  rewrite bindE/= bindE/=.
  case/boolP: (loc_id r1 == loc_id r2) => [/eqP|] Hr.
    rewrite -Hr nth_error_set_nth /coerce.
    move: Hr2; rewrite -Hr Hr1 => -[] HT2.
    subst T1'.
    by case: ml_type_eq_dec.
  rewrite (nth_error_set_nth_other _ _ Hr Hr1) /coerce.
  by case: ml_type_eq_dec.
rewrite bindE /= bindE /= Hr2 {1}/coerce.
case: ml_type_eq_dec => HT2 //.
subst T1' T2'.
rewrite -!eq_rect_eq.
rewrite bindE /= bindE /=.
case/boolP: (loc_id r1 == loc_id r2) => [/eqP|] Hr.
  rewrite -Hr nth_error_set_nth /coerce.
  move: Hr2; rewrite -Hr Hr1 => -[] HT2.
  subst T2.
  by case: ml_type_eq_dec.
rewrite (nth_error_set_nth_other _ _ Hr Hr1) /coerce.
by case: ml_type_eq_dec.
Qed.

Let cputC T1 T2 (r1 : loc T1) (r2 : loc T2) (s1 : coq_type T1)
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
    case: (ml_type_eq_dec T1 T1') => HT1; last first.
      rewrite bindfailf.
      case: (ml_type_eq_dec T2 T1') => HT2; last by rewrite bindfailf.
      subst T1'.
      rewrite -eq_rect_eq bindE /= bindE /= nth_error_set_nth.
      by case: ml_type_eq_dec.
    subst T1'.
    rewrite -eq_rect_eq bindE /= bindE /= nth_error_set_nth.
    by case: ml_type_eq_dec => [/esym|] //.
  subst T2.
  rewrite /coerce.
  case: ml_type_eq_dec => HT1 //.
  subst T1'.
  rewrite -eq_rect_eq bindE /= bindE /= bindE /= bindE /= !nth_error_set_nth.
  case: ml_type_eq_dec => HT1 //.
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
case: (ml_type_eq_dec _ _) => HT1; last first.
  rewrite bindfailf.
  case: (ml_type_eq_dec _ _) => HT2; last by rewrite bindfailf.
  subst T2'.
  rewrite -eq_rect_eq.
  rewrite bindE /=.
  rewrite !bindE /=.
  rewrite (nth_error_set_nth_other _ _ Hr Hr1) /coerce.
  by case: ml_type_eq_dec.
subst T1'.
rewrite -eq_rect_eq /coerce.
rewrite bindE /= bindE /= (nth_error_set_nth_other _ _ _ Hr2);
  last by rewrite eq_sym.
case: ml_type_eq_dec => HT2' //.
subst T2'.
rewrite -eq_rect_eq bindE /= bindE /= (nth_error_set_nth_other _ _ Hr Hr1).
case: ml_type_eq_dec => // HT1.
by rewrite -eq_rect_eq set_set_nth (negbTE Hr).
Qed.

Let cputgetC T1 T2 (r1 : loc T1) (r2 : loc T2) (s1 : coq_type T1)
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
case: (ml_type_eq_dec _ _) => HT1; last first.
  rewrite bindfailf.
  case: (ml_type_eq_dec _ _) => HT2; last by rewrite bindfailf.
  subst T2'.
  rewrite -eq_rect_eq.
  rewrite bindE /= bindE /= bindE /= /bindS /= MS_mapE /= fmapE Hr1 /coerce.
  by case: ml_type_eq_dec.
subst T1'.
rewrite -eq_rect_eq /coerce.
rewrite bindE /= bindE /= bindE /= /bindS /= MS_mapE /= fmapE.
rewrite (nth_error_set_nth_other _ _ _ Hr2); last by rewrite eq_sym.
case: ml_type_eq_dec => HT2' //.
subst T2'.
rewrite -eq_rect_eq bindE /= bindE /= bindE /= bindE /=.
rewrite /bindS /= MS_mapE /= fmapE Hr1.
case: ml_type_eq_dec => // HT1.
by rewrite -eq_rect_eq bindE.
Qed.

Let cputnewC T T' (r : loc T) (s : coq_type T) (s' : coq_type T') A
    (k : loc T' -> M A) :
  cget r >> (cnew s' >>= fun r' => cput r s >> k r') =
  cput r s >> (cnew s' >>= k).
Proof.
apply/boolp.funext => -[st] /=.
rewrite bindE /= /bindS MS_mapE /= fmapE /= bindA /=.
rewrite [in RHS]bindE /= /bindS MS_mapE /= fmapE /= bindA /= /cget /cput.
case Hr: (nth_error _ _) => [[T1 u]|]; last by rewrite bindfailf.
rewrite {1 3}/coerce.
case: ml_type_eq_dec => H /=; last by case ml_type_eq_dec => H' //; elim H.
subst T1.
rewrite bindE /= /bindS /= bindE /= bindE /= /bindS /= MS_mapE /= fmapE /=.
rewrite bindE /= /bindS /= bindE /= bindE /= /bindS /= MS_mapE /= fmapE /=.
rewrite (nth_error_rcons_some _ Hr).
rewrite /coerce.
case: ml_type_eq_dec => // H.
rewrite -eq_rect_eq.
rewrite bindE /= /bindS /= bindE /= bindE /= /bindS /= MS_mapE /= fmapE /=.
rewrite bindE /= /bindS /=.
rewrite /fresh_loc/=.
rewrite (nth_error_size_set_nth _ _ Hr).
by rewrite (nth_error_set_nth_rcons _ _ _ Hr).
Qed.

Let crunret (A B : UU0) (m : M A) (s : B) :
  crun m -> crun (m >> Ret s) = Some s.
Proof.
rewrite /crun /= bindE /= /bindS MS_mapE /= fmapE /= bindA /=.
by case Hm: (m (mkEnv [::])).
Qed.

Let crunskip : crun skip = Some tt.
Proof. by []. Qed.

Let crunnew (A : UU0) T (m : M A) (s : coq_type T) :
  crun m -> crun (m >> cnew s).
Proof.
rewrite /crun /= bindE /= /bindS MS_mapE /= fmapE /= bindA /=.
by case Hm: (m (mkEnv [::])) => [|[a [b]]].
Qed.

Canonical Structure isMonadTypedStoreModel :=
  isMonadTypedStore.Build M cnewget cnewput cgetput cgetputskip
    cgetget cputget cputput cgetC cgetnewD cgetnewE cgetputC cputC
    cputgetC cputnewC crunret crunskip crunnew.
End ModelTypedStore.
