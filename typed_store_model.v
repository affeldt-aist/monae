(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2023 monae authors, license: LGPL-2.1-or-later               *)
Require Import JMeq.
From mathcomp Require Import all_ssreflect finmap.
From mathcomp Require boolp.
#[local] Remove Hints boolp.Prop_irrelevance : core.
Require Import monae_lib.
From HB Require Import structures.
Require Import hierarchy monad_lib fail_lib state_lib trace_lib.
Require Import monad_transformer monad_model.

(******************************************************************************)
(*                        Model for typed store                               *)
(*                                                                            *)
(* Separate file as it requires disabling various sanity checks.              *)
(* Reuses coerce and locT_nat from monad_model.v.                             *)
(* Similarities with ModelTypedStore from monad_model.v                       *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.

Section ModelTypedStore.
Variable MLU : ML_universe.

Record binding (M : Type -> Type) :=
  mkbind { bind_type : MLU; bind_val : coq_type M bind_type }.
Arguments mkbind {M bind_type}.

Definition M0 Env (T : UU0) := MS Env option_monad T.

End ModelTypedStore.

#[bypass_check(positivity)]
Inductive Env (MLU : ML_universe) :=
  mkEnv : seq (binding MLU (M0 (Env _))) -> Env _.

Section ModelTypedStore_contd.
Variable MLU : ML_universe.

Definition ofEnv (e : Env MLU) := let: mkEnv e := e in e.
Definition sizeEnv e := size (ofEnv e).

Local Notation mkEnv := (@mkEnv MLU).
Local Notation Env := (@Env MLU).

Definition acto : UU0 -> UU0 := MS Env option_monad.
Local Notation M := acto.

Local Notation coq_type := (@coq_type MLU M).

Local Notation val_nonundef := (val_nonempty MLU).

Definition def := mkbind (@val_nonempty MLU M).

Local Notation ml_type := (MLU : Type).

Local Notation nth_error := List.nth_error.

Definition extend_env T (v : coq_type T) (e : Env) :=
  mkEnv (rcons (ofEnv e) (mkbind v)).
Definition fresh_loc (T : ml_type) (e : Env) := mkloc T (sizeEnv e).

Local Notation loc := (@loc ml_type locT_nat).

Let cnew T (v : coq_type T) : M (loc T) :=
  fun e => inr (fresh_loc T e, extend_env v e).

Let cget T (r : loc T) : M (coq_type T) :=
  fun st =>
    if nth_error (ofEnv st) (loc_id r) is Some (mkbind T' v) then
      if coerce T v is Some u then inr (u, st) else inl tt
    else inl tt.

Let cput T (r : loc T) (v : coq_type T) : M unit :=
  fun st =>
    let n := loc_id r in
    if nth_error (ofEnv st) n is Some (mkbind T' _) then
      if coerce T' v is Some u then
        let b := mkbind (u : coq_type T') in
        inr (tt, mkEnv (set_nth def (ofEnv st) n b))
      else inl tt
    else inl tt.

Let crun (A : UU0) (m : M A) : option A :=
  match m (mkEnv nil) with
  | inl _ => None
  | inr (a, _) => Some a
  end.

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
  ~~ coercible T s' ->
  cget r e = fail.
Proof. by move=> H Ts'; rewrite /cget H not_coercible. Qed.

Lemma None_cget T (r : loc T) e :
  nth_error (ofEnv e) (loc_id r) = None ->
  cget r e = fail.
Proof. by move=> H; rewrite /cget H. Qed.

(* Prove the laws *)
Let cnewget T (s : coq_type T) A (k : loc T -> coq_type T -> M A) :
  cnew s >>= (fun r => cget r >>= k r) = cnew s >>= (fun r => k r s).
Proof.
apply/boolp.funext => e.
by rewrite bind_cnew (Some_cget s)// nth_error_rcons_size.
Qed.

Lemma nocoerce_cput T (r : loc T) (s : coq_type T) T' (s' : coq_type T') e :
  nth_error (ofEnv e) (loc_id r) = Some (mkbind s') ->
  ~~ coercible T s' ->
  cput r s e = fail.
Proof.
move=> H Ts'; move: e H => [e] H; rewrite /cput H.
by rewrite not_coercible// (coercible_sym _ s').
Qed.

Lemma None_cput T (r : loc T) (s : coq_type T) e :
  nth_error (ofEnv e) (loc_id r) = None ->
  cput r s e = fail.
Proof. by move=> H; move: e H => [e] H; rewrite /cput H. Qed.

Let cnewput T (s t : coq_type T) A (k : loc T -> M A) :
  cnew s >>= (fun r => cput r t >> k r) = cnew t >>= k.
Proof.
apply/boolp.funext => e.
rewrite bind_cnew 2!MS_bindE.
by rewrite /cput/= nth_error_rcons_size coerce_Some set_nth_rcons.
Qed.

(*
Definition permutable T1 T2 (A : UU0) (k : loc T1 -> loc T2 -> M A) :=
  forall (n1 n2 : nat) (b1 b2 : binding M) (st : seq (binding M)),
    k (mkloc T1 n1) (mkloc T2 n2)
      (mkEnv (set_nth def (set_nth def st n1 b1) n2 b2)) =
    k (mkloc T1 n2) (mkloc T2 n1)
      (mkEnv (set_nth def (set_nth def st n2 b1) n1 b2)).

Let cnewC T1 T2 (s : coq_type T1) (t : coq_type T2)
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
    nth_error (ofEnv e) (loc_id r) = Some (mkbind s') -> ~~ coercible T s' ->
    nth_error_spec e r
  | NthError_None : nth_error (ofEnv e) (loc_id r) = None -> nth_error_spec e r.

Lemma ntherrorP (T : ml_type) (e : Env) (r : loc T) : nth_error_spec e r.
Proof.
case H : (nth_error (ofEnv e) (loc_id r)) => [[T' s']|].
  have [Ts'|Ts'] := boolP (coercible T s').
    have ? := coercible_eq Ts'; subst T'.
    exact: NthError H.
  exact: NthError_nocoerce H Ts'.
exact: NthError_None.
Qed.

Let cgetput T (r : loc T) (s : coq_type T) : cget r >> cput r s = cput r s.
Proof.
apply/boolp.funext => e.
have [s' H|T' s' H Ts'|H] := ntherrorP e r.
- by rewrite (Some_cget s').
- by rewrite MS_bindE (nocoerce_cget H)// (nocoerce_cput _ H).
- by rewrite MS_bindE None_cget// None_cput.
Qed.

(* TODO: at least rename *)
Lemma Some_cputE T (r : loc T) (s s' : coq_type T) e :
  nth_error (ofEnv e) (loc_id r) = Some (mkbind s') ->
  cput r s e = inr (tt, mkEnv (set_nth def (ofEnv e) (loc_id r) (mkbind s))).
Proof. by move=> H; rewrite /cput/= H coerce_Some. Qed.

Lemma Some_cput T (r : loc T) (s : coq_type T) e :
  nth_error (ofEnv e) (loc_id r) = Some (mkbind s) ->
  cput r s e = (@skip M) e.
Proof.
move=> H.
rewrite /cput/= H coerce_Some/= nth_error_set_nth_id//.
by destruct e.
Qed.

Lemma Some_cputget T (s' s : coq_type T) (r : loc T) A (k : coq_type T -> M A)
  (e : Env) :
  nth_error (ofEnv e) (loc_id r) = Some (mkbind s') ->
  (cput r s >> (cget r >>= k)) e = (cput r s >> k s) e.
Proof.
move=> H.
rewrite 2!MS_bindE (Some_cputE _ H).
by rewrite bindE/= (Some_cget s)// nth_error_set_nth.
Qed.
Arguments Some_cputget {T} s'.

Let cgetputskip T (r : loc T) : cget r >>= cput r = cget r >> skip.
Proof.
apply/boolp.funext => e /=.
have [s' H|T' s' H Ts'|H] := ntherrorP e r.
- by rewrite (Some_cget s')// (Some_cget s')// (Some_cput H).
- by rewrite !MS_bindE (nocoerce_cget H).
- by rewrite !MS_bindE None_cget.
Qed.

Let cgetget T (r : loc T) (A : UU0) (k : coq_type T -> coq_type T -> M A) :
  cget r >>= (fun s => cget r >>= k s) = cget r >>= fun s => k s s.
Proof.
apply/boolp.funext => e /=.
have [s' H|T' s' H Ts'|H] := ntherrorP e r.
- by do 3 rewrite (Some_cget s')//.
- by rewrite !MS_bindE (nocoerce_cget H).
- by rewrite !MS_bindE None_cget.
Qed.

Let cputget T (r : loc T) (s: coq_type T) (A: UU0) (k: coq_type T -> M A) :
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
rewrite MS_bindE/=.
rewrite [in LHS](Some_cputE _ H)//.
rewrite [in RHS](Some_cputE _ H)//.
rewrite bindE/= /cput.
rewrite nth_error_set_nth coerce_Some/=.
by rewrite set_set_nth eqxx.
Qed.

Let cputput T (r : loc T) (s s' : coq_type T) :
  cput r s >> cput r s' = cput r s'.
Proof.
apply/boolp.funext => e.
have [s'' H|T'' s'' H Ts''|H] := ntherrorP e r.
- by rewrite (Some_cputput _ _ H).
- by rewrite !MS_bindE (nocoerce_cput _ H)// (nocoerce_cput _ H).
- by rewrite MS_bindE !None_cput.
Qed.

Let cgetC T1 T2 (r1 : loc T1) (r2 : loc T2) (A : UU0)
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

Let cgetnewD T T' (r : loc T) (s : coq_type T') A
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

Let cgetnewE T1 T2 (r1 : loc T1) (s : coq_type T2) (A : UU0)
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

(* TODO: do not rely on bindE to pass option and do not unfold cget *)
Let cgetputC T1 T2 (r1 : loc T1) (r2 : loc T2) (s : coq_type T2) :
  cget r1 >> cput r2 s = cput r2 s >> cget r1 >> skip.
Proof.
apply/boolp.funext => e /=.
have [u r1u|T1' v1 Hr1 T1v1|Hr1] := ntherrorP e r1.
- rewrite (Some_cget u)// [in RHS]bindA MS_bindE.
  have [v r2v|T' v r2v T2v|Hr2] := ntherrorP e r2.
  + rewrite (Some_cputE _ r2v) [in RHS]bindE/=.
    have [r12|r12] := eqVneq (loc_id r1) (loc_id r2).
      move: r2v; rewrite -r12 r1u => -[?] _; subst T2.
      by rewrite MS_bindE /cget nth_error_set_nth// coerce_Some.
    by rewrite (Some_cget u)// (nth_error_set_nth_other _ _ r12 r1u).
  + by rewrite (nocoerce_cput _ _ T2v).
  + by rewrite None_cput.
- rewrite MS_bindE [RHS]MS_bindE bindA.
  have [v r2v|T' v r2v T2v|Hr2] := ntherrorP e r2.
  + rewrite {1}/cget Hr1.
    have [?|T1'T1] := eqVneq T1' T1.
    * subst T1'; rewrite coerce_Some.
      rewrite [in LHS]bindE/= (Some_cputE _ r2v) [in RHS]bindE/=.
      have [Hr|Hr] := eqVneq (loc_id r1) (loc_id r2).
        move: r2v; rewrite -Hr Hr1 => -[?] _; subst T2.
        by rewrite /cget nth_error_set_nth coerce_Some.
      by rewrite /cget (nth_error_set_nth_other _ _ Hr Hr1) coerce_Some.
    * rewrite coerce_None//= bindfailf (Some_cputE _ r2v) [in RHS]bindE/=.
      have [r12|r12] := eqVneq (loc_id r1) (loc_id r2).
        move: r2v; rewrite -r12 Hr1 => -[?] _; subst T1'.
        by rewrite /cget nth_error_set_nth coerce_None.
      by rewrite /cget (nth_error_set_nth_other _ _ r12 Hr1) coerce_None.
  + by rewrite (nocoerce_cget _ T1v1)// bindfailf (nocoerce_cput _ _ T2v).
  + by rewrite (nocoerce_cget _ T1v1)// None_cput// bindfailf.
- rewrite MS_bindE None_cget// bindfailf bindA MS_bindE.
  have [v r2v|T' v r2v T2v|Hr2] := ntherrorP e r2.
  + rewrite (Some_cputE _ r2v)/=.
    rewrite bindE/=.
    rewrite MS_bindE None_cget/= ?bindfailf//.
    by rewrite (nth_error_set_nth_none _ _ Hr1 r2v).
  + by rewrite (nocoerce_cput _ r2v).
  + by rewrite None_cput.
Qed.

Lemma cput_then_fail T1 T2 T1' e (s1' : coq_type T1')
    (r2 : loc T2) (s2 : coq_type T2)
    (r1 : loc T1) (s1 : coq_type T1) :
  nth_error (ofEnv e) (loc_id r1) = Some (mkbind s1') ->
  ~~ coercible T1 s1' ->
  (cput r2 s2 >> cput r1 s1) e = fail.
Proof.
move=> Hr1 T1s'.
have [v Hr2|T2' v Hr2 T2v|Hr2] := ntherrorP e r2; last first.
- by rewrite MS_bindE None_cput.
- by rewrite MS_bindE (nocoerce_cput _ _ T2v).
- rewrite MS_bindE (Some_cputE _ Hr2).
  rewrite bindE/=.
  have [Hr|Hr] := eqVneq (loc_id r1) (loc_id r2).
  + rewrite {1}/cput -Hr /= nth_error_set_nth.
    have [HT|HT] := eqVneq T1 T2; last by rewrite coerce_None.
    subst T2.
    rewrite coerce_Some//=.
    move: Hr1; rewrite Hr Hr2 => -[?]; subst T1' => _.
    by rewrite coercible_Some // in T1s'.
  + rewrite (nocoerce_cput _ _ T1s')//=.
    by rewrite (@nth_error_set_nth_other _ _ _ _ _ (mkbind s1')).
Qed.

Let cputC T1 T2 (r1 : loc T1) (r2 : loc T2) (s1 : coq_type T1)
    (s2 : coq_type T2) (A : UU0) :
  loc_id r1 != loc_id r2 \/ JMeq s1 s2 ->
  cput r1 s1 >> cput r2 s2 = cput r2 s2 >> cput r1 s1.
Proof.
move=> H; apply/boolp.funext => e /=.
have [u Hr1|T1' s'd Hr1 T1s'|Hr1] := ntherrorP e r1; last first.
  rewrite MS_bindE None_cput// bindfailf.
  have [v Hr2|T2' s' Hr2 T2s'|Hr2] := ntherrorP e r2; last first.
    by rewrite MS_bindE None_cput.
  + by rewrite MS_bindE (nocoerce_cput _ _ T2s').
  + rewrite MS_bindE (Some_cputE _ Hr2).
    rewrite bindE/=.
    by rewrite None_cput// (nth_error_set_nth_none _ _ Hr1 Hr2).
- rewrite MS_bindE (nocoerce_cput _ _ T1s')// bindfailf.
  by rewrite (cput_then_fail _ _ _ Hr1).
- rewrite MS_bindE (Some_cputE _ Hr1)/=.
  rewrite bindE/=.
  case/boolP: (loc_id r1 == loc_id r2) H => [/eqP|] Hr /=.
  + case => // H.
    rewrite MS_bindE.
    rewrite {2}/cput -Hr Hr1.
    case/boolP: (T1 == T2) => [/eqP HT|HT]; last first.
      rewrite coerce_None//; last by rewrite eq_sym.
      by rewrite /cput/= Hr nth_error_set_nth// coerce_None// eq_sym.
    subst T2.
    rewrite coerce_Some bindE/=.
    have ? := JMeq_eq H; subst s2.
    by rewrite /cput -Hr.
  + move=> _.
    have [v r2v|T2' s Hr2 T2s|Hr2] := ntherrorP e r2; last first.
    * rewrite MS_bindE None_cput/=; last first.
        by rewrite (nth_error_set_nth_none _ _ Hr2 Hr1).
      by rewrite None_cput.
    * rewrite MS_bindE.
      rewrite [in RHS](nocoerce_cput _ _ T2s)// bindfailf.
      rewrite (nocoerce_cput _ _ T2s)//=.
      by rewrite (nth_error_set_nth_other _ _ _ Hr2) 1?eq_sym.
    * rewrite MS_bindE.
      rewrite [in RHS](Some_cputE _ r2v).
      rewrite {1}/cput/=.
      rewrite (nth_error_set_nth_other _ _ _ r2v) 1?eq_sym//.
      rewrite coerce_Some.
      rewrite bindE/=.
      rewrite /cput (nth_error_set_nth_other _ _ Hr Hr1).
      rewrite coerce_Some.
      by rewrite set_set_nth (negbTE Hr).
Qed.

Let cputgetC T1 T2 (r1 : loc T1) (r2 : loc T2) (s1 : coq_type T1)
    (A : UU0) (k : coq_type T2 -> M A) :
  loc_id r1 != loc_id r2 ->
  cput r1 s1 >> cget r2 >>= k = cget r2 >>= (fun v => cput r1 s1 >> k v).
Proof.
move=> Hr; apply/boolp.funext => e /=; rewrite !bindA.
have [u Hr1|T1' s1' Hr1 T1s'|Hr1] := ntherrorP e r1.
- have [v Hr2|T' s' Hr2 T2s'|Hr2] := ntherrorP e r2.
  + rewrite (Some_cget _ _ _ _ Hr2).
    rewrite [in LHS]MS_bindE [in RHS]MS_bindE /cput Hr1 coerce_Some !bindretf/=.
    rewrite MS_bindE /cget (nth_error_set_nth_other _ _ _ Hr2) 1?eq_sym//.
    by rewrite coerce_Some.
  + rewrite [RHS]MS_bindE (nocoerce_cget _ T2s')// bindfailf.
    rewrite !MS_bindE /cput Hr1 coerce_Some bindretf//=.
    rewrite MS_bindE /cget/= (nth_error_set_nth_other _ _ _ Hr2) 1?eq_sym//.
    by rewrite not_coercible.
  + rewrite [in RHS]MS_bindE None_cget// bindfailf.
    rewrite MS_bindE /cput Hr1 coerce_Some bindretf/=.
    by rewrite MS_bindE /cget (nth_error_set_nth_none _ _ Hr2 Hr1).
- rewrite MS_bindE (nocoerce_cput _ _ T1s')// bindfailf.
  have [v Hr2|T' s' Hr2 T2s'|Hr2] := ntherrorP e r2.
  - by rewrite (Some_cget _ _ _ _ Hr2) MS_bindE (nocoerce_cput _ _ T1s').
  - by rewrite MS_bindE (nocoerce_cget _ T2s').
  - by rewrite MS_bindE None_cget.
- rewrite MS_bindE None_cput// bindfailf MS_bindE.
  have [v Hr2|T' s' Hr2 T2s'|Hr2] := ntherrorP e r2.
  + by rewrite /cget Hr2 coerce_Some bindretf//= MS_bindE None_cput.
  + by rewrite (nocoerce_cget Hr2).
  + by rewrite None_cget.
Qed.

Let cputnewC T T' (r : loc T) (s : coq_type T) (s' : coq_type T') A
    (k : loc T' -> M A) :
  cget r >> (cnew s' >>= fun r' => cput r s >> k r') =
  cput r s >> (cnew s' >>= k).
Proof.
apply/boolp.funext => e /=.
have [u Hr|T1 s1' Hr T1s'|Hr] := ntherrorP e r.
- rewrite (Some_cget _ _ _ _ Hr).
  rewrite [RHS]MS_bindE [in RHS]/cput Hr coerce_Some bindretf/=.
  rewrite !MS_bindE /cnew !bindretf/= !MS_bindE /cput.
  rewrite (nth_error_rcons_some _ Hr) coerce_Some bindretf/= /fresh_loc/=.
  rewrite /sizeEnv/= /extend_env/=.
  by rewrite (nth_error_size_set_nth _ _ Hr) (nth_error_set_nth_rcons _ _ _ Hr).
- rewrite 2!MS_bindE (nocoerce_cget _ T1s')// bindfailf.
  by rewrite (nocoerce_cput _ _ T1s').
- by rewrite 2!MS_bindE None_cget// bindfailf None_cput.
Qed.

Let crunret (A B : UU0) (m : M A) (s : B) :
  crun m -> crun (m >> Ret s) = Some s.
Proof. by rewrite /crun /= MS_bindE/=; case: (m _) => //- []. Qed.

Let crunskip : crun skip = Some tt.
Proof. by []. Qed.

Let crunnew (A : UU0) T (m : M A) (s : A -> coq_type T) :
  crun m -> crun (m >>= fun x => cnew (s x)).
Proof. by rewrite /crun /= MS_bindE; case: (m _) => // -[]. Qed.

Let crunnewget (A : UU0) T (m : M A) (s : A -> coq_type T) :
  crun m -> crun (m >>= fun x => cnew (s x) >>= @cget T).
Proof.
rewrite /crun /= MS_bindE.
case: (m _) => // -[a e] _.
by under eq_bind do under eq_uncurry do
  rewrite -(bindmret (_ >>= _)) bindA cnewget.
Qed.

Let crungetnew (A : UU0) T1 T2 (m : M A) (r : A -> loc T1)
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

Let crungetput (A : UU0) T (m : M A) (r : A -> loc T) (s : A -> coq_type T) :
  crun (m >>= fun x => cget (r x)) ->
  crun (m >>= fun x => cput (r x) (s x)).
Proof.
rewrite /crun /= !bindE /= /bindS !MS_mapE /= !fmapE /= !bindA /=.
case Hm: (m _) => [|[a [b]]] //=.
rewrite !bindE /= !bindE /= /cget /cput /=.
case Hnth: nth_error => [[T' v]|] //.
case: (eqVneq T' T) => T'T; last first.
  by rewrite coerce_None// 1?eq_sym// coerce_None.
subst T'.
by rewrite !coerce_Some.
Qed.

HB.instance Definition _ := Monad.on M.
HB.instance Definition isMonadTypedStoreModel :=
  isMonadTypedStore.Build _ M _ M cnewget cnewput cgetput cgetputskip
    cgetget cputget cputput cgetC cgetnewD cgetnewE cgetputC cputC
    cputgetC cputnewC
    crunret crunskip crunnew crunnewget crungetnew crungetput.

(* To restart computations *)
Definition W (A : UU0) : UU0 := unit + (A * Env).

Definition Restart A B (r : W A) (f : M B) : W B :=
  if r is inr (_, env) then f env else inl tt.

Definition FromW A (r : W A) : M A :=
  fun env => if r is inr (a, _) then inr (a, env) else inl tt.

End ModelTypedStore_contd.

Arguments W {MLU}.
