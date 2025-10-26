Require Import JMeq.
From mathcomp Require Import all_ssreflect.
From mathcomp Require boolp.
Require Import preamble.
From HB Require Import structures.
Require Import hierarchy monad_lib fail_lib state_lib monad_transformer typed_store_universe.
Require Import delay_monad_model elgotstate_model elgotexcept_model.

(**md**************************************************************************)
(* # Model of the typed store monad built using transformers                  *)
(*                                                                            *)
(* Contrary to typed_store_model.v, this model does not allow for functions   *)
(* in the store. But it is sound since it does not bypass positivity.         *)
(******************************************************************************)


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.

Definition locT_nat : eqType := nat.

Module ModelTypedStore.

Section ModelTypedStore.
Variables (MLU : ML_universe) (N : monad) (M0 : monad).

Local Notation coq_type := (@coq_type MLU N).

Local Notation ml_type := (MLU : Type).

Record binding :=
  mkbind { bind_type : ml_type; bind_val : coq_type bind_type }.


Definition acto : UU0 -> UU0 := MS (seq binding) (MX unit M0).
Local Notation M := acto.

Definition def : binding := mkbind (val_nonempty N).

Local Notation nth_error := List.nth_error.

Notation loc := (@loc ml_type locT_nat).

Let cnew T (v : coq_type T) : M (loc T) :=
  fun st => let n := size st in
            Ret (mkloc T n, rcons st (mkbind v)).

Let cget T (r : loc T) : M (coq_type T) :=
  fun st =>
    if nth_error st (loc_id r) is Some (mkbind T' v) then
      if coerce T v is Some u then Ret (u, st) else fail
    else fail.

Let cput T (r : loc T) (v : coq_type T) : M unit :=
  fun st =>
    let n := loc_id r in
    if nth_error st n is Some (mkbind T' _) then
      if coerce T' v is Some u then
        Ret (tt, set_nth def st n (mkbind u))
      else fail
    else fail.

Definition Env := seq binding.

Definition fresh_loc (T : ml_type) (e : Env) := mkloc T (size e).

Section mkbind.

Definition extend_env T (v : coq_type T) (e : Env) :=
  rcons e (mkbind v).

Variant nth_error_spec (T : ml_type) (e : Env) (r : loc T) : Type :=
  | NthError : forall s : coq_type T,
    nth_error e (loc_id r) = Some (mkbind s) -> nth_error_spec e r
  | NthError_nocoerce : forall T' (s' : coq_type T'),
    nth_error e (loc_id r) = Some (mkbind s') -> ~~ coercible T s' ->
    nth_error_spec e r
  | NthError_None : nth_error e (loc_id r) = None -> nth_error_spec e r.

Lemma ntherrorP (T : ml_type) (e : Env) (r : loc T) : nth_error_spec e r.
Proof.
case H : (nth_error e (loc_id r)) => [[T' s']|].
  have [Ts'|Ts'] := boolP (coercible T s').
    have ? := coercible_eq Ts'; subst T'.
    exact: NthError H.
  exact: NthError_nocoerce H Ts'.
exact: NthError_None.
Qed.


Lemma bind_cnew T (s : coq_type T) A (k : loc T -> M A) e :
  (cnew s >>= k) e = k (fresh_loc T e) (extend_env s e).
Proof. by rewrite MS_bindE /cnew/= bindretf. Qed.

Lemma Some_cget T (r : loc T) (s : coq_type T) e (A : UU0) (f : coq_type T -> M A) :
  nth_error e (loc_id r) = Some (mkbind s) ->
  (cget r >>= f) e = f s e.
Proof. by move=> H; rewrite MS_bindE /cget H coerce_Some bindretf. Qed.
Arguments Some_cget {T r} s.

Let cnewget T (s : coq_type T) A (k : loc T -> coq_type T -> M A) :
  cnew s >>= (fun r => cget r >>= k r) = cnew s >>= (fun r => k r s).
Proof.
apply/boolp.funext => e.
by rewrite !bind_cnew (Some_cget s) // nth_error_rcons_size.
Qed.

Let cnewput T (s t : coq_type T) A (k : loc T -> M A) :
  cnew s >>= (fun r => cput r t >> k r) = cnew t >>= k.
Proof.
apply/boolp.funext => e.
rewrite !bind_cnew.
by rewrite /cput/= MS_bindE nth_error_rcons_size coerce_Some set_nth_rcons bindretf.
Qed.

Lemma nocoerce_cget T (r : loc T) T' (s' : coq_type T') e :
  nth_error e (loc_id r) = Some (mkbind s') ->
  ~~ coercible T s' ->
  cget r e = fail.
Proof. by move=> H Ts'; rewrite /cget H not_coercible. Qed.

Lemma nocoerce_cput T (r : loc T) (s : coq_type T) (T' : ml_type)
    (s' : coq_type T') e :
  nth_error e (loc_id r) = Some (mkbind s') ->
  ~~ coercible T s' ->
  cput r s e = fail.
Proof.
by move=> H Ts'; rewrite /cput H not_coercible// (coercible_sym _ s').
Qed.

Lemma None_cget T (r : loc T) e :
  nth_error e (loc_id r) = None -> cget r e = fail.
Proof. by move=> H; rewrite /cget H. Qed.

Lemma None_cput T (r : loc T) (s : coq_type T) e :
  nth_error e (loc_id r) = None -> cput r s e = fail.
Proof. by move=> H; rewrite /cput H. Qed.

Definition cgetput T (r : loc T) (s : coq_type T) :
  cget r >> cput r s = cput r s.
Proof.
apply/boolp.funext => e.
have [s' H|T' s' H Ts'|H] := ntherrorP e r.
- by rewrite (Some_cget s').
- by rewrite MS_bindE (nocoerce_cget H)// (nocoerce_cput _ H) // bindfailf.
- by rewrite MS_bindE None_cget// None_cput // bindfailf.
Qed.

Lemma Some_cput T (r : loc T) (s : coq_type T) e :
  nth_error e (loc_id r) = Some (mkbind s) ->
  cput r s e = (@skip M) e.
Proof. by move=> H; rewrite /cput/= H coerce_Some/= nth_error_set_nth_id. Qed.

Let cgetputskip T (r : loc T) : cget r >>= cput r = cget r >> skip.
Proof.
apply/boolp.funext => e /=.
have [s' H|T' s' H Ts'|H] := ntherrorP e r.
- by rewrite (Some_cget s')// (Some_cget s')// (Some_cput H).
- by rewrite !MS_bindE (nocoerce_cget H) // !bindfailf.
- by rewrite !MS_bindE None_cget // !bindfailf.
Qed.

Let cgetget T (r : loc T) (A : UU0)
    (k : coq_type T -> coq_type T -> M A) :
  cget r >>= (fun s => cget r >>= k s) = cget r >>= fun s => k s s.
Proof.
apply/boolp.funext => e /=.
have [s' H|T' s' H Ts'|H] := ntherrorP e r.
- by do 3 rewrite (Some_cget s')//.
- by rewrite !MS_bindE (nocoerce_cget H) // !bindfailf.
- by rewrite !MS_bindE None_cget // !bindfailf.
Qed.

Lemma Some_cputE T (r : loc T) (s s' : coq_type T) e :
  nth_error e (loc_id r) = Some (mkbind s') ->
  cput r s e = Ret (tt, set_nth def e (loc_id r) (mkbind s))(*inr (tt, set_nth def e (loc_id r) (mkbind s))*).
Proof. by move=> H; rewrite /cput/= H coerce_Some. Qed.

Lemma Some_cputget T (s' s : coq_type T) (r : loc T) A (k : coq_type T -> M A)
  (e : Env) :
  nth_error e (loc_id r) = Some (mkbind s') ->
  (cput r s >> (cget r >>= k)) e = (cput r s >> k s) e.
Proof.
move=> H.
rewrite 2!MS_bindE (Some_cputE _ H) !bindretf /=.
by rewrite (Some_cget s)// nth_error_set_nth.
Qed.
Arguments Some_cputget {T} s'.

Let cputget T (r : loc T) (s : coq_type T) (A : UU0)
    (k : coq_type T -> M A) :
  cput r s >> (cget r >>= k) = cput r s >> k s.
Proof.
apply/boolp.funext => e /=.
have [s' H|T' s' H Ts'|H] := ntherrorP e r.
- by rewrite (Some_cputget s').
- by rewrite !MS_bindE (nocoerce_cput _ H) // !bindfailf.
- by rewrite 2!MS_bindE None_cput // !bindfailf.
Qed.

Lemma Some_cputput (T : ml_type) (r : loc T) (s s' : coq_type T)
  (e : Env) (s'' : coq_type T) :
  nth_error e (loc_id r) = Some (mkbind s'') ->
  (cput r s >> cput r s') e = cput r s' e.
Proof.
move=> H.
rewrite MS_bindE/=.
rewrite [in LHS](Some_cputE _ H)//.
rewrite [in RHS](Some_cputE _ H)// !bindretf /= /cput.
rewrite nth_error_set_nth coerce_Some/=.
by rewrite set_set_nth eqxx.
Qed.

Let cputput T (r : loc T) (s s' : coq_type T) :
  cput r s >> cput r s' = cput r s'.
Proof.
apply/boolp.funext => e.
have [s'' H|T'' s'' H Ts''|H] := ntherrorP e r.
- by rewrite (Some_cputput _ _ H).
- by rewrite !MS_bindE (nocoerce_cput _ H)// (nocoerce_cput _ H) // !bindfailf.
- by rewrite MS_bindE !None_cput // !bindfailf.
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
  + by rewrite 2!MS_bindE (nocoerce_cget Hr2)// !bindfailf.
  + by rewrite !MS_bindE None_cget // !bindfailf.
- rewrite MS_bindE (nocoerce_cget Hr1)// bindfailf.
  have [v Hr2|v T2' Hr2 T2v|Hr2] := ntherrorP e r2.
  + by rewrite (Some_cget v)// MS_bindE (nocoerce_cget Hr1) // !bindfailf.
  + by rewrite MS_bindE (nocoerce_cget Hr2) // !bindfailf.
  + by rewrite MS_bindE None_cget // !bindfailf.
- rewrite MS_bindE None_cget// bindfailf.
  have [v Hr2|v T2' Hr2 T2v|Hr2] := ntherrorP e r2.
  + by rewrite (Some_cget v)// MS_bindE None_cget // !bindfailf.
  + by rewrite MS_bindE (nocoerce_cget Hr2) // !bindfailf.
  + by rewrite MS_bindE !None_cget // !bindfailf.
Qed.

(* NB: this is similar to the cnewget law *)
Let cnewgetD_helper e T T' r v (s : coq_type T') A (k : loc T' -> coq_type T -> M A) :
  nth_error e (loc_id r) = Some (mkbind v) ->
  (cnew s >>= (fun r' => cget r >>= k r')) e = (cnew s >>= (fun r => k r v)) e.
Proof.
move=> H.
rewrite bind_cnew//.
rewrite (Some_cget v) //.
- by rewrite bind_cnew.
- by rewrite  (nth_error_rcons_some _ H) .
Qed.

Let cgetnewD T T' (r : loc T) (s : coq_type T') A
           (k : loc T' -> coq_type T -> coq_type T -> M A) :
  cget r >>= (fun u => cnew s >>= fun r' => cget r >>= k r' u) =
  cget r >>= (fun u => cnew s >>= fun r' => k r' u u).
Proof.
apply/boolp.funext => e.
have [u Hr|u T1 Hr T1u|Hr] := ntherrorP e r.
- by rewrite (Some_cget u)// (Some_cget u)// (cnewgetD_helper _ _ Hr)//.
- by rewrite !MS_bindE (nocoerce_cget Hr) // !bindfailf.
- by rewrite !MS_bindE None_cget // !bindfailf.
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
- by move: r1u => /= /nth_error_size ->.
- by rewrite !MS_bindE (nocoerce_cget Hr1) // !bindfailf.
- by rewrite !MS_bindE None_cget // !bindfailf.
Qed.

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
      by rewrite MX_mapE fmapE bindretf /= /bindX bindretf /= /cget /= MS_bindE nth_error_set_nth// coerce_Some bindretf /=.
    by rewrite MX_mapE fmapE bindretf /= /bindX bindretf /= (Some_cget u)// (nth_error_set_nth_other _ _ r12 r1u).
  + by rewrite (nocoerce_cput _ _ T2v) // !bindfailf.
  + by rewrite None_cput // !bindfailf.
- rewrite MS_bindE [RHS]MS_bindE bindA.
  have [v r2v|T' v r2v T2v|Hr2] := ntherrorP e r2.
  + rewrite {1}/cget Hr1.
    have [?|T1'T1] := eqVneq T1' T1.
    * subst T1'; rewrite coerce_Some.
      rewrite [in LHS]bindE/= !MX_mapE !fmapE bindretf /= /bindX !bindretf (Some_cputE _ r2v) [in RHS]bindE/=.
      have [Hr|Hr] := eqVneq (loc_id r1) (loc_id r2).
        move: r2v; rewrite -Hr Hr1 => -[?] _; subst T2.
        by rewrite !MX_mapE !fmapE bindretf /= /bindX !bindretf /= /cget nth_error_set_nth coerce_Some bindretf /=.
      by rewrite MX_mapE fmapE bindretf /= /bindX bindretf /=/cget (nth_error_set_nth_other _ _ Hr Hr1) coerce_Some bindretf /=.
    * rewrite coerce_None//= bindfailf (Some_cputE _ r2v) [in RHS]bindE/=.
      have [r12|r12] := eqVneq (loc_id r1) (loc_id r2).
        move: r2v; rewrite -r12 Hr1 => -[?] _; subst T1'.
        by rewrite MX_mapE fmapE bindretf /= /bindX bindretf /=/cget nth_error_set_nth coerce_None // !bindfailf.
      by rewrite  MX_mapE fmapE bindretf /= /bindX bindretf /=/cget (nth_error_set_nth_other _ _ r12 Hr1) coerce_None // !bindfailf.
  + by rewrite (nocoerce_cget _ T1v1)// bindfailf (nocoerce_cput _ _ T2v) // !bindfailf.
  + by rewrite (nocoerce_cget _ T1v1)// None_cput// !bindfailf.
- rewrite MS_bindE None_cget// bindfailf bindA MS_bindE.
  have [v r2v|T' v r2v T2v|Hr2] := ntherrorP e r2.
  + rewrite (Some_cputE _ r2v)/=.
    rewrite bindE/= MX_mapE fmapE bindretf /= /bindX bindretf /=.
    rewrite MS_bindE None_cget/= ?bindfailf//.
    by rewrite (nth_error_set_nth_none _ _ Hr1 r2v).
  + by rewrite (nocoerce_cput _ r2v) // !bindfailf.
  + by rewrite None_cput // !bindfailf.
Qed.

Lemma cput_then_fail T1 T2 T1' e (s1' : coq_type T1')
    (r2 : loc T2) (s2 : coq_type T2)
    (r1 : loc T1) (s1 : coq_type T1) :
  nth_error e (loc_id r1) = Some (mkbind s1') ->
  ~~ coercible T1 s1' ->
  (cput r2 s2 >> cput r1 s1) e = fail.
Proof.
move=> Hr1 T1s'.
have [v Hr2|T2' v Hr2 T2v|Hr2] := ntherrorP e r2; last first.
- by rewrite MS_bindE None_cput // !bindfailf.
- by rewrite MS_bindE (nocoerce_cput _ _ T2v) // !bindfailf.
- rewrite MS_bindE (Some_cputE _ Hr2).
  rewrite bindE/=.
  have [Hr|Hr] := eqVneq (loc_id r1) (loc_id r2).
  + rewrite MX_mapE fmapE bindretf /= /bindX bindretf /= {1}/cput -Hr /= nth_error_set_nth.
    have [HT|HT] := eqVneq T1 T2; last by rewrite coerce_None.
    subst T2.
    rewrite coerce_Some//=.
    move: Hr1; rewrite Hr Hr2 => -[?]; subst T1' => _.
    by rewrite coercible_Some // in T1s'.
  + rewrite MX_mapE fmapE bindretf /= /bindX bindretf /= (nocoerce_cput _ _ T1s')//=.
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
    by rewrite MS_bindE None_cput // !bindfailf.
  + by rewrite MS_bindE (nocoerce_cput _ _ T2s') // !bindfailf.
  + rewrite MS_bindE (Some_cputE _ Hr2).
    rewrite bindE/= MX_mapE fmapE bindretf /= /bindX bindretf /=.
    by rewrite None_cput// (nth_error_set_nth_none _ _ Hr1 Hr2).
- rewrite MS_bindE (nocoerce_cput _ _ T1s')// bindfailf.
  by rewrite (cput_then_fail _ _ _ Hr1).
- rewrite MS_bindE (Some_cputE _ Hr1)/= bindretf/=.
  case/boolP: (loc_id r1 == loc_id r2) H => [/eqP|] Hr /=.
  + case => // H.
    rewrite MS_bindE.
    rewrite {2}/cput -Hr Hr1.
    case/boolP: (T1 == T2) => [/eqP HT|HT]; last first.
      rewrite coerce_None//; last by rewrite eq_sym.
      rewrite /cput/= Hr nth_error_set_nth// coerce_None//.
      by rewrite bindfailf.
      by rewrite eq_sym.
    subst T2.
    rewrite coerce_Some bindE/=.
    have ? := JMeq_eq H; subst s2.
    rewrite MX_mapE fmapE bindretf /= /bindX bindretf /=.
    by rewrite /cput -Hr.
  + move=> _.
    have [v r2v|T2' s Hr2 T2s|Hr2] := ntherrorP e r2; last first.
    * rewrite MS_bindE None_cput/=; last first.
        by rewrite (nth_error_set_nth_none _ _ Hr2 Hr1).
      by rewrite None_cput // !bindfailf.
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
      rewrite MX_mapE fmapE bindretf /= /bindX bindretf /=.
      rewrite /cput (nth_error_set_nth_other _ _ Hr Hr1).
      rewrite coerce_Some.
      by rewrite set_set_nth (negbTE Hr).
Qed.
Let cputgetC T1 T2 (r1 : loc T1) (r2 : loc T2) (s1 : coq_type T1)
    (A : UU0) (k : coq_type T2 -> M A) :
  loc_id r1 != loc_id r2 ->
  cput r1 s1 >> (cget r2 >>= k) = cget r2 >>= (fun v => cput r1 s1 >> k v).
Proof.
move=> Hr; apply/boolp.funext => e /=.
have [u Hr1|T1' s1' Hr1 T1s'|Hr1] := ntherrorP e r1.
- have [v Hr2|T' s' Hr2 T2s'|Hr2] := ntherrorP e r2.
  + rewrite (Some_cget _ _ _ _ Hr2).
    rewrite [in LHS]MS_bindE [in RHS]MS_bindE /cput Hr1 coerce_Some !bindretf/=.
    rewrite MS_bindE /cget (nth_error_set_nth_other _ _ _ Hr2) 1?eq_sym//.
    by rewrite coerce_Some bindretf.
  + rewrite [RHS]MS_bindE (nocoerce_cget _ T2s')// bindfailf.
    rewrite !MS_bindE /cput Hr1 coerce_Some bindretf//=.
    rewrite MS_bindE /cget/= (nth_error_set_nth_other _ _ _ Hr2) 1?eq_sym//.
    by rewrite not_coercible // !bindfailf.
  + rewrite [in RHS]MS_bindE None_cget// bindfailf.
    rewrite MS_bindE /cput Hr1 coerce_Some bindretf/=.
    by rewrite MS_bindE /cget (nth_error_set_nth_none _ _ Hr2 Hr1) // !bindfailf.
- rewrite MS_bindE (nocoerce_cput _ _ T1s')// bindfailf.
  have [v Hr2|T' s' Hr2 T2s'|Hr2] := ntherrorP e r2.
  - by rewrite (Some_cget _ _ _ _ Hr2) MS_bindE (nocoerce_cput _ _ T1s') // !bindfailf.
  - by rewrite MS_bindE (nocoerce_cget _ T2s') // !bindfailf.
  - by rewrite MS_bindE None_cget // !bindfailf.
- rewrite MS_bindE None_cput// bindfailf MS_bindE.
  have [v Hr2|T' s' Hr2 T2s'|Hr2] := ntherrorP e r2.
  + by rewrite /cget Hr2 coerce_Some bindretf//= MS_bindE None_cput // !bindfailf.
  + by rewrite (nocoerce_cget Hr2) // !bindfailf.
  + by rewrite None_cget // !bindfailf.
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
  rewrite (nth_error_rcons_some _ Hr) coerce_Some bindretf/=.
  by rewrite (nth_error_size_set_nth _ _ Hr) (nth_error_set_nth_rcons _ _ _ Hr).
- rewrite 2!MS_bindE (nocoerce_cget _ T1s')// bindfailf.
  by rewrite (nocoerce_cput _ _ T1s') // !bindfailf.
- by rewrite 2!MS_bindE None_cget// bindfailf None_cput // !bindfailf.
Qed.

(*
Definition crunret (A B : UU0) (m : M A) (s : B) :
  crun m -> crun (m >> Ret s) = Some s.
Proof. by rewrite /crun /= MS_bindE/=; case: (m [::]) => //- []. Qed.

Definition crunskip : crun skip = Some tt.
Proof. by []. Qed.

Definition crunnew (A : UU0) T (m : M A) (s : A -> coq_type T) :
  crun m -> crun (m >>= fun x => cnew (s x)).
Proof. by rewrite /crun /= MS_bindE; case: (m [::]) => // -[]. Qed.

Definition crunnewgetC (A : UU0) T1 T2 (m : M A) (r : A -> loc T1)
  (s : A -> coq_type T2) :
  crun (m >>= fun x => cget (r x)) ->
  crun (m >>= fun x => cnew (s x) >> cget (r x)).
Proof.
rewrite /crun /= !bindE /= /bindS !MS_mapE /= !fmapE /= !bindA /=.
case Hm: (m [::]) => [|[a b]] //.
rewrite !bindE /= !bindE /= /bindS MS_mapE /= fmapE /= bindA.
rewrite !bindE /= !bindE /= /cget.
case Hnth: nth_error => [[]|] //.
rewrite (nth_error_rcons_some _ Hnth).
by case Hcoe: coerce.
Qed.

Definition crungetput (A : UU0) T (m : M A) (r : A -> loc T) (s : A -> coq_type T) :
  crun (m >>= fun x => cget (r x)) ->
  crun (m >>= fun x => cput (r x) (s x)).
Proof.
rewrite /crun /= !bindE /= /bindS !MS_mapE /= !fmapE /= !bindA /=.
case Hm: (m _) => [|[a b]] //=.
rewrite !bindE /= !bindE /= /cget /cput /=.
case Hnth: nth_error => [[T' v]|] //.
case: (eqVneq T' T) => T'T; last first.
  by rewrite coerce_None// 1?eq_sym// coerce_None.
subst T'.
by rewrite !coerce_Some.
Qed.

Definition crunmskip (A : UU0) (m : M A) : crun (m >> skip) = crun m :> bool.
Proof.
rewrite /crun /= !bindE /= /bindS !MS_mapE /= !fmapE /= !bindA.
by case Hm: (m _) => [|[]].
Qed.
*)
HB.instance Definition _ := Monad.on M.
HB.instance Definition isMonadTypedStoreModel :=
  isMonadTypedStore.Build ml_type N locT_nat M cnewget cnewput cgetput cgetputskip
    cgetget cputget cputput cgetC cgetnewD cgetnewE cgetputC cputC
    cputgetC cputnewC.
(*
HB.instance Definition isMonadTypedStoreRunModel :=
  isMonadTypedStoreRun.Build ml_type N locT_nat M
    crunret crunskip crunnew crunnewgetC crungetput crunmskip.
*)
End mkbind.
End ModelTypedStore.

Section ModelelgotTypedStore.
Variable (M : elgotMonad) (N: monad) (MLU: ML_universe).
Definition DTS := (acto MLU N M).
HB.instance Definition _ := MonadTypedStore.on DTS.
HB.instance Definition _ := MonadElgot.on DTS.
HB.instance Definition _ := MonadElgotTypedStore.on DTS.
End ModelelgotTypedStore.
End ModelTypedStore.
