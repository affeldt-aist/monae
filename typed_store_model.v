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
Include MLTY.
Parameter ml_undef : ml_type.
Parameter undef : forall M, coq_type M ml_undef.
End MLTYdef.

Module ModelTypedStore (MLtypes : MLTYdef).
Module MTypedStore := MonadTypedStore (MLtypes).
Import MLtypes.
Import MTypedStore.

#[bypass_check(positivity)]
Inductive acto : UU0 -> UU0 :=
  mkActo : forall T : UU0,
      MS (seq (binding acto)) [the monad of option_monad] T -> acto T.
Local Notation M := acto.
Local Notation coq_type := (coq_type M).

Definition ofActo T (m : M T)
  : MS (seq (binding M)) [the monad of option_monad] T :=
  let: mkActo _ m' := m in m'.

Definition def := mkbind ml_undef (undef M).
Local Notation nth_error := List.nth_error.

Definition cnew T (v : coq_type T) : M (loc T) :=
  mkActo (fun st => let n := size st in Ret (mkloc T n, rcons st (mkbind T v))).

Definition coerce (T1 T2 : ml_type) (v : coq_type T1) : option (coq_type T2) :=
  match ml_type_eq_dec T1 T2 with
  | left H => Some (eq_rect _ _ v _ H)
  | right _ => None
  end.

Definition cget T (r : loc T) : M (coq_type T) :=
  mkActo (fun st =>
            if nth_error st (loc_id r) is Some (mkbind T' v) then
              if coerce T v is Some u then Ret (u, st) else fail
            else fail).

Definition cput T (r : loc T) (v : coq_type T) : M unit :=
  mkActo (fun st =>
            let n := loc_id r in
            if nth_error st n is Some (mkbind T' _) then
              if coerce T' v is Some u then
                Ret (tt, set_nth def st n (mkbind T' u))
              else fail
            else fail).

Definition cchk T (r : loc T) : M unit :=
  mkActo (fun st =>
            if nth_error st (loc_id r) is Some (mkbind T' u) then
              if coerce T u is Some _ then Ret (tt, st) else fail
            else fail).

Definition crun (A : UU0) (m : M A) : option A :=
  match ofActo m nil with
  | inl _ => None
  | inr (a, _) => Some a
  end.

Let ret : forall A, idfun A -> M A := fun A a => mkActo (Ret a).
Let bind A B (m : M A) (f : A -> M B) : M B :=
      mkActo (ofActo m >>= (fun a => ofActo (f a))).
Let left_neutral : BindLaws.left_neutral bind ret.
Proof. by move=> A B a f; rewrite /bind /ret bindretf; case: (f a). Qed.
Let right_neutral : BindLaws.right_neutral bind ret.
Proof. by move=> A a; rewrite /bind /ret  bindmret; case: a. Qed.
Let associative : BindLaws.associative bind.
Proof. by move=> A B C m f g; rewrite /bind /= bindA. Qed.

Let actm (A B : UU0) (f : A -> B) (m : M A) : M B :=
  mkActo (actm _ _ f (ofActo m)).

Definition isFunctorTS : isFunctor.axioms_ M.
exists actm.
- move=> A. apply boolp.funext => -[] {A} A m.
  by rewrite /actm functor_id.
- move=> A B C g h. apply boolp.funext => m.
  case: m h => {A} A m h /=.
  by rewrite /actm /= functor_o.
Defined.

Unset Universe Checking.
Canonical Structure FunctorTS : Functor M := Functor.Class isFunctorTS.
Canonical Structure functorTS : functor := Functor.Pack isFunctorTS.
Set Universe Checking.

Let ret_naturality : naturality [the functor of idfun] M ret.
Proof. by []. Qed.

Canonical Structure naturalityTSret := isNatural.Build _ _ _ ret_naturality.

Let ret' : [the functor of idfun] ~> [the functor of M] :=
   @Nattrans.Pack _ _ ret (Nattrans.Class naturalityTSret).

Unset Universe Checking.
Let join' : [the functor of M \o M] ~~> [the functor of M] :=
      fun _ m => bind m idfun.
Set Universe Checking.

Let actm_bind (a b c : UU0) (f : a -> b) m (g : c -> M a) :
  (actm f) (bind m g) = bind m (actm f \o g).
Proof.
congr mkActo.
case: m g => {}c m g /=.
rewrite bindE fmapE 2!bindA /=.
reflexivity.
Qed.

Lemma mkActoK A (m : MS _ _ A) : ofActo (mkActo m) = m.
Proof. done. Qed.

Unset Universe Checking.
Let join'_naturality : naturality _ _ join'.
Proof.
move=> a b h.
unfold join'.
rewrite /=. apply: boolp.funext => mm /=.
unfold hierarchy.actm, isFunctor.actm.
rewrite /= (actm_bind h mm idfun) /= /bind bindA.
apply f_equal.
apply f_equal.
apply boolp.funext => x /=.
rewrite /retS /= fmapE.
case: x h mm => {}a x h mm.
rewrite mkActoK /hierarchy.actm /= /actm /= fmapE !bindretf mkActoK.
reflexivity.
Qed.

Canonical Structure naturalityTS := isNatural.Build _ _ _ join'_naturality.

Let join : [the functor of M \o M] ~> [the functor of M] :=
   @Nattrans.Pack _ _ join' (Nattrans.Class naturalityTS).

Canonical Structure isMonadTS : isMonad.axioms_ M isFunctorTS.
exists ret' join bind.
- move=> A B f m.
  rewrite /join /= /join' /bind.
  apply f_equal.
  rewrite bindA.
  reflexivity.
- move=> A.
  apply boolp.funext => x /=.
  case: x => {}A m.
  reflexivity.
- move=> A.  
  apply boolp.funext => x /=.
  case: x => {}A m.
  rewrite /join' /bind /=.
  apply f_equal.
  rewrite fmapE /ret.
  rewrite bindA /=.
  under [fun _ => _]boolp.funext do rewrite bindretf mkActoK.
  rewrite bindmret.
  reflexivity.
- move=> A /=.
  rewrite /join' /bind.
  apply boolp.funext => x /=.
  apply f_equal.
  rewrite fmapE.
  rewrite !bindA.
  apply f_equal.
  apply boolp.funext => y /=.
  rewrite bindretf mkActoK.
  reflexivity.
Defined.

Canonical Structure MonadTS : Monad M := Monad.Class isMonadTS.
Canonical Structure monadTS : monad := Monad.Pack isMonadTS.
Set Universe Checking.

(* Doesn't work
HB.instance Definition xyz :=
  isMonad_ret_bind.Build M left_neutral right_neutral associative.
*)
(* Since we couldn't build the instance, redefine notations *)
(*Local Notation "m >>= f" := (bind m f).
Local Notation "m >> f" := (bind m (fun=> f)).*)

(* Make ml_type an eqType *)
Definition ml_type_eqb T1 T2 : bool := ml_type_eq_dec T1 T2.
Lemma ml_type_eqP : Equality.axiom ml_type_eqb.
Proof.
rewrite /ml_type_eqb => T1 T2.
by case: ml_type_eq_dec; constructor.
Qed.
Definition ml_type_eq_mixin := EqMixin ml_type_eqP.
Canonical ml_type_eqType := Eval hnf in EqType _ ml_type_eq_mixin.

(* Prove the laws *)
Let cnewget T (s : coq_type T) A (k : loc T -> coq_type T -> M A) :
  cnew s >>= (fun r => cget r >>= k r) = cnew s >>= (fun r => k r s).
Proof.
congr mkActo.
apply/boolp.funext => st /=.
rewrite bindE /= /bindS MS_mapE /= fmapE /= bindA /=.
rewrite [in RHS]bindE /= /bindS MS_mapE /= fmapE /= bindA /=.
rewrite bindE /= /bindS /= bindE /= bindE /= /bindS /= MS_mapE /= fmapE.
rewrite nth_error_rcons_size.
rewrite /coerce.
case: ml_type_eq_dec => // H.
by rewrite -eq_rect_eq.
Qed.

Let cnewgetC T T' (r : loc T) (s : coq_type T') A
           (k : loc T' -> coq_type T -> M A) :
  cchk r >> (cnew s >>= (fun r' => cget r >>= k r')) =
  cget r >>= (fun u => cnew s >>= fun r' => k r' u).
Proof.
congr mkActo.
apply/boolp.funext => st /=.
rewrite bindE /= /bindS MS_mapE /= fmapE /= bindA /=.
rewrite [in RHS]bindE /= /bindS MS_mapE /= fmapE /= bindA /=.
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

Let cnewput T (s t : coq_type T) A (k : loc T -> M A) :
  cnew s >>= (fun r => cput r t >> k r) = cnew t >>= k.
Proof.
congr mkActo.
apply/boolp.funext => st /=.
rewrite bindE /= /bindS MS_mapE /= fmapE /= bindA /=.
rewrite bindE /= bindE /= bindE /= /bindS /= MS_mapE /= fmapE bindA.
rewrite [in RHS]bindE /= /bindS MS_mapE /= fmapE /= bindA /=.
rewrite [in RHS]bindE /= [in RHS]bindE /=.
rewrite nth_error_rcons_size.
rewrite /coerce.
case: ml_type_eq_dec => // H.
by rewrite -eq_rect_eq bindE /= bindE /= set_nth_rcons.
Qed.

Let cnewputC T T' (r : loc T) (s : coq_type T) (s' : coq_type T') A
    (k : loc T' -> M A) :
  cchk r >> (cnew s' >>= fun r' => cput r s >> k r') =
  cput r s >> (cnew s' >>= k).
Proof.
congr mkActo.
apply/boolp.funext => st /=.
rewrite bindE /= /bindS MS_mapE /= fmapE /= bindA /=.
rewrite [in RHS]bindE /= /bindS MS_mapE /= fmapE /= bindA /=.
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
rewrite (nth_error_size_set_nth _ _ Hr).
by rewrite (nth_error_set_nth_rcons _ _ _ Hr).
Qed.

Let cnewchk T (s : coq_type T) (A : UU0) (k : loc T -> M A) :
  cnew s >>= (fun r => cchk r >> k r) = cnew s >>= k.
Proof.
congr mkActo.
apply/boolp.funext => st /=.
rewrite bindE /= /bindS MS_mapE /= fmapE /= bindA /=.
rewrite [in RHS]bindE /= /bindS MS_mapE /= fmapE /= bindA /=.
rewrite bindE /= /bindS /= bindE /= bindE /= /bindS /= MS_mapE /= fmapE.
rewrite nth_error_rcons_size.
rewrite /coerce.
by case: ml_type_eq_dec.
Qed.

Let cchknewC T1 T2 (r : loc T1) (s : coq_type T2) (A : UU0)
    (k : loc T2 -> M A) :
 cchk r >> (cnew s >>= fun r' => cchk r >> k r') = cchk r >> (cnew s >>= k).
Proof.
congr mkActo.
apply/boolp.funext => st /=.
rewrite bindE /= /bindS MS_mapE /= fmapE /= bindA /=.
rewrite [in RHS]bindE /= /bindS MS_mapE /= fmapE /= bindA /=.
case Hr: (nth_error st (loc_id r)) => [[T' u]|] //.
case Hc: (coerce T1 u) => [u'|] //.
rewrite bindE /= bindE /= bindE /= /bindS /= MS_mapE /= fmapE /= bindA.
rewrite bindE /= bindE /= bindE /= /bindS /= MS_mapE /= fmapE /= bindA.
rewrite (nth_error_rcons_some _ Hr) Hc.
do! rewrite bindE /=.
by rewrite /bindS /= MS_mapE /= fmapE bindA.
Qed.

Let cchkC T1 T2 (r1: loc T1) (r2: loc T2) :
  cchk r1 >> cchk r2 = cchk r2 >> cchk r1.
Proof.
congr mkActo.
apply/boolp.funext => st /=.
rewrite bindE /= /bindS MS_mapE /= fmapE /= bindA /=.
rewrite [in RHS]bindE /= /bindS MS_mapE /= fmapE /= bindA /=.
case Hr1 : (nth_error st (loc_id r1)) => [[T1' v1]|] /=; last first.
  rewrite bindfailf.
  case Hr2 : (nth_error st (loc_id r2)) => [[T2' v2]|] /=;
    last by rewrite bindfailf.
  case Hc: (coerce T2 v2) => [u|]; last by rewrite bindfailf.
  by rewrite bindE/= bindE/= Hr1.
case Hr2 : (nth_error st (loc_id r2)) => [[T2' v2]|] /=; last first.
  rewrite bindfailf.
  case Hc: (coerce T1 v1) => [u|]; last by rewrite bindfailf.
  by rewrite bindE/= bindE/= Hr2.
case Hc: (coerce T1 v1) => [u1|]; last first.
  rewrite bindfailf.
  case Hc2: (coerce T2 v2) => [u|]; last by rewrite bindfailf.
  by rewrite bindE/= bindE/= Hr1 Hc.
rewrite bindE /= bindE /= Hr2.
case Hc2: (coerce T2 v2) => [u2|]; last by rewrite !bindfailf.
do! rewrite bindE /=.
by rewrite Hr1 Hc.
Qed.

Let cchkdup T (r : loc T) : cchk r >> cchk r = cchk r.
Proof.
congr mkActo.
apply/boolp.funext => st /=.
rewrite bindE /= /bindS MS_mapE /= fmapE /= bindA /=.
case Hr1 : (nth_error st (loc_id r)) => [[T1' v1]|] //=.
case Hc: (coerce T v1) => [u1|] //.
by rewrite bindE /= bindE /= Hr1 Hc.
Qed.

Let cchkgetC T1 T2 (r1: loc T1) (r2: loc T2) (A: UU0) (k: coq_type T2 -> M A) :
  cchk r1 >> (cget r2 >>= k) = cget r2 >>= (fun s => cchk r1 >> k s).
Proof.
congr mkActo.
apply/boolp.funext => st /=.
rewrite bindE /= /bindS MS_mapE /= fmapE /= bindA /=.
rewrite [in RHS]bindE /= /bindS MS_mapE /= fmapE /= bindA /=.
case Hr1 : (nth_error st (loc_id r1)) => [[T1' v1]|] /=; last first.
  rewrite bindfailf.
  case Hr2 : (nth_error st (loc_id r2)) => [[T2' v2]|] /=;
    last by rewrite bindfailf.
  case Hc: (coerce T2 v2) => [u|]; last by rewrite bindfailf.
  by rewrite bindE/= bindE/= bindE/= /bindS /= MS_mapE /= fmapE Hr1 bindfailf.
case Hr2 : (nth_error st (loc_id r2)) => [[T2' v2]|] /=; last first.
  rewrite bindfailf.
  case Hc: (coerce T1 v1) => [u|]; last by rewrite bindfailf.
  by rewrite bindE/= bindE/= bindE/= /bindS /= MS_mapE /= fmapE Hr2 bindfailf.
case Hc: (coerce T1 v1) => [u1|]; last first.
  rewrite bindfailf.
  case Hc2: (coerce T2 v2) => [u|]; last by rewrite bindfailf.
  rewrite bindE/= bindE/= bindE/= /bindS /= MS_mapE /= fmapE Hr1 Hc.
  by rewrite bindfailf.
rewrite bindE /= /bindS /= bindE /= bindE /= /bindS /= MS_mapE /= fmapE.
rewrite Hr2.
case Hc2: (coerce T2 v2) => [u2|]; last by rewrite !bindfailf.
do! rewrite bindE /=.
by rewrite /bindS /= MS_mapE /= fmapE Hr1 Hc.
Qed.

Let cchkget T (r : loc T) (A: UU0) (k : coq_type T -> M A) :
  cchk r >> (cget r >>= k) = cget r >>= k.
Proof.
congr mkActo.
apply/boolp.funext => st /=.
rewrite bindE /= /bindS MS_mapE /= fmapE /= bindA /=.
rewrite [in RHS]bindE /= /bindS MS_mapE /= fmapE /= bindA /=.
case Hr: (nth_error st (loc_id r)) => [[T' u]|] //.
case Hc: (coerce T u) => [u'|] //.
do! rewrite bindE /=.
by rewrite /bindS /= MS_mapE /= fmapE Hr Hc.
Qed.

Let cgetchk T (r : loc T) (A: UU0) (k : coq_type T -> M A) :
  cget r >>= (fun s => cchk r >> k s) = cget r >>= k.
Proof.
congr mkActo.
apply/boolp.funext => st /=.
rewrite bindE /= /bindS MS_mapE /= fmapE /= bindA /=.
rewrite [in RHS]bindE /= /bindS MS_mapE /= fmapE /= bindA /=.
case Hr: (nth_error st (loc_id r)) => [[T' u]|] //.
case Hc: (coerce T u) => [u'|] //.
do! rewrite bindE /=.
by rewrite /bindS /= MS_mapE /= fmapE Hr Hc.
Qed.

Let cchkputC T1 T2 (r1 : loc T1) (r2 : loc T2) (s : coq_type T2) :
  cchk r1 >> cput r2 s = cput r2 s >> cchk r1.
Proof.
congr mkActo.
apply/boolp.funext => st /=.
rewrite bindE /= /bindS MS_mapE /= fmapE /= bindA /=.
rewrite [in RHS]bindE /= /bindS MS_mapE /= fmapE /= bindA /=.
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

Let cchkput T (r : loc T) (s : coq_type T) :
  cchk r >> cput r s = cput r s.
Proof.
congr mkActo.
apply/boolp.funext => st /=.
rewrite bindE /= /bindS MS_mapE /= fmapE /= bindA /=.
case Hr: (nth_error st (loc_id r)) => [[T' u]|] //.
rewrite /coerce.
case: ml_type_eq_dec => HT; last by case: ml_type_eq_dec => // /esym //.
subst T'.
case: ml_type_eq_dec => // HT.
rewrite -eq_rect_eq {HT}.
do! rewrite bindE /=.
rewrite Hr.
case: ml_type_eq_dec => // HT.
by rewrite -eq_rect_eq.
Qed.

Let cputchk T (r : loc T) (s : coq_type T) :
  cput r s >> cchk r = cput r s.
Proof.
congr mkActo.
apply/boolp.funext => st /=.
rewrite bindE /= /bindS MS_mapE /= fmapE /= bindA /=.
case Hr: (nth_error st (loc_id r)) => [[T' u]|] //.
rewrite /coerce.
case: ml_type_eq_dec => HT //.
subst T'.
rewrite -!eq_rect_eq.
do! rewrite bindE /=.
rewrite nth_error_set_nth.
by case: ml_type_eq_dec.
Qed.

Let cputput T (r : loc T) (s s' : coq_type T) :
    cput r s >> cput r s' = cput r s'.
Proof.
congr mkActo.
apply/boolp.funext => st.
case: r s s' => {}T n s s' /=.
rewrite bindE /= /bindS MS_mapE /= fmapE /= bindA /=.
case Hst : (nth_error st n) => [[T' v]|] /=; last by rewrite bindfailf.
rewrite {1 3}/coerce.
case: ml_type_eq_dec => H /=; last by rewrite bindfailf.
subst T'.
rewrite !bindretf /= nth_error_set_nth /coerce.
case: ml_type_eq_dec => // H.
rewrite -eq_rect_eq.
by rewrite set_set_nth eqxx.
Qed.

Let cputget T (r : loc T) (s : coq_type T) (A : UU0) (k : coq_type T -> M A) :
  cput r s >> (cget r >>= k) = cput r s >> k s.
Proof.
congr mkActo.
apply/boolp.funext => st /=.
case: r s k => {}T n s k /=.
rewrite bindE /= /bindS MS_mapE /= fmapE /= bindA /=.
rewrite [in RHS]bindE /= /bindS MS_mapE /= fmapE /= bindA /=.
case Hst : (nth_error st n) => [[T' v]|] /=; last by rewrite bindfailf.
rewrite {1 3}/coerce.
case: ml_type_eq_dec => H /=; last by rewrite bindfailf.
subst T'.
rewrite !bindretf /=.
rewrite bindE /= /bindS MS_mapE /= fmapE /= bindA /=.
rewrite nth_error_set_nth.
rewrite /coerce.
case: ml_type_eq_dec => H /=; last by rewrite bindfailf.
by rewrite -eq_rect_eq !bindretf.
Qed.

Let cgetputchk T (r : loc T) : cget r >>= cput r = cchk r.
Proof.
congr mkActo.
apply/boolp.funext => st /=.
rewrite bindE /= /bindS MS_mapE /= fmapE /= bindA /=.
case Hr: (nth_error _ _) => [[T1 u]|]; last by rewrite bindfailf.
rewrite /coerce.
case: (ml_type_eq_dec T1 T) => H //.
subst T1.
rewrite bindE /= bindE /= Hr.
case: (ml_type_eq_dec T T) => H //.
by rewrite -eq_rect_eq nth_error_set_nth_id.
Qed.

Let cgetget T (r : loc T) (A : UU0) (k : coq_type T -> coq_type T -> M A) :
  cget r >>= (fun s => cget r >>= k s) = cget r >>= fun s => k s s.
Proof.
congr mkActo.
apply/boolp.funext => st /=.
rewrite bindE /= /bindS MS_mapE /= fmapE /= bindA /=.
rewrite [in RHS]bindE /= /bindS MS_mapE /= fmapE /= bindA /=.
case Hr: (nth_error _ _) => [[T1 u]|]; last by rewrite bindfailf.
rewrite /coerce.
case: (ml_type_eq_dec T1 T) => H //.
subst T1.
rewrite bindE /= bindE /=.
rewrite bindE /= /bindS MS_mapE /= fmapE /= bindA /=.
rewrite Hr.
case: (ml_type_eq_dec T T) => H //.
by rewrite -eq_rect_eq.
Qed.

Let cgetC T1 T2 (r1 : loc T1) (r2 : loc T2) (A : UU0)
           (k : coq_type T1 -> coq_type T2 -> M A) :
  cget r1 >>= (fun u => cget r2 >>= (fun v => k u v)) =
  cget r2 >>= (fun v => cget r1 >>= (fun u => k u v)).
Proof.
congr mkActo.
apply/boolp.funext => st /=.
rewrite bindE /= /bindS MS_mapE /= fmapE /= bindA /=.
rewrite [in RHS]bindE /= /bindS MS_mapE /= fmapE /= bindA /=.
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

Let cputC T1 T2 (r1 : loc T1) (r2 : loc T2) (s1 : coq_type T1)
    (s2 : coq_type T2) (A : UU0) :
  loc_id r1 != loc_id r2 \/ JMeq s1 s2 ->
  cput r1 s1 >> cput r2 s2 = cput r2 s2 >> cput r1 s1.
Proof.
move=> H.
congr mkActo.
apply/boolp.funext => st /=.
rewrite bindE /= /bindS MS_mapE /= fmapE /= bindA /=.
rewrite [in RHS]bindE /= /bindS MS_mapE /= fmapE /= bindA /=.
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
congr mkActo.
apply/boolp.funext => st /=.
rewrite !bindA.
rewrite bindE /= /bindS MS_mapE /= fmapE /= bindA /=.
rewrite [in RHS]bindE /= /bindS MS_mapE /= fmapE /= bindA /=.
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

Let crunret (A B : UU0) (m : M A) (s : B) :
  crun m -> crun (m >> ret s) = Some s.
Proof.
case: m => T /= m.
rewrite /crun /= bindE /= /bindS MS_mapE /= fmapE /= bindA /=.
by case Hm: (m [::]).
Qed.

Let crunskip : crun skip = Some tt.
Proof. by []. Qed.

Let crunnew (A : UU0) T (m : M A) (s : coq_type T) :
  crun m -> crun (m >> cnew s).
Proof.
case: m => U /= m.
rewrite /crun /= bindE /= /bindS MS_mapE /= fmapE /= bindA /=.
by case Hm: (m [::]).
Qed.

Unset Universe Checking.
Definition isMonadTypedStoreModel :
  isMonadTypedStore.axioms_ M isFunctorTS isMonadTS.
Proof.
exists cnew cget cput cchk crun.
- exact cnewget.
- exact cnewgetC.
- exact cnewput.
- exact cnewputC.
- exact cputput.
- exact cputget.
- exact cgetputchk.
- exact cgetget.
- exact cgetC.
- exact cputC.
- exact cputgetC.
- exact cnewchk.
- exact cchknewC.
- exact cchkgetC.
- exact cchkget.
- exact cgetchk.
- exact cchkputC.
- exact cchkput.
- exact cputchk.
- exact cchkC.
- exact cchkdup.
- exact crunret.
- exact crunskip.
- exact crunnew.
Defined.
Set Universe Checking.
End ModelTypedStore.
