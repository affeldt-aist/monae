Require Import JMeq.
From Stdlib Require Import Recdef Wf_nat.
From mathcomp Require Import all_ssreflect ssralg ssrint.
From mathcomp Require boolp.
Require Import preamble.
From HB Require Import structures.
Require Import hierarchy monad_lib fail_lib state_lib.
Require Import monad_transformer.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.

Module ModelUnion.
Section modelunion.

Local Notation I := nat.
Implicit Types (i j : I) (A : UU0).

Definition is_forest (f : I -> I) := forall x, f x <=  x.

Definition forest := {f : I -> I | is_forest f}.

Function find_rec (f : forest) (i : I) {wf lt i} :=
  let y := sval f i in
  if y == i then i else find_rec f y.
Proof.
  - by move=> f x H; apply/ltP; rewrite ltn_neqAle H (proj2_sig f).
  - exact: lt_wf.
Defined.

Definition equiv (f1 f2 : forest) := find_rec f1 = find_rec f2. 

Definition is_equiv A (g : forest -> A * forest ) := 
  forall f1 f2,
    equiv f1 f2 -> (g f1).1 = (g f2).1 /\ equiv (g f1).2 (g f2).2.

Definition acto : UU0 -> UU0 := fun A =>
   {g : forest -> A * forest | is_equiv g}.

Local Notation M := acto. 

Lemma ret_correct A (a : A): is_equiv (fun f => (a, f)).
Proof. by move=> f1 f2 H; split. Qed.

Let ret := fun A (a : A) => exist _ _ (ret_correct a). 

Lemma bind_correct (A B : UU0) (m : M A) (t : A -> M B) :
is_equiv (fun f =>
    let: (a, f') := (proj1_sig m) f in
    (proj1_sig (t a)) f').
Proof.
  move=>f1 f2 Heq.
  case: m => m hm /=.
  move: {hm} (hm _ _ Heq).
  case: (m f1) => [a1 f1'].
  case: (m f2) => [a2 f2'] /= [] <- Heq'.
  case: (t a1) => tm htm /=.
  exact: (htm _ _ Heq').
Defined.

Let bind (A B : UU0) (m : M A) (t : A -> M B) : M B :=
  exist _ _  (bind_correct m t).

Let left_neutral : BindLaws.left_neutral bind ret.
Proof.
  move => A B a t.
  move H: (t a) => [f' Hf'] /=.
  by apply boolp.eq_exist, boolp.funext => f/=; rewrite H.
Qed.

Let right_neutral : BindLaws.right_neutral bind ret.
Proof.
  move=>A t.
  case: t => [f' Hf'] /=.
  apply boolp.eq_exist, boolp.funext => f/=.
  by case: (f' f) => [a f'0].
Qed.

Let associative : BindLaws.associative bind.
Proof.
  move=> A B C a b c.
  apply boolp.eq_exist, boolp.funext => f.
  case a => fa Hfa /=.
  by case (fa f) => [a0 f'].
Qed.

HB.instance Definition _ := 
  isMonad_ret_bind.Build acto left_neutral right_neutral associative.

Definition find_correct i : is_equiv (fun f => (find_rec f i, f)).
Proof. by move=> f1 f2 H; rewrite H. Qed.

Definition find (i : I) : M I :=
  exist _ _ (find_correct i).

Lemma find_step f i : find_rec f i= find_rec f (proj1_sig f i).
Proof.
  functional induction (find_rec f i); last by [].
  move/eqP in e.
  by rewrite e find_rec_equation e eq_refl.
Qed.

Lemma find_return_root f i : sval f (find_rec f i) = find_rec f i.
Proof.
  functional induction (find_rec f i).
  by move/eqP in e.
  exact IHn.
Qed.

Lemma find_root i f : find_rec f (find_rec f i) = find_rec f i.
Proof.
  by rewrite {1}find_rec_equation find_return_root eq_refl.
Qed.

Definition add_edge (f : forest) (i j : I) := 
  fun k => if k == i then j else sval f k.

Definition union_func (f : forest) (i : I) (j : I) : I -> I :=
  let rep_i := find_rec f i in
  let rep_j := find_rec f j in
  if rep_i == rep_j then sval f
  else if rep_i < rep_j then
    add_edge f rep_j rep_i
  else
    add_edge f rep_i rep_j.

Lemma is_forest_add_edge (f : forest) (i j : I):
  j < i -> is_forest (add_edge f i j).
Proof.
  move=> Hinf k.
  rewrite /add_edge.
  case: ifPn => [ /eqP -> | _ ].
  - exact: ltnW.
  - exact: (proj2_sig f).
Qed.

Lemma is_forest_union f i i' : is_forest (union_func f i i').
Proof.
  rewrite /union_func.
  case: ifPn => Heq; first exact: (proj2_sig f).
  case: ifPn.
  - exact: is_forest_add_edge.
  - rewrite ltn_neqAle Heq /= -ltnNge.
    exact: is_forest_add_edge.
Qed.

Definition union_forest f i i' := exist _ _ (is_forest_union f i i'). 

Lemma find_changed_union i i' j f :
  find_rec f j = find_rec f i -> 
  find_rec f i' < find_rec f i ->
  find_rec (union_forest f i' i) j = find_rec f i'.
Proof.
  move=> Hfind Hlti.
  rewrite /union_forest.
  move: (is_forest_union f i' i).
  rewrite /union_func /add_edge (ltn_eqF Hlti) Hlti => /= Hf. 
  rewrite -/(add_edge _ _ _).
  set new_f := exist is_forest _ Hf.
  functional induction (find_rec new_f j); [move: e | move: y0 IHn]; 
    rewrite /= -/(add_edge _ _ _).
  - case: ifPn => [ _ /eqP <- // | ].
    rewrite -Hfind find_rec_equation => /[swap] ->.
    by rewrite eqxx.
  - case: ifPn => //.
    case: ifPn => [_ |] _ _ _.
      rewrite find_rec_equation /= /add_edge find_return_root.
      by rewrite if_same eqxx.
    by rewrite -find_step => ->.
Qed.

Lemma find_unchanged_union i i' j f:
  find_rec f j <> find_rec f i -> 
  find_rec f i' < find_rec f i ->
  find_rec (union_forest f i' i) j = find_rec f j.
Proof.
move=> Hfind Hlti.
  rewrite /union_forest.
  move: (is_forest_union f i' i).
  rewrite /union_func /add_edge (ltn_eqF Hlti) Hlti => /= Hf. 
  rewrite -/(add_edge _ _ _).
  set new_f := exist is_forest _ Hf.
  functional induction (find_rec new_f j); [move: e | move: y0 IHn]; 
    rewrite /= -/(add_edge _ _ _).
  - case: ifPn => [ /eqP -> | _ ].
      by rewrite find_root.
    by rewrite find_rec_equation => ->.
  - move: Hfind. case: ifPn => //.
    case: ifPn => [ /eqP -> | _ _].
      by rewrite find_root.
    rewrite -find_step => Hfind _.
    exact.  
Qed.

Lemma exist_surjective f Hf: f = (exist is_forest (sval f) Hf).
Proof.
  case: f Hf => x p Hf.
  exact: boolp.eq_exist.
Qed.

Lemma union_func_sym i i' f: union_func f i i' = union_func f i' i.
Proof.
  rewrite /union_func eq_sym.
  case: ifPn => // i'i.
  case: ifPn => Hlt; by rewrite ltn_neqAle i'i leqNgt Hlt.
Qed.

Lemma union_forest_sym i i' f :
  union_forest f i i' = union_forest f i' i.
Proof. by apply /boolp.eq_exist /union_func_sym. Qed.

Lemma is_forest_union_equiv_aux i i' f1 f2 j:
  find_rec f1 = find_rec f2 ->  
  find_rec f1 i < find_rec f1 i' ->
  find_rec (union_forest f1 i i') j = find_rec (union_forest f2 i i') j.
Proof.
  move=> Hequiv Hlti.
  case Hji: (find_rec f1 j == find_rec f1 i'); move/eqP in Hji.
  - rewrite (find_changed_union  Hji Hlti).
    rewrite Hequiv in Hji, Hlti.
    by rewrite (find_changed_union  Hji Hlti) Hequiv.
  - rewrite (find_unchanged_union Hji Hlti).
    rewrite Hequiv in Hji, Hlti.
    by rewrite (find_unchanged_union  Hji Hlti) Hequiv.
Qed.

Lemma is_forest_union_equiv i i' : is_equiv (fun f => (tt, (union_forest f i i'))).
Proof.
  move =>f1 f2 Hequiv => /=.
  split=>//.
  rewrite /equiv in Hequiv.
  apply boolp.funext => j /=.
  case Heq: (find_rec f1 i == find_rec f1 i').
  - rewrite /equiv /union_forest.
    move: (is_forest_union f1 i i') (is_forest_union f2 i i').
    rewrite /union_func -Hequiv Heq.
    by move=> Hf1 Hf2; do 2 rewrite <- exist_surjective; rewrite Hequiv.
  - case Hlti:  (find_rec f1 i < find_rec f1 i').
    + by apply is_forest_union_equiv_aux.
    +rewrite ltn_neqAle Heq leqNgt /= in Hlti.
    move /negPn in Hlti. 
    rewrite !(union_forest_sym i i').
    by apply is_forest_union_equiv_aux.
Qed.

Definition union (i:I) (i' : I) : M unit :=
exist _ (fun f => (tt, union_forest f i i')) (is_forest_union_equiv i i').

Definition Bis A (P Q : M A) :=
  forall f, 
    (sval P f).1 = (sval Q f).1 /\ equiv (sval P f).2 (sval Q f).2 .

Local Notation "a '≈' b" := (Bis a b).

Lemma refl A (d : M A) : d ≈ d. 
Proof.
  by move=> f;case (sval d f) => [a f'].
Qed.

Lemma sym A (d1 d2 : M A) : d1 ≈ d2 -> d2 ≈ d1.
Proof.
  move=> Hbisim f.
  case: (Hbisim f) =>[H0 H1].
  revert H1.
  by rewrite -H0 /equiv => <-.
Qed.

Lemma trans A (d1 d2 d3 : M A) : d1 ≈ d2 -> d2 ≈ d3 -> d1 ≈ d3.
Proof.
  move => Hb1 Hb2 f.
  case: (Hb1 f) => [Hb1' Hb1''].
  case: (Hb2 f) => [Hb2' Hb2''].
  rewrite /equiv in Hb1'' Hb2'' *.
  by rewrite Hb1' Hb1''.
Qed.

Lemma bindl A B (t : A -> M B) (d1 d2 : M A) : d1 ≈ d2 -> (d1 >>= t) ≈ (d2 >>= t).
Proof.
  move=> Heq f /=.
  case: (Heq f ) => [Heq' Heq''].
  move: Heq' Heq''.
  case (sval d1 f)=>[a f0].
  case (sval d2 f)=>[a1 f1]/=.
  move=> -> H.
  case (t a1) => t_func Ht /=.
  by apply (Ht f0 f1).
Qed.

Lemma bindr A B (f g : A -> M B) d :
  (forall a, f a ≈ g a) -> (d >>= f) ≈ (d >>= g).
Proof.
  by move=> Heq f'/= ; case (sval d f').
Qed.

HB.instance Definition _ := @hasPreorder.Build M Bis
  (@refl) (@trans) (@bindl) (@bindr).

HB.instance Definition _ := @hasEquivalence.Build M (@sym).

Lemma eq_is_bisim : forall A (P Q : M A) , P = Q -> P ≈ Q.
Proof.
  by move=> A P Q Heq; rewrite /Bis Heq.
Qed.

Let findfind (A : UU0) i (k : I -> I -> M A):
    find i >>= (fun r => find i >>= (fun r' => k r r')) ≈ find i >>= (fun r => k r r).
Proof. by apply eq_is_bisim, boolp.eq_exist, boolp.funext => f/=. Qed.

Let unionfind i i': union i i'>> find i ≈ union i i' >> find i'.
Proof.
  apply eq_is_bisim, boolp.eq_exist, boolp.funext => f.
  apply pair_equal_spec; split=>//.
  rewrite /union_forest.
  case Heq: (find_rec f i == find_rec f i').
  -move: (is_forest_union f i i').
  rewrite /union_func Heq => Hf.
  rewrite <- exist_surjective.
  by move/eqP in Heq.
  case Hlti:  (find_rec f i < find_rec f i').
  - by move/eqP in Heq;rewrite (find_unchanged_union  Heq Hlti)
          (find_changed_union erefl Hlti).
  - rewrite ltn_neqAle Heq leqNgt /= in Hlti.
    move /negPn in Hlti. 
    move /eqP /nesym in Heq.
    fold (union_forest f i i').
    by rewrite (union_forest_sym i i')
          (find_unchanged_union Heq Hlti)
          (find_changed_union erefl Hlti).
Qed.

Let findunion i i': find i' >>= union i ≈ union i i'.
Proof.
  apply eq_is_bisim, boolp.eq_exist ,boolp.funext => f/=.
  apply pair_equal_spec; split => //.
  apply boolp.eq_exist.
  by rewrite /union_func find_root.
Qed.

Lemma union_forest_id f i i':
(find_rec f i == find_rec f i') = true ->
(union_forest f i i') = f.
Proof.
  move=> Heq.
  rewrite /union_forest.
  move: (is_forest_union f i i').
  rewrite /union_func Heq => Hf.
  by rewrite <- exist_surjective.
Qed.

Let union_sym i i': union i i' ≈ union i' i.
Proof.
  apply eq_is_bisim, boolp.eq_exist, boolp.funext => f/=.
  rewrite pair_equal_spec;split=>//.
  apply: union_forest_sym.
Qed.

Lemma findunionfind_lt f i i' u :
find_rec f i < find_rec f i' -> 
find_rec (union_forest f i i') (find_rec f u) = find_rec (union_forest f i i') u.
Proof.
  move=> Hlti.
  rewrite -(find_root u (union_forest f i i')).
  case H: (find_rec f u == find_rec f i'); move/eqP in H.
  - rewrite (find_changed_union H Hlti).
    have Hi : find_rec f (find_rec f i) <> find_rec f i'
      by rewrite find_root;move/ltn_eqF /eqP in Hlti.
    rewrite -find_root in H. 
    by rewrite  (find_changed_union H Hlti) 
                (find_unchanged_union Hi Hlti) find_root.
  - by rewrite (find_unchanged_union H Hlti).
Qed.

Let findunionfind i i' u:
  find u >>= (fun v => union i i' >> find v) ≈ union i i' >> find u.
Proof.
  rewrite /union. 
  apply eq_is_bisim, boolp.eq_exist, boolp.funext => f/=.
  case Heq: (find_rec f i == find_rec f i')=>/=.
  by rewrite (union_forest_id Heq) find_root.
  case Hlti: (find_rec f i < find_rec f i').
  by rewrite findunionfind_lt .
  by rewrite ltn_neqAle Heq leqNgt /= in Hlti;
     move /negPn in Hlti;
     rewrite union_forest_sym (findunionfind_lt u Hlti).
Qed.

Let union_refl i : union i i ≈ skip.
Proof.
  apply eq_is_bisim, boolp.eq_exist, boolp.funext => f.
  by rewrite (union_forest_id (eqxx (find_rec f i))).
Qed.    

Let findC (A : UU0) i i' (k : I -> I -> M A):
    find i >>= (fun u => find i' >>= (fun v => k u v)) ≈
    find i' >>= (fun v => find i >>= (fun u => k u v)).
Proof. by apply eq_is_bisim, boolp.eq_exist, boolp.funext. Qed.  

Lemma find_unchanged_unchanged_union f i i' u v j :
find_rec f i > find_rec f i' ->
find_rec f j <> find_rec f i ->
find_rec (union_forest f i i') u > find_rec (union_forest f i i') v ->
find_rec f j <> find_rec (union_forest f i i') u ->
find_rec (union_forest (union_forest f i i') u v) j = find_rec f j.
Proof.
  move=> Hlti Hji Hltu Hju.
  rewrite (union_forest_sym i i') (union_forest_sym u v) find_unchanged_union.
    - by apply (find_unchanged_union  Hji Hlti).
    - by rewrite(find_unchanged_union  Hji Hlti) (union_forest_sym i' i) .
    - by rewrite (union_forest_sym i' i).
Qed.

Lemma find_unchanged_changed_union f i i' u v j :
find_rec f i > find_rec f i' ->
find_rec f j <> find_rec f i ->
find_rec (union_forest f i i') u > find_rec (union_forest f i i') v ->
find_rec f j = find_rec (union_forest f i i') u ->
find_rec (union_forest f i i') v <> find_rec f i ->
find_rec (union_forest (union_forest f i i') u v) j = find_rec (union_forest f i i') v.
Proof.
  move=> Hlti Hji Hltu Hju Heqvi.
  rewrite (union_forest_sym i i') (union_forest_sym u v) find_changed_union. 
  + by [].
  + by rewrite (find_unchanged_union Hji Hlti) Hju (union_forest_sym i i').
  + by rewrite (union_forest_sym i' i).
Qed.

Lemma find_changed_unchanged_union: 
forall f i i' u v j,
find_rec f i > find_rec f i' ->
find_rec f j = find_rec f i ->
find_rec (union_forest f i i') u > find_rec (union_forest f i i') v ->
find_rec f i' <> find_rec (union_forest f i i') u ->
find_rec (union_forest (union_forest f i i') u v) j = find_rec f i'.
Proof.
  move=> f i i' u v j Hlti Hji Hltu Hju.
  rewrite (union_forest_sym i i') (union_forest_sym u v) find_unchanged_union. 
  + by rewrite find_changed_union. 
  + by rewrite (find_changed_union Hji Hlti) (union_forest_sym i' i).
  + by rewrite (union_forest_sym i' i).
Qed.

Lemma union_dec : forall f i i' j,
find_rec (union_forest f i' i) j <= find_rec f j .
Proof.
  move=> f i i' j.
  case Heqi: (find_rec f i' == find_rec f i).
  - rewrite /union_forest.
  move: (is_forest_union f i' i).
  rewrite /union_func Heqi => Hf.
  by rewrite <- exist_surjective.
  case Hlti : (find_rec f i' < find_rec f i).
  - case Hji: (find_rec f j == find_rec f i); move/eqP in Hji.
    +rewrite (find_changed_union Hji Hlti).
    rewrite <- Hji in Hlti.
    +by apply ltnW.
    by rewrite (find_unchanged_union Hji Hlti).
  - rewrite ltn_neqAle Heqi leqNgt /= in Hlti.
    move /negPn in Hlti. 
    case Hji: (find_rec f j == find_rec f i'); move/eqP in Hji.
    + rewrite (union_forest_sym) (find_changed_union Hji Hlti).
      rewrite <- Hji in Hlti.
    + by apply ltnW.
    by rewrite union_forest_sym (find_unchanged_union Hji Hlti).
Qed.

Lemma find_eq_union f i i' u v :
find_rec f i = find_rec f i' ->
find_rec f u < find_rec f v ->
find_rec (union_forest f u v) i == find_rec (union_forest f u v) i'.
Proof.
  move=> Heqi Hltu.
  case Heqv: (find_rec f i == find_rec f v); move/eqP in Heqv.
  - rewrite (find_changed_union Heqv Hltu).
    rewrite Heqi in Heqv.
    by rewrite find_changed_union .
  - rewrite (find_unchanged_union Heqv Hltu).
    rewrite Heqi in Heqv.
    rewrite (find_unchanged_union Heqv Hltu).
    by move/eqP in Heqi.
Qed.

Lemma find_changed_changed_union_rev f i i' u v j :
find_rec f i > find_rec f i' ->
find_rec f j = find_rec f u ->
find_rec f v = find_rec f i  ->
find_rec (union_forest f i i') v < find_rec (union_forest f i i') u ->
find_rec (union_forest (union_forest f i i') u v) j = find_rec f i'.
Proof.
  move=> Hlti Hju Heqvi Hltu.
  rewrite (union_forest_sym u v) find_changed_union.
  by rewrite union_forest_sym (find_changed_union Heqvi Hlti).
  by apply /eqP; rewrite union_forest_sym find_eq_union.
  exact Hltu.
Qed.

Lemma union_diff f i i' j :
find_rec f i < find_rec f i' ->
find_rec (union_forest f i' i) j < find_rec f j ->
find_rec f j = find_rec f i'.
Proof.
  move=> Hlti Hlt.
  case H: (find_rec f j == find_rec f i'); move /eqP in H.
  - by [].
  - by rewrite (union_forest_sym i' i) (find_unchanged_union H Hlti) ltnn in Hlt.
Qed.

Lemma lt_union f i i' u v :
find_rec f i' < find_rec f i ->
find_rec (union_forest f i i') u > find_rec (union_forest f i i') v ->
find_rec f i' = find_rec (union_forest f i i') u ->
find_rec f v < find_rec f i.
Proof.
  move=> Hlti Hltu Hju.
  case H: (find_rec (union_forest f i' i) v == find_rec f v); move/eqP in H.
  - rewrite Hju in Hlti.
    rewrite (union_forest_sym i i') H  (union_forest_sym i' i) in Hltu.
    apply (ltn_trans Hltu Hlti).
  - move/eqP in H. have H' := union_dec f i' i v.
    have: find_rec (union_forest f i i') v < find_rec f v
    by rewrite ltn_neqAle Bool.andb_lazy_alt union_forest_sym H union_forest_sym.
    move=> Hlt'. have H0 := union_diff Hlti Hlt'.
    have H1 := (find_changed_union H0 Hlti).
    rewrite union_forest_sym in H1.
    by rewrite <-Hju, H1, ltnn in Hltu.
Qed.

Lemma find_changed_changed_union f i i' u v j:
find_rec f i > find_rec f i' ->
find_rec f j = find_rec f i ->
find_rec (union_forest f i i') u > find_rec (union_forest f i i') v ->
find_rec f i' = find_rec (union_forest f i i') u ->
find_rec (union_forest (union_forest f i i') u v) j = find_rec f v.
Proof.
  move=> Hlti Hji Hltu Hju.
  have: find_rec f v < find_rec f i by apply (lt_union Hlti Hltu Hju).
  move=>/ltn_eqF /eqP Hvi;
  rewrite (union_forest_sym i i') (union_forest_sym u v) find_changed_union. 
  + by rewrite find_unchanged_union . 
  + by rewrite (find_changed_union Hji Hlti) Hju (union_forest_sym i' i).
  + by rewrite (union_forest_sym i' i).
Qed.

Lemma union_eq : forall f i i' u v,
find_rec f i == find_rec f i' ->
union_forest (union_forest f u v) i i' = union_forest f u v.
Proof.
  move=> f i i' u v /eqP Heqi.
  apply boolp.eq_exist.
  rewrite {1}/union_func /union_forest.
  case Hequ: (find_rec f u == find_rec f v).
  - move: (is_forest_union f u v).
  rewrite /union_func Hequ => Hf.
  by rewrite -exist_surjective Heqi eq_refl.
  case Hltu: (find_rec f u < find_rec f v)=> /=.
  -  by rewrite (find_eq_union Heqi Hltu).
  - rewrite ltn_neqAle Hequ leqNgt /= in Hltu.
    move /negPn in Hltu. 
    fold (union_forest f u v).
    by rewrite (union_forest_sym u v) (find_eq_union Heqi Hltu).
Qed.

Lemma find_eq_unionC i i' u v f :
find_rec f u = find_rec f i->
find_rec f v = find_rec f i'->
(union_forest f u v) = (union_forest f i i').
Proof.
  by move=> Heq Heq';
  apply boolp.eq_exist;
  rewrite /union_func Heq Heq'.
Qed.

Lemma union_case f i i' u v :
find_rec f i' < find_rec f i ->
find_rec f v <= find_rec f u ->
(find_rec (union_forest f i i') u  = find_rec (union_forest f i i') v) -> 
find_rec f u = find_rec f v \/ (find_rec f u = find_rec f i /\ find_rec f v = find_rec f i').
Proof.
  move=> Hlti Hltu Heq.
  case Hequv: (find_rec f u == find_rec f v); move/eqP in Hequv.
  - by rewrite Hequv; apply or_introl.
  - apply or_intror.
    case H: (find_rec f u == find_rec f i); move/eqP in H.
    +have Hv : find_rec f v <> find_rec f i
        by rewrite H in Hequv;move/nesym in Hequv.
      by rewrite union_forest_sym (find_changed_union H Hlti) (find_unchanged_union Hv Hlti) in Heq. 
    + rewrite union_forest_sym (find_unchanged_union H Hlti) in Heq. 
      case Hvi : (find_rec f v == find_rec f i); move/eqP in Hvi.
      * rewrite (find_changed_union Hvi Hlti) in Heq.
        rewrite Heq Hvi in Hltu. 
        by apply (leq_ltn_trans Hltu) in Hlti; rewrite ltnn in Hlti.
      * by rewrite (find_unchanged_union Hvi Hlti) in Heq.
Qed.

Lemma find_union_eq f i i' u v :
find_rec f i' < find_rec f i ->
find_rec f u = find_rec f v ->
find_rec (union_forest f i i') u = find_rec (union_forest f i i') v.
Proof.
  move=> Hlti Hfind.
  case Heq: (find_rec f u == find_rec f i);move/eqP in Heq.
  - rewrite union_forest_sym (find_changed_union Heq Hlti).
    rewrite Hfind in Heq.
    by rewrite (find_changed_union Heq Hlti).
  - rewrite union_forest_sym (find_unchanged_union Heq Hlti).
    rewrite Hfind in Heq.
    by rewrite (find_unchanged_union Heq Hlti).
Qed.

Lemma inf_after_union i i' u v f :
find_rec f i < find_rec f i' ->
find_rec (union_forest f i i') u < find_rec (union_forest f i i') v ->
find_rec f u < find_rec f v \/ 
(find_rec f u > find_rec f v /\ find_rec f u = find_rec f i' /\find_rec f v > find_rec f i).
Proof.
  move=>  Hlti Hltunion.
  case Hlt: (find_rec f u < find_rec f v).
  by apply or_introl.
  apply or_intror.
  have Huv : ((find_rec f u == find_rec f v) = false).
    apply /eqP => Hcontr. 
    apply (find_union_eq Hlti) in Hcontr.
    move /ltn_eqF /eqP in Hltunion. 
    by rewrite union_forest_sym in Hltunion.
  have Hlt' := Hlt.
  rewrite ltn_neqAle Huv leqNgt /= in Hlt'.
    move /negPn in Hlt'. 
  have  Hui': find_rec f u = find_rec f i'.
  apply /eqP /contraT => /eqP Hcontr. 
    rewrite (find_unchanged_union Hcontr Hlti) in Hltunion.
    move/ltnW in Hltunion. 
    have H' := (leq_trans Hltunion (union_dec f i' i v)).
    move: H'. rewrite leq_eqVlt. rewrite Hlt => H.
    rewrite orbF in H.
    move/eqP in H; move/eqP in Huv.
    exfalso. 
    by apply Huv. 
  have Hvi' : find_rec f v == find_rec f i' = false by rewrite -Hui'; apply /ltn_eqF.
  by move/eqP in Hvi'; 
  rewrite (find_changed_union Hui' Hlti) (find_unchanged_union Hvi' Hlti) in Hltunion.
Qed.

Lemma union_lt_exchange f i i' u v :
find_rec f i < find_rec f i' ->
find_rec f v < find_rec f u ->
find_rec f i' <> find_rec f u \/ find_rec f i < find_rec f v ->
find_rec (union_forest f u v) i < find_rec (union_forest f u v) i'.
Proof.
  move=> Hlti Hltuf H.
  case: H => H'.
  - rewrite union_forest_sym (find_unchanged_union H' Hltuf).
    apply: leq_ltn_trans.
    + apply union_dec.
    + by [].
  - have Hlt := (ltn_trans H' Hltuf).
  move /ltn_eqF /eqP in Hlt.
  rewrite union_forest_sym (find_unchanged_union Hlt Hltuf).
  case Hequi': (find_rec f i' == find_rec f u);move/eqP in Hequi'.
  - by rewrite (find_changed_union ).
  - by rewrite find_unchanged_union.
Qed.

Lemma union_lt_exchange2 f i i' u v :
find_rec f i < find_rec f i' ->
find_rec f v < find_rec f u ->
find_rec f i' = find_rec f u ->
find_rec f i > find_rec f v -> 
find_rec (union_forest f u v) i > find_rec (union_forest f u v) i'.
Proof. 
  move=>  Hlti Hltuf Heqi'u Hlt.
  rewrite union_forest_sym (find_changed_union Heqi'u Hltuf).
  have Hdiff : find_rec f i <> find_rec f u.
    rewrite -Heqi'u => H. 
    move /ltn_eqF in Hlti. 
    rewrite H eq_refl in Hlti.
    by inversion Hlti.
  by rewrite find_unchanged_union.
Qed.

Lemma case_find_union f i i' u :
find_rec f i < find_rec f i' ->
find_rec f i = find_rec (union_forest f i' i) u ->
find_rec f i = find_rec f u \/ find_rec f i' = find_rec f u.
Proof.
  move=> Hlti Hfind.
  case Heq : (find_rec f i == find_rec f u); move/eqP in Heq.
  - by apply or_introl.
  - apply or_intror. 
  case Heq' : (find_rec f u == find_rec f i'); move/eqP in Heq'.
  + by [].
  + by rewrite union_forest_sym (find_unchanged_union Heq' Hlti) in Hfind.
Qed.

Let unionC_aux f i i' u v j :
find_rec f i < find_rec f i' ->
find_rec (union_forest f i' i) v < find_rec (union_forest f i' i) u ->
find_rec (union_forest (union_forest f i i') u v) j = find_rec (union_forest (union_forest f u v) i i') j.
Proof.
  move=> Hlti Hltu.
  rewrite union_forest_sym in Hltu.
  have Hltuf := inf_after_union Hlti Hltu.
  have Heqi := ltn_eqF Hlti.
  have Hequ := ltn_eqF Hltu.
  rewrite  (union_forest_sym i i') (union_forest_sym i i').
  case Hij: (find_rec f j == find_rec f i'); move/eqP in Hij.
  case Huj: (find_rec f i == find_rec (union_forest f i i') u); move/eqP in Huj.
    - rewrite (union_forest_sym i i') in Hltu, Huj;
      rewrite (find_changed_changed_union Hlti Hij Hltu Huj).
      have H: find_rec f i = find_rec f u \/ find_rec f i' = find_rec f u by apply (case_find_union Hlti Huj).
      case H => Hui.
      +have Hltuf' : find_rec f v < find_rec f u.
        rewrite Hui ltnn/= in Hltuf. 
        case Hltuf. 
          by [].
          by move=> H'; case: H' =>[H0 [H1 H2]].
      have Hju: find_rec f j <> find_rec f u 
        by rewrite <- Hui, Hij; apply /nesym /eqP /negPf /ltn_eqF.
      have Hdiff: find_rec f i' <> find_rec f u \/ find_rec f i < find_rec f v
        by apply or_introl;rewrite -Hui; move /ltn_eqF /eqP /nesym in Hlti.
      have Hlti' := union_lt_exchange Hlti Hltuf' Hdiff.
      by rewrite (find_changed_changed_union_rev Hltuf' Hij Hui Hlti').
      + have Hltuf' : find_rec f v < find_rec f u.
        rewrite Hui in Hltuf.
        case: Hltuf => Hltuf'.
        by [].
        by rewrite union_forest_sym (find_union_eq Hlti (Hltuf'.2.1)) eq_refl in Hequ.
      have Hju: find_rec f j = find_rec f u by rewrite <- Hui.
        have Hdiff : find_rec f i <> find_rec f u by move=> Hcontradiction; rewrite <- Hcontradiction in Hui;rewrite Hui eq_refl in Heqi.
        have Hltvi: find_rec f v < find_rec f i.
          rewrite <-Huj in Hltu.
          have Hdiffv: find_rec f v <> find_rec f i'.
          by move=> Hcontr; move/ltn_eqF in Hltuf'; rewrite <-Hui,Hcontr, eq_refl in Hltuf'.
          by rewrite union_forest_sym (find_unchanged_union  Hdiffv Hlti) in Hltu.
        have Hji' : find_rec f v <> find_rec (union_forest f u v) i.
          rewrite union_forest_sym (find_unchanged_union Hdiff Hltuf')=> Hcontr.
          by apply ltn_eqF in Hltvi; rewrite Hcontr eq_refl in Hltvi. 
        have Hlti':= (union_lt_exchange2 Hlti Hltuf' Hui Hltvi).
        by rewrite (union_forest_sym i' i) (find_changed_unchanged_union Hltuf' Hju Hlti' Hji').
      + rewrite union_forest_sym in Huj, Hltu.
        rewrite (find_changed_unchanged_union Hlti Hij Hltu Huj).
        have Hju': find_rec f j <> find_rec f u
          by move=>Hcontr; rewrite Hcontr in Hij;rewrite union_forest_sym (find_changed_union Hij Hlti) in Huj.
        have Hdiffu : find_rec f i <> find_rec f u
          by move=>Hcontr;rewrite Hij in Hju'; move/nesym in Hju'; rewrite union_forest_sym (find_unchanged_union Hju' Hlti) in Huj.
        case Hltuf => Hltuf'.
        * have Hiu: find_rec (union_forest f u v) i <> find_rec f u
              by rewrite union_forest_sym (find_unchanged_union Hdiffu Hltuf').
          have Hjud: find_rec f i' <> find_rec f u \/ find_rec f i < find_rec f v 
            by apply or_introl;rewrite Hij in Hju'. 
          have Hji': find_rec f j = find_rec (union_forest f u v) i'
            by rewrite Hij in Hju';  rewrite union_forest_sym (find_unchanged_union Hju' Hltuf').
          have Hlti' := union_lt_exchange Hlti Hltuf' Hjud.
          rewrite (find_unchanged_changed_union Hltuf' Hju' Hlti' Hji' Hiu).
          by rewrite union_forest_sym (find_unchanged_union Hdiffu Hltuf').
        * case: Hltuf' => [Hltuf1 [Hltuf2 Hltuf3]].
        have Hexch : find_rec f i' <> find_rec f v \/ find_rec f i < find_rec f u 
          by apply or_intror.
        have Hlti' := union_lt_exchange Hlti Hltuf1 Hexch.
        rewrite -Hltuf2 in Hij.
        have Hui: find_rec f u = find_rec (union_forest f v u) i'
          by symmetry in Hltuf2;rewrite union_forest_sym (find_changed_union Hltuf2 Hltuf1).
        by rewrite (union_forest_sym u v) (find_changed_changed_union Hltuf1 Hij Hlti' Hui).
      +  rewrite union_forest_sym in Hltu.
        case Hju: (find_rec f j == find_rec (union_forest f i' i) u);move/eqP in Hju.
        case Hvi: (find_rec f v == find_rec f i'); move/eqP in Hvi.
        * case Hltuf=>Hltuf'.
          -- have Hdiff : find_rec f u <> find_rec f i' 
            by move=>Hcontr; 
            apply ltn_eqF in Hltuf';
            rewrite Hcontr Hvi eq_refl in Hltuf'.
          have Hju': find_rec f j = find_rec f u 
            by rewrite union_forest_sym (find_unchanged_union Hdiff Hlti) in Hju.
          rewrite (find_changed_changed_union_rev Hlti Hju' Hvi Hltu).
          have Hvi': find_rec f v = find_rec (union_forest f u v) i' 
          by rewrite Hju' in Hij;move /nesym in Hij;
          rewrite union_forest_sym (find_unchanged_union Hij Hltuf').
          move/nesym in Hdiff;
          have Hdiff': find_rec f i' <> find_rec f u \/ find_rec f i < find_rec f v 
            by apply or_introl.
          have Hlti' := union_lt_exchange Hlti Hltuf' Hdiff'.
          by rewrite (find_changed_changed_union Hltuf' Hju' Hlti' Hvi'). 
        -- case: Hltuf' => [Hltuf1 [Hltuf2 Hltuf3]]. 
          have Hui: find_rec f u <> find_rec f i'.
            by rewrite -Hltuf2; move/ltn_eqF /eqP in Hltuf1.
          have Hexch : find_rec f i' <> find_rec f v \/ find_rec f i < find_rec f u
            by apply or_intror.
          have Hlti' := union_lt_exchange Hlti Hltuf1 Hexch.
          have Hvi' : find_rec (union_forest f i' i) v <> find_rec f i'.
            rewrite union_forest_sym (find_changed_union Hltuf2 Hlti).
            by move /ltn_eqF /eqP in Hlti.
          rewrite (find_unchanged_changed_union Hlti Hij Hltu Hju Hvi').
          rewrite union_forest_sym (find_unchanged_union Hui Hlti) in Hju.
          rewrite -Hltuf2 in Hij.
          have Hji' : find_rec f j = find_rec (union_forest f v u) i'
            by symmetry in Hltuf2; rewrite  union_forest_sym (find_changed_union Hltuf2 Hltuf1).
          have Hiv : find_rec (union_forest f v u) i <> find_rec f v
            by rewrite -Hvi in Hlti; move /ltn_eqF /eqP in Hlti;
            rewrite union_forest_sym (find_unchanged_union Hlti Hltuf1).
          rewrite (union_forest_sym u v) (find_unchanged_changed_union Hltuf1 Hij Hlti' Hji' Hiv).
          have Hvidiff: find_rec f i <> find_rec f v
            by rewrite Hltuf2; move/ltn_eqF /eqP in Hlti.
          by rewrite union_forest_sym (find_changed_union Hltuf2 Hlti)
            union_forest_sym ( find_unchanged_union Hvidiff Hltuf1).
        * have Hltuf' : find_rec f v < find_rec f u.
          case : Hltuf=>Hltuf'.
            by [].
            by exfalso; apply Hvi; exact Hltuf'.2.1.
          have Hdiff: find_rec (union_forest f i' i) v <> find_rec f i'
            by rewrite union_forest_sym (find_unchanged_union Hvi Hlti).
        have H : find_rec f j = find_rec f u \/ find_rec f u = find_rec f i' /\ find_rec f j = find_rec f i.
          case Heq : (find_rec f u == find_rec f i');move/eqP in Heq.
          - by apply or_intror; rewrite union_forest_sym (find_changed_union Heq Hlti) in Hju; split.
          - by apply or_introl; rewrite union_forest_sym (find_unchanged_union Heq Hlti) in Hju.
          case: H => H'.
          --  rewrite (find_unchanged_changed_union Hlti Hij Hltu Hju Hdiff).
          rewrite H' in Hij; move/nesym in Hij.
          have Hdiff0: find_rec f i' <> find_rec f u \/ find_rec f i < find_rec f v
            by apply or_introl. 
          have Hlti' := union_lt_exchange Hlti Hltuf' Hdiff0. 
          have Hvi' : find_rec f v <> find_rec (union_forest f u v) i'.
            by rewrite union_forest_sym (find_unchanged_union Hij Hltuf').
          by rewrite (find_changed_unchanged_union Hltuf' H' Hlti' Hvi')
          union_forest_sym (find_unchanged_union Hvi Hlti).
          -- case: H' => Hui' Hji.
            have Hlt : find_rec f v < find_rec f i by
            rewrite union_forest_sym (find_changed_union Hui' Hlti) 
            (find_unchanged_union Hvi Hlti) in Hltu.
          symmetry in Hui';
          have Hlti' := union_lt_exchange2 Hlti Hltuf' Hui' Hlt.
          have Hdiff': find_rec (union_forest f i' i) v <> find_rec f i'
            by rewrite union_forest_sym (find_unchanged_union Hvi Hlti).
          rewrite (find_unchanged_changed_union Hlti Hij Hltu Hju Hdiff').
          rewrite Hui' in Hij.
          have Hji' : find_rec f j = find_rec (union_forest f u v) i.
            by rewrite Hji in Hij; 
            rewrite union_forest_sym (find_unchanged_union Hij Hltuf').
          have Hi'u : find_rec (union_forest f u v) i' <> find_rec f u
            by rewrite union_forest_sym (find_changed_union Hui' Hltuf'); move /ltn_eqF /eqP in Hltuf'.
          by rewrite !(union_forest_sym i' i) (find_unchanged_changed_union Hltuf' Hij Hlti' Hji' Hi'u)
          (find_unchanged_union Hvi Hlti) union_forest_sym (find_changed_union Hui' Hltuf').
        *rewrite (find_unchanged_unchanged_union Hlti Hij Hltu Hju).
          case H: (find_rec f u == find_rec f i'); move/eqP in H.
          -- have Hltuf' : find_rec f v < find_rec f u.
              rewrite -H in Hltuf.
              case: Hltuf => Hltuf'.
              by [].
              by rewrite union_forest_sym (find_union_eq Hlti (Hltuf'.2.1)) eq_refl in Hequ.
            rewrite union_forest_sym (find_changed_union H Hlti) in Hju.
            have Hvi : find_rec f v <> find_rec f i'
              by move=>Hcontr;rewrite union_forest_sym (find_changed_union Hcontr Hlti) (find_changed_union H Hlti) ltnn in Hltu.
            have Hlt : find_rec f v < find_rec f i
              by rewrite union_forest_sym (find_changed_union H Hlti) (find_unchanged_union Hvi Hlti) in Hltu.
            symmetry in H;
            have Hlti' := union_lt_exchange2 Hlti Hltuf' H Hlt.
            rewrite H in Hij.
            have Hui : find_rec f i <> find_rec f u
              by move=> Hcontr; rewrite Hcontr H eq_refl in Heqi.
            have Hji' : find_rec f j <> find_rec (union_forest f u v) i .
            by rewrite union_forest_sym (find_unchanged_union Hui Hltuf').
            by rewrite (union_forest_sym i' i)  (find_unchanged_unchanged_union Hltuf' Hij Hlti' Hji').
          -- case: Hltuf => Hltuf'.
            ++have Hdiff : find_rec f i' <> find_rec f u \/ find_rec f i < find_rec f v
              by move/nesym in H; apply or_introl.
            have Hlti' := union_lt_exchange Hlti Hltuf' Hdiff.
            have Hji' : find_rec f j <> find_rec (union_forest f u v) i'
              by move/nesym in H; rewrite union_forest_sym (find_unchanged_union H Hltuf').
            have Hju' :  find_rec f j <> find_rec f u
              by rewrite union_forest_sym (find_unchanged_union H Hlti) in Hju.
            by rewrite (find_unchanged_unchanged_union Hltuf' Hju' Hlti' Hji').
            ++ case: Hltuf' => [Hltuf1 [Hltuf2 Hltuf3]].
            rewrite -Hltuf2 in Hij.
            have Hdiff : find_rec f i' <> find_rec f v \/ find_rec f i < find_rec f u 
              by apply or_intror.
            have Hlti' := union_lt_exchange Hlti Hltuf1 Hdiff.
            have Hji' : find_rec f j <> find_rec (union_forest f v u) i'.
            by symmetry in Hltuf2;rewrite union_forest_sym (find_changed_union Hltuf2 Hltuf1);
              rewrite union_forest_sym (find_unchanged_union H Hlti) in Hju.
            by rewrite (union_forest_sym u v) (find_unchanged_unchanged_union Hltuf1 Hij Hlti' Hji').
Qed.

Lemma unionC_aux2 j i i' u v f :
find_rec f i < find_rec f i' ->
find_rec (union_forest (union_forest f i i') u v) j =
find_rec (union_forest (union_forest f u v) i i') j.
Proof.
  move=> Hlti.
  wlog : u v/find_rec f u <= find_rec f v.
  -move=> Hwlog.
  case Hleu: (find_rec f u <= find_rec f v).
    + by apply Hwlog.
    + have Hlev: find_rec f v <= find_rec f u.
        by move: (leqVgt (find_rec f u) (find_rec f v));rewrite Hleu /=; apply ltnW.
      rewrite !(union_forest_sym u v).
      by apply Hwlog.
  -move=> Hleu.
    case Hequ: (find_rec (union_forest f i i') u == find_rec (union_forest f i i') v).
    + rewrite eq_sym union_forest_sym in Hequ; move /eqP in Hequ.
    have H := union_case Hlti Hleu Hequ.
    case H.
    *  by move=>Hequ';move/eqP in Hequ'; rewrite !(union_forest_sym u v) (union_forest_id Hequ') (union_eq i i' Hequ').
    *  move=>Hequivi'; case: Hequivi' => Hequi Heqvi'.
        have Heq := find_union_eq Hlti Heqvi'.
        have Heq' := find_union_eq Hlti Hequi.
        by rewrite !(union_forest_sym u v) (find_eq_unionC  Hequi Heqvi') 
          (union_forest_sym v u) (union_forest_sym i i') (find_eq_unionC  Heq Heq').
    case Hltu: (find_rec (union_forest f i i') v < find_rec (union_forest f i i') u).
    +by rewrite union_forest_sym in Hltu; apply unionC_aux . 
    + rewrite eq_sym in Hequ. 
    rewrite ltn_neqAle Hequ leqNgt /= in Hltu.
    move /negPn in Hltu. 
    rewrite !(union_forest_sym i i') in Hltu.
    rewrite !(union_forest_sym u v).
    by apply unionC_aux . 
Qed.

Let unionC i i' u v: union i i' >> union u v ≈ union u v >> union i i'.
Proof.
  split; first by [].
  rewrite /equiv /=; apply: boolp.funext => j/=.
  case Heqi: (find_rec f i == find_rec f i').
  - by  rewrite (union_forest_id Heqi) (union_eq u v Heqi).
  case Hlti: (find_rec f i < find_rec f i').
  -  apply: (unionC_aux2 j u v Hlti).
  - rewrite ltn_neqAle Heqi leqNgt /= in Hlti.
    move /negPn in Hlti. 
    rewrite !(union_forest_sym i i').
    apply: (unionC_aux2 j u v Hlti).
Qed.

Let findskip i: (find i>> skip) ≈ skip.
Proof.
  by apply eq_is_bisim, boolp.eq_exist, boolp.funext=>?;
  rewrite /find /find_rec /=.
Qed.

HB.instance Definition _ := isMonadUnion.Build
  acto  
  findfind 
  unionfind 
  findunion 
  findunionfind
  union_refl 
  findC 
  union_sym
  unionC
  findskip.

End modelunion.
End ModelUnion.
HB.export ModelUnion.


Module ModelUnionFail.
Section modelunionfail.

Definition acto := MX unit (ModelUnion.acto).
Local Notation M := acto.
Local Notation I := nat.

HB.instance Definition _ := MonadExcept.on M.

Let find i := liftX unit (ModelUnion.find i ).
Let union i j := liftX unit (ModelUnion.union i j).

Definition Bis A (P Q : M A) := ModelUnion.Bis P Q.
Local Notation "a '>>=' b" := (bind a b).
Local Notation "a '>>' b" := (bind a (fun _ => b)).

Lemma refl A (d : M A) : d ≈ d. 
Proof. exact: refl. Qed.

Lemma sym A (d1 d2 : M A) : d1 ≈ d2 -> d2 ≈ d1.
Proof. exact: sym. Qed.

Lemma trans A (d1 d2 d3 : M A) : d1 ≈ d2 -> d2 ≈ d3 -> d1 ≈ d3.
Proof. exact: trans. Qed.

Lemma bindl A B (t : A -> M B) (d1 d2 : M A) : d1 ≈ d2 -> (d1 >>= t) ≈ (d2 >>= t).
Proof. exact: bindl. Qed.

Lemma bindr A B (f g : A -> M B) d :
  (forall a, f a ≈ g a) -> (d >>= f) ≈ (d >>= g).
Proof. by move=> rH; apply: bindfeqv; case. Qed.

HB.instance Definition _ := @hasPreorder.Build M Bis
  (@refl) (@trans) (@bindl) (@bindr).

HB.instance Definition _ := @hasEquivalence.Build M (@sym).

Lemma liftXequiv A (P Q: ModelUnion.acto A ) : 
  P ≈ Q -> liftX unit P ≈ liftX unit Q.
Proof. by move=> Hequiv; apply: bindmeqv. Qed.

Let findfind (A : UU0) i (k : I -> I -> M A):
    eqvM (find i >>= fun r => find i >>= k r)
          (find i >>= fun r => k r r).
Proof. exact: (@findfind (ModelUnion.acto)). Qed.

Let unionfind i j: eqvM (union i j >> find i) (union i j >> find j).
Proof.  
  rewrite -monadMbind -monadMbind /=.
  by apply: liftXequiv;  rewrite (@unionfind (ModelUnion.acto)).
Qed.

Let findunion i j: eqvM (find j >>= union i) (union i j).
Proof. 
  rewrite -monadMbind /=.
  by apply liftXequiv; rewrite (@findunion (ModelUnion.acto)).
Qed.

Let findunionfind  i j u: eqvM (find u >>= fun v => union i j >> find v) (union i j >> find u).
Proof.
  rewrite -monadMbind /=.
  under eq_bind do rewrite -(monadMbind) /=.
  rewrite -(monadMbind) /=.
  apply: liftXequiv.
  exact: (@findunionfind (ModelUnion.acto)).
Qed.

Let ret A (a:A) := liftX unit (Ret a : ModelUnion.acto A).

Let union_refl i: (union i i) ≈ (skip : M unit).
Proof.
  by rewrite /union /skip liftXequiv; 
  last exact: (@union_refl (ModelUnion.acto)).
Qed.

Let findC (A : UU0) i j (k : I -> I -> M A):
  (find i >>= fun u => find j >>= k u) ≈
  (find j >>= fun v => find i >>= k ^~ v).
Proof. exact: (@findC (ModelUnion.acto)). Qed.

Let union_sym i j: (union i j) ≈ (union j i).
Proof.
  rewrite /union; apply liftXequiv; exact: (@union_sym (ModelUnion.acto)). Qed.

Let unionC i j u v: (union i j >> union u v) ≈ (union u v >> union i j).
Proof. 
  rewrite /union -!monadMbind /=;
  apply: liftXequiv; 
  exact: (@unionC (ModelUnion.acto)).
Qed.

Let findskip i : (find i >> skip) ≈ (@skip M).
Proof. by apply: eq_is_bisim; apply: boolp.eq_exist. Qed.

HB.instance Definition _ := isMonadUnion.Build
  acto  
  findfind 
  unionfind 
  findunion 
  findunionfind
  union_refl 
  findC 
  union_sym
  unionC
  findskip.

Let neqfind a b := (find a >>= fun a' => find b >>= fun b' =>  @guard M (a' != b')).

Let neqfindE : forall a b, neqfind a b =
    (find a >>= fun a' => find b >>= fun b':I =>  @guard M (a' != b')).
Proof. by []. Qed.

Lemma find_unchanged_union_eq f i j a:
  (find_rec f a <> find_rec f i) ->
  (find_rec f a <> find_rec f j)->
  (find_rec (union_forest f i j) a) = find_rec f a.
Proof.
  move=> Hi Hj.
  case Heq: (find_rec f i == find_rec f j).
  -  by rewrite union_forest_id.
  case Hlt : (find_rec f i < find_rec f j).
  - by rewrite find_unchanged_union.
  -  rewrite ltn_neqAle Heq leqNgt /= in Hlt.
    move /negPn in Hlt.
    by rewrite union_forest_sym find_unchanged_union.
Qed.

Let findunion_neq A  i j a (k : I-> M A ): 
  (neqfind a i>>neqfind a j>> union i j>> find a >>= k) ≈
  (neqfind a i>> neqfind a j>> find a >>= fun a'=> union i j>> k a').
Proof.
  rewrite neqfindE.
  apply eq_is_bisim, boolp.eq_exist, boolp.funext => f/=.
  case Hi : (find_rec f a != find_rec f i) => //=.
  case Hj : (find_rec f a != find_rec f j) => //=.
  by move/eqP in Hi; move/eqP in Hj;rewrite find_unchanged_union_eq.
Qed.

Let findunion_eq i j: 
    (do i' <- find i; do j' <- find j; union i j >> do r <- find i; 
      @guard M ((i' == r) || (j' == r)))%Do ≈ union i j.
Proof.
  apply eq_is_bisim, boolp.eq_exist, boolp.funext => f/=.
  case Heq: (find_rec f i == find_rec f j).
    - by rewrite (union_forest_id Heq) eq_refl guardT.
    - case Hlt : (find_rec f i < find_rec f j).
      + move/eqP in Heq.
      by rewrite (find_unchanged_union Heq Hlt) eq_refl guardT. 
      + rewrite ltn_neqAle Heq leqNgt /= in Hlt.
        move /negPn in Hlt. 
      rewrite (union_forest_sym i j) 
              (find_changed_union (eqP (eqxx (find_rec f i))) Hlt).
      by rewrite eq_refl orbT guardT.
Qed.

HB.instance Definition _ := isMonadUnionFail.Build
  acto  
  neqfindE
  findunion_neq
  findunion_eq.

End modelunionfail.
End ModelUnionFail.
