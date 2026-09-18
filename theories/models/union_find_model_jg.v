(* monae: Monadic equational reasoning in Rocq                                *)
(* Copyright (C) 2025 monae authors, license: LGPL-2.1-or-later               *)
From Stdlib Require Import Recdef Wf_nat.
From mathcomp Require Import all_ssreflect ssralg ssrint.
From mathcomp Require boolp.
Require Import preamble hierarchy monad_lib alt_lib fail_lib.
From HB Require Import structures.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.

Module AsFunction.
Definition I := nat.

Definition forest := {f : I -> I | forall x, f x <= x}.

Implicit Type f : forest.

Definition proj_forest f := sval f.
Coercion proj_forest : forest >-> Funclass.

Function find f x {wf lt x} :=
  let y := f x in
  if y == x then x else find f y.
Proof.
- by move=> f x H; apply/ltP; rewrite ltn_neqAle H (proj2_sig f).
- exact: lt_wf.
Defined.

Definition union' f (x y : I) : I -> I :=
  let x := find f x in let y := find f y in
  if x < y then (fun z => if z == y then x else f z) else
  if y < x then (fun z => if z == x then y else f z) else f.

Lemma union_forest f x y z : union' f x y z <= z.
Proof.
have f_decr := proj2_sig f.
rewrite /union'; case: ifPn => [/ltnW xy | _].
  by case: ifP => [/eqP -> |].
case: ifPn => // /ltnW yx.
by case: ifP => [/eqP -> |].
Qed.

Definition union f (x y : I) : forest :=
  exist _ _ (union_forest f x y).

Definition empty : forest := exist _ _ leqnn.

Local Notation is_root f x := (proj_forest f x == x).

Lemma find_is_root f x : is_root f (find f x).
Proof. functional induction (find f x) => //; exact/eqP. Qed.

Lemma find_iter f x : 
  exists n, find f x == iter n f x.
Proof.
functional induction (find f x).
  by exists 0.
by case: IHi => n IH; exists n.+1; rewrite iterSr.
Qed.

Definition find_steps f x := ex_minn (find_iter f x).

Lemma is_root_iter_eq f x m n :
  is_root f (iter m f x) -> is_root f (iter n f x) ->
  iter m f x = iter n f x.
Proof.
wlog nm : m n / m >= n.
  case: (leqP n m) => nm; first exact.
  move=> H Hm Hn; apply/esym/H => //; exact/ltnW.
rewrite -(subnK nm) iterD => _ /eqP Hr.
by rewrite iter_fix.
Qed.

Lemma iter_find (f : forest) x n :
  find f (iter n f x) = find f x.
Proof.
set y := iter _ _ x.
have := find_is_root f x.
have := find_is_root f y.
case: (find_iter f x) => n1 /eqP ->.
case: (find_iter f y) => n2 /eqP ->.
rewrite {}/y -iterD.
exact: is_root_iter_eq.
Qed.

Lemma leq_find f x : find f x <= x.
Proof.
functional induction (find f x) => //.
exact/(leq_trans IHi)/(proj2_sig f).
Qed.

Lemma find_root f x : is_root f x <-> find f x = x.
Proof.
split.
  by rewrite find_equation => ->.
move <-; exact: find_is_root.
Qed.

Lemma find_steps_next f z :
  ~~ is_root f z -> find_steps f z = (find_steps f (f z)).+1.
Proof.
symmetry.
rewrite /find_steps.
case: ex_minnP => m Hm Hn.
case: ex_minnP => m1 Hm1 /(_ m.+1).
rewrite iterSr -(eqP Hm) -(iter_find f z 1) /= eqxx => /(_ isT) m1m.
apply/eqP; rewrite eqn_leq m1m andbT.
move/(_ m1.-1): Hn.
rewrite (iter_find f z 1) -iterSr -ltnS.
case: m1 Hm1 H {m1m} => [/eqP /find_root -> | m1 ffz _] //=; exact.
Qed.

Lemma union_non_root f x y z :
  ~~ is_root f z -> union f x y z = f z.
Proof.
rewrite /= /union' /=.
by case: ltngtP => // xy; case: ifP => // /eqP ->; rewrite find_is_root.
Qed.

Lemma iter_union_keep f x y z :
  iter (find_steps f z) (union f x y) z = find f z.
Proof.
functional induction (find f z) as [z|z].
  rewrite /find_steps; case: ex_minnP => m Hm /(_ 0) /=.
  by rewrite leqn0 (eqP Hm) iter_fix ?(eqP e) // eqxx => /(_ isT) /eqP ->.
have nrz : ~~ is_root f z by case: ifP y1.
by rewrite find_steps_next // iterSr -IHi union_non_root.
Qed.

Lemma find_union f x y z :
  find (union f x y) (find f z) = find (union f x y) z.
Proof. by rewrite -(iter_union_keep f x y z) iter_find. Qed.

Lemma is_root_union f x y z :
  is_root (union f x y) (find f z) =
  (find f z != maxn (find f x) (find f y)) || (find f x == find f y).
Proof.
rewrite /= /union' /=.
case: ltngtP => xy.
- case: ifP => /eqP zy /=; last exact: find_is_root.
  by rewrite zy ltn_eqF.
- case: ifP => /eqP zx /=; last exact: find_is_root.
  by rewrite zx ltn_eqF.
- by rewrite find_is_root orbT.
Qed.

Lemma is_root_unionL f x y :
  find f x <= find f y -> is_root (union f x y) (find f x).
Proof.
by rewrite is_root_union; case: ltngtP => // [/ltn_eqF -> //|]; rewrite eqxx.
Qed.

Lemma is_root_unionR f x y :
  find f x >= find f y -> is_root (union f x y) (find f y).
Proof.
by rewrite is_root_union; case: ltngtP => // [/ltn_eqF -> //|]; rewrite eqxx.
Qed.

Lemma unionC f : commutative (union f).
Proof. by move=> x y; apply/boolp.eq_exist; rewrite /union' /=; case: ltngtP.
Qed.

Lemma unionxx f x y : find f x = find f y -> union f x y = f.
Proof.
case: f => f hf xy; apply/boolp.eq_exist/boolp.funext => z.
by rewrite /union' xy ltnn.
Qed.

Lemma union_joined f x y :
  find (union f x y) (find f x) = find (union f x y) (find f y).
Proof.
wlog xy : x y / find f x <= find f y.
  move=> H; case: (leqP (find f x) (find f y)) => [/H // | yx].
  rewrite unionC; exact/esym/H/ltnW.
have Hrx := is_root_unionL xy.
rewrite [RHS]find_equation /= /union' /=.
move: xy; rewrite leq_eqVlt => /orP[/eqP <- | xy].
  rewrite ltnn find_is_root; exact/find_root.
by rewrite xy eqxx (ltn_eqF xy).
Qed.
(*set u := union f x y.
rewrite find_equation; symmetry; rewrite find_equation.
case: (ltngtP (find f x) (find f y)) => xy.
- have Hx : is_root u (find f x) by exact/is_root_unionL/ltnW.
  rewrite Hx /= /union' xy eqxx (ltn_eqF xy).
  exact/find_root.
- have Hy : is_root u (find f y) by exact/is_root_unionR/ltnW.
  rewrite Hy /= /union' xy ltnNge (ltnW xy) /= eqxx (ltn_eqF xy).
  exact/esym/find_root.
- by rewrite /= /union' xy ltnn find_is_root.*)

Lemma union_ok f x y z :
  let u := union f x y in
  (find u z == find u x) = ((find f z == find f x) || (find f z == find f y)).
Proof.
move=> u.
rewrite -(find_union _ _ _ z) -(find_union _ _ _ x) -/u.
have [-> | zx] := eqVneq (find f z) (find f x); first by rewrite eqxx.
have [-> | zy] := eqVneq (find f z) (find f y).
  by rewrite union_joined eqxx.
apply/negbTE.
have /find_root -> : is_root u (find f z).
  rewrite is_root_union.
  by case: (ltngtP (find f x) (find f y)); rewrite (zx,zy,orbT).
case: (leqP (find f x) (find f y)) => xy.
- by move/is_root_unionL/find_root : xy ->.
- rewrite union_joined.
  by move/ltnW/is_root_unionR/find_root : xy ->.
Qed.

Lemma union_keep f x y z t :
  let u := union f x y in
  find f z = find f t -> find u z = find u t.
Proof. by move=> u zt; rewrite -find_union zt find_union. Qed.

Lemma union_spec f x y z :
  find f x <= find f y ->
  find (union f x y) z = if find f z == find f y then find f x else find f z.
Proof.
move=> xy.
case: ifPn => zy.
  move: (union_ok f y x z) => /=.
  rewrite zy /= unionC => /eqP ->.
  move/find_root: (is_root_unionL xy) => <-.
  by rewrite (union_joined f x y) find_union.
rewrite -find_union.
move: (is_root_union f x y z).
case: ltnP xy => // xy _.
by rewrite zy => /find_root.
Qed.

Section monad.
Definition equiv (f1 f2 : forest) := find f1 = find f2.
Local Definition bisim {A} (m1 m2 : forest -> A * forest) :=
  forall f1 f2, equiv f1 f2 ->
                (m1 f1).1 = (m2 f2).1 /\ equiv (m1 f1).2 (m2 f2).2.
Definition acto : UU0 -> UU0 := fun A =>
   {g : forest -> A * forest | bisim g g}.
Local Notation M := acto.
Let id_equiv A (a:A) f1 f2 : equiv f1 f2 -> a = a /\ equiv f1 f2 :=
  fun p => conj erefl p.
Let ret : idfun ~~> M := fun A a => exist _ (fun s => (a, s)) (id_equiv a).
Local Definition bind (A B : UU0) (m : M A) (f : A -> M B) : M B.
exists (fun s => let (a,s) := sval m s in sval (f a) s).
abstract (move=> f1 f2 f12;
case: m => m hm /=;
move: {hm} (hm _ _ f12);
case: (m f1) => a1 f1';
case: (m f2) => a2 f2' /= [] <- f12';
case: (f a1) => {}m hm /=;
exact: hm).
Defined.

Lemma surjective_exist (T : Type) (P : T -> Prop) (p : {x : T | P x}):
  exist [eta P] (sval p) (proj2_sig p) = p.
Proof. by case: p. Qed.

Let left_neutral : BindLaws.left_neutral bind ret.
Proof.
move=> A B a f; rewrite -[RHS]surjective_exist; exact: boolp.eq_exist.
Qed.
Let right_neutral : BindLaws.right_neutral bind ret.
Proof.
by move=> A [] f Hf; apply/boolp.eq_exist/boolp.funext => s /=; case: (f s).
Qed.
Let associative : BindLaws.associative bind.
Proof.
move=> A B C [a Ha] b c /=.
by apply/boolp.eq_exist/boolp.funext => s /=; case: (a s).
Qed.
HB.instance Definition _ :=
  isMonad_ret_bind.Build M left_neutral right_neutral associative.

Let wBisim {A} (m1 m2 : M A) := bisim (sval m1) (sval m2).
Let wBisim_refl A (a : M A) : wBisim a a.
Proof. by move=> f1 f2 f12; case: (proj2_sig a _ _ f12). Qed.
Let wBisim_sym A (a b : M A) : wBisim a b -> wBisim b a.
Proof. by move=> ab f1 f2 /esym/ab[ab1 ab2]. Qed.
Let wBisim_trans A (a b c : M A) : wBisim a b -> wBisim b c -> wBisim a c.
Proof.
move=> ab bc f1 f2 /ab[ab1 ab2].
by case: (bc f2 _ erefl) => /(etrans ab1) ? /(etrans ab2).
Qed.

Let bindmwB (A B : UU0) (f : A -> M B) (d1 d2 : M A) :
    wBisim d1 d2 -> wBisim (d1 >>= f) (d2 >>= f).
Proof.
move=> d1d2 f1 f2 f12.
rewrite /hierarchy.bind /=.
case: (d1d2 _ _ f12).
case: (sval d1 f1) => a f1' /=.
by case: (sval d2 f2) => b f2' /= <- /(proj2_sig (f a)).
Qed.

Let bindfwB (A B : UU0) (f g : A -> M B) (d : M A) :
    (forall a, wBisim (f a) (g a)) -> wBisim (d >>= f) (d >>= g).
Proof.
move=> fg f1 f2 f12.
rewrite /hierarchy.bind /=.
case: (proj2_sig d _ _ f12).
case: (sval d f1) => a f1'.
case: (sval d f2) => b f2' /= <- f1f2'.
exact: fg.
Qed.

HB.instance Definition _ :=
  hasWBisim.Build M wBisim_refl wBisim_sym wBisim_trans bindmwB bindfwB.

Lemma equiv_union x y f1 f2 :
  equiv f1 f2 -> equiv (union f1 x y) (union f2 x y).
Proof.
move=> f12; apply: boolp.funext => z.
rewrite /equiv in f12.
case: (leqP (find f2 x) (find f2 y)) => [|/ltnW] xy.
  by rewrite !union_spec ?f12.
by rewrite unionC [in RHS]unionC !union_spec ?f12.
Qed.

Definition munion (x y : I) : M unit.
exists (fun f => (tt, union f x y)).
abstract (by move=> f1 f2 /= /(equiv_union x y)).
Defined.

Definition mfind (x : I) : M I.
exists (fun f => (find f x, f)).
abstract (by move=> f1 f2; rewrite /equiv => <- /=).
Defined.
End monad.

Lemma union_find_l f x y : union f (find f x) y = union f x y.
Proof.
apply/boolp.eq_exist/boolp.funext => z.
rewrite /union' /= -[X in find X (find f x)](unionxx (@erefl _ (find f x))).
by rewrite find_union unionxx.
Qed.

Lemma union_same_l f x x' y :
  find f x = find f x' -> union f x y = union f x' y.
Proof. by move=> xx'; rewrite -union_find_l xx' union_find_l. Qed.

Lemma union_find_r f x y : union f x (find f y) = union f x y.
Proof. by rewrite unionC union_find_l unionC. Qed.

Lemma union_same_r f x y y' :
  find f y = find f y' -> union f x y = union f x y'.
Proof. by move=> yy'; rewrite -union_find_r yy' union_find_r. Qed.

Lemma find_union_same f x y z z' :
  find f z = find f z' -> find (union f x y) z = find (union f x y) z'.
Proof. by move=> zz'; rewrite -find_union zz' find_union. Qed.

Lemma order_union_seq f x y u t :
  (forall x y, find f x < find f y -> 
     find (union (union f x y) u t) =1 find (union (union f u t) x y)) ->
  find (union (union f x y) u t) =1 find (union (union f u t) x y).
Proof.
case: (ltngtP (find f x) (find f y)) => xy.
- exact.
- rewrite !(unionC _ x y); exact.
- by rewrite (unionxx xy) (unionxx (union_keep u t xy)).
Qed.

Lemma union_seq1 f x y t :
  find f x < find f y < find f t ->
  find (union (union f x y) y t) =1 find (union (union f y t) x y).
Proof.
rewrite !ltn_neqAle => /andP[] /andP[xy xy'] /andP[/negbTE yt yt'] z.
rewrite !union_spec // ?(eqxx,yt,eq_sym (find f t)); first last.
- exact: leq_trans yt'.
- by case: ifPn => [/eqP|].
case: (ifP (find f z == find f y)) => [/eqP -> | zy].
  by rewrite yt eqxx; case: ifPn xy xy' yt' => // /eqP <-; case: ltngtP.
case: ifP => zt; last by rewrite zy.
by rewrite eqxx; case: ifPn xy xy' yt' => // /eqP <-; case: ltngtP.
Qed.

Lemma union_seq2 f x y u :
  find f u <= find f x < find f y ->
  find (union (union f u y) x y) =1 find (union (union f x y) u y).
Proof.
case/andP => ux /[dup] /(leq_ltn_trans ux). 
rewrite !ltn_neqAle => /andP[/negbTE uy uy'] /andP[/negbTE xy xy'] z.
rewrite unionC !union_spec ?(eqxx,uy,xy) //.
case/boolP: (find f z == find f y) => zy //.
by rewrite eqxx if_same.
Qed.

Lemma unionunion f x y u t :
  find (union (union f x y) u t) =1 find (union (union f u t) x y).
Proof.
apply: order_union_seq => {x y} x y xy z; symmetry.
apply: order_union_seq z => {u t} u t ut z; symmetry.
case/boolP: (find f u == find f y) ut => [/eqP|/negbTE] uy.
  rewrite uy (union_same_l _ uy) (union_same_l _(find_union_same _ _ uy)) => ut.
  exact/union_seq1/andP.
case/boolP: (find f x == find f t) => [/eqP|/negbTE] xt.
  symmetry; rewrite xt in xy.
  rewrite (union_same_l _ xt) (union_same_l _ (find_union_same _ _ xt)).
  exact/union_seq1/andP.
case/boolP: (find f t == find f y) => [/eqP|/negbTE] ty.
  rewrite ty (union_same_r _ ty) (union_same_r _ (find_union_same _ _ ty)).
  case: (leqP (find f u) (find f x)) => [|/ltnW] ux ut.
    exact/esym/union_seq2/andP.
  exact/union_seq2/andP.
move: xy; rewrite !ltn_neqAle => /andP[xy' xy] /andP[ut' ut].
move: (ty); rewrite eq_sym => yt.
rewrite !union_spec // !(xt,uy,ty,yt) //.
case/boolP: (find f z == find f y) => [/eqP -> | /negbTE zy].
  by rewrite xt yt eqxx.
case/boolP: (find f z == find f t) => zt; by rewrite (uy,zy).
Qed.

Local Notation M := acto.
Local Notation "a '≈' b" := (wBisim a b).

Lemma munionunion x y u t : munion x y >> munion u t ≈ munion u t >> munion x y.
Proof.
rewrite /wBisim/= => f1 f2 f1f2 /=.
split=> //.
apply/boolp.funext => z.
rewrite unionunion.
case: (munion u t) => f1' f2'.
by move: (equiv_union u t f1f2) => /(equiv_union x y) /= ->.
Qed.

Lemma macto_ext A (m1 m2 : M A) : sval m1 =1 sval m2 -> m1 = m2.
Proof. case: m1 m2 => ?? [??] ?; exact/boolp.eq_exist/boolp.funext. Qed.

Lemma mfindunionr x y : mfind y >>= munion x = munion x y.
Proof. by apply/macto_ext => f /=; rewrite union_find_r. Qed.

Lemma munionC x y : munion x y = munion y x.
Proof. by apply/macto_ext => f /=; rewrite unionC. Qed.

Lemma mfindC A x y (m : I -> I -> M A) :
  mfind x >>= (fun x' => mfind y >>= m x') =
  mfind y >>= (fun y' => mfind x >>= m ^~ y').
Proof. exact/macto_ext. Qed.

Lemma mfindfind A x (k : I -> I -> M A) :
  mfind x >>= (fun x' => mfind x >>= k x') =
  mfind x >>= (fun x' => mfind x >> k x' x').
Proof. exact/macto_ext. Qed.

Lemma mfindskip x : mfind x >> skip = skip.
Proof. exact/macto_ext. Qed.

Lemma mfindunionfind x y z :
  (mfind z >>= fun z' => munion x y >> mfind z') = munion x y >> mfind z.
Proof. by apply/macto_ext => f /=; rewrite find_union. Qed.

Lemma munionfind x y : munion x y >> mfind x = munion x y >> mfind y.
Proof.
apply/macto_ext => f; congr pair.
by rewrite -find_union union_joined find_union.
Qed.

Lemma munionxx x : munion x x = skip.
Proof. by apply/macto_ext => f /=; rewrite unionxx. Qed.

(* Derived rules *)

Lemma mfindunionl x y : mfind x >>= munion ^~ y = munion x y.
Proof. by under eq_bind do rewrite munionC; rewrite mfindunionr munionC. Qed.

Lemma mfinddup x : mfind x >>= mfind = mfind x.
Proof.
rewrite -[RHS]bindskipf -(munionxx x) -mfindunionfind.
by apply: eq_bind => z; rewrite munionxx bindskipf.
Qed.

Lemma muniondup x y : munion x y >> munion x y = munion x y.
Proof.
rewrite -{2}mfindunionl -bindA munionfind bindA.
by rewrite mfindunionl munionxx bindmskip.
Qed.
End AsFunction.
