From mathcomp Require Import all_ssreflect.
Require Import preamble.
From mathcomp Require boolp.
Require Import hierarchy monad_lib  fail_lib state_lib.
Require Import monad_transformer.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.

Section extra_rules.
Variable M : unionFailMonad.
Local Notation I := hierarchy.UnionFind.I.

Lemma findunionl i j : (find i >>= union ^~ j) ≈ @union M i j.
Proof. by setoid_rewrite union_sym; rewrite findunion. Qed.

Lemma finddup A i m : (find i >>= fun x => find x >>= m  : M A) ≈ find i >>= m.
Proof.
  rewrite -{2}(bindskipf (find i)) -(union_refl i) -findunionfind !bindA.
  apply: bindfeqv => a.
  by rewrite -{1}(bindskipf (find a)) -(union_refl i).
Qed.

Lemma uniondup i j : @union M i j >> union i j ≈ union i j.
Proof.
  setoid_rewrite <-findunionl at 2.
  setoid_rewrite <-bindA.
  rewrite unionfind  bindA.
  setoid_rewrite findunionl.
  setoid_rewrite union_refl.
  by rewrite bindmskip. 
Qed.

Lemma union_eq a i j: @find M a ≈ find j -> @union M i a ≈ union i j.
Proof. by rewrite -findunion -findunion; apply: bindmeqv. Qed.

Lemma find_lookup A i (m : M A) : (find i >> m) ≈ m.
Proof. by rewrite -(bindskipf m) -{2}(findskip i) bindA. Qed.

End extra_rules.

Section equivLaws.
Variable M : unionFailMonad.
Local Notation I := hierarchy.UnionFind.I.

(* TODO M more generic + move into lib*)
Lemma bind_eqv_guard [A : UU0] [b : bool] [m1 m2 : M A]:
  (b -> m1 ≈ m2) -> guard b >> m1 ≈ guard b >> m2.
Proof.
  case: b => H.
  - by rewrite guardT !bindskipf H.
  - by rewrite guardF !bindfailf.
Qed.
End equivLaws.

Section correction_proof.
Variable  M : unionFailMonad.
Local Notation I := hierarchy.UnionFind.I.

Section findchk.
Definition findchk A a a' (k : _ -> M A) : M A :=
  find a >>= fun x => guard (a' == x) >> k x.

Import Morphisms.
#[global] Add Parametric Morphism A : (@findchk A) with signature
  eq ==> eq ==> (Morphisms.pointwise_relation nat (@eqvM M A)) ==> (@eqvM M A)
  as findchk_mor_eqvM.
Proof.
move => x y f g Hfg; rewrite /findchk.
apply: bindfeqv => a.
by setoid_rewrite (Hfg a).
Qed.
End findchk.

Lemma remember_find  B (a : I) (k : I-> M B) :
  (find a >>= k) ≈ (find a >>= fun a' => findchk a a' (fun=> k a')).
Proof.
  by rewrite findfind; apply: bindfeqv => {}a'; rewrite eqxx guardT bindskipf.
Qed.

Lemma guardfindC A b a (f: I -> M A): 
  @guard M b >> (find a >>= f) ≈
  find a >>= fun x => guard b >> f x.
Proof.
case: b.
- rewrite guardT bindskipf.
  by under [eqvRHS]eq_bind do rewrite bindskipf.
- rewrite guardF !bindfailf.
  under [eqvRHS]eq_bind do rewrite bindfailf.
  by rewrite find_lookup.
Qed.

Lemma findchkfindC B a a' b (k : I -> I-> M B) :
  (findchk a a' (fun x => find b >>= k ^~ x)) ≈
  (find b >>= fun v => findchk a a' (k v)).
Proof.
by rewrite [eqvLHS](bindfeqv (fun a => guardfindC (a' == a) b _)) findC.
Qed.

Lemma guardC A b1 b2 (m : M A) :
  guard b1 >> (guard b2 >> m) ≈ guard b2 >> (guard b1 >> m).
Proof. by rewrite -!bindA -guard_and andbC guard_and. Qed.

Lemma findchkfind A a a' (k : I -> M A) :
  findchk a a' (fun=> find a' >>= k) ≈ findchk a a' k.
Proof.
transitivity (findchk a a' (fun x => find x >>= k)).
  by apply: bindfeqv => x; apply: bind_eqv_guard => /eqP ->.
rewrite [eqvLHS](bindfeqv (fun x => guardfindC _ _ _)).
rewrite -(findfind _ _ (fun x y => _ >>= fun z => guard (a' == x) >> _)).
by rewrite (bindfeqv (fun x => finddup _ _)) findfind.
Qed.

Ltac normalize_bindA :=
  rewrite ?bindA;
  try (under eq_bind => ?; [normalize_bindA; over |]).

Lemma add_neqfind A a a' i i' (m : M A) : 
  a' != i' ->
  findchk a a' (fun=> findchk i i' (fun=> m)) ≈
  findchk a a' (fun=> findchk i i' (fun=> neqfind a' i' >> m)).
Proof.
move=> Hdiff.
symmetry.
rewrite /findchk neqfindE.
normalize_bindA.
setoid_rewrite (findchkfindC i).
rewrite [eqvLHS]findchkfind.
apply: bindfeqv => r.
apply: bind_eqv_guard => /eqP <-.
rewrite findchkfind.
apply: bindfeqv => i1.
apply: bind_eqv_guard => /eqP <-.
by rewrite Hdiff guardT bindskipf.
Qed.

Lemma findchkC A a a' j j' (k : I -> I -> M A) :
  findchk a a' (fun x => findchk j j' (k x)) ≈
  findchk j j' (fun y => findchk a a' (k ^~ y)).
Proof.
rewrite [eqvLHS](bindfeqv (fun x => guardfindC (a' == x) _ _)) findC.
apply: bindfeqv => j0.
case: (j' == j0).
  rewrite guardT !bindskipf.
  apply: bindfeqv => a0.
  by rewrite bindskipf.
symmetry.
rewrite guardF !bindfailf -{1}(find_lookup a fail).
apply: bindfeqv => a0.
case: (a' == a0).
- by rewrite guardT bindskipf bindfailf.
- by rewrite guardF bindfailf.
Qed.

Lemma findchk_neqfindC A i i' a j (m : M A) :
  findchk i i' (fun=> neqfind a j >> m) ≈
  neqfind a j >> findchk i i' (fun=> m).
Proof.
  rewrite neqfindE.
  normalize_bindA.
  symmetry.
  normalize_bindA.
  setoid_rewrite (guardfindC _ i).
  rewrite (bindfeqv (fun=>findC _ _ i _)) findC.
  apply: bindfeqv => i0.
  do 2 (rewrite guardfindC; apply: bindfeqv => ?).
  by rewrite guardC.
Qed.

Lemma union_axiom_neqcase a' a b' b i' i j' j : 
  a' != b' -> a' != i' -> a' != j' ->
  findchk b b' (fun=> findchk a a'
    (fun=> findchk j j' (fun=> findchk i i' (fun=> union i' j' >> fail)))) ≈
  findchk b b' (fun=> findchk a a'
    (fun=> findchk j j' (fun=> findchk i i' (fun=> union i' j' >>
       (find b' >>= fun y => find a' >>= fun x => guard (x == y)))))).
Proof.
  move=> Hab Hai Haj.
  setoid_rewrite (findchkC a a' j j').
  setoid_rewrite (add_neqfind a i _ Hai).
  do 2 setoid_rewrite (findchkC j j').
  setoid_rewrite (findchkC a a' i i').
  rewrite /findchk.
  do 2 setoid_rewrite findchk_neqfindC.
  setoid_rewrite (add_neqfind a j _ Haj).
  (*use neqfind to exchange find and union*)
  do 2 setoid_rewrite <-findchk_neqfindC.
  setoid_rewrite (findC _ b' a').
  symmetry.
  rewrite -3![X in findchk j j' (fun=> X)]bindA.
  setoid_rewrite findunion_neq.
  rewrite !bindA.
  (* supress neqfind once used*)
  do 8 setoid_rewrite findchk_neqfindC.
  do 2 apply: bindfeqv => _.
  (* reunite find a and find a' *)
  setoid_rewrite (findchkC a).
  setoid_rewrite findchkfind.
  (*case analysis*)
  case Hb: ( (b' == i') || (b' == j')).
  - case/orP: Hb => [/eqP Hbi | /eqP Hbj].
    + rewrite Hbi.
      apply: bindfeqv => b0.
      apply: bind_eqv_guard => _ {b0}.
      (*test to see*)
      do 2 setoid_rewrite (findchkC i).
      setoid_rewrite (findchkC j).
      apply: bindfeqv => a0.
      apply: bind_eqv_guard => /eqP <- {a0}.
      setoid_rewrite <-(findunion_eq i' j').
      normalize_bindA.
      setoid_rewrite (findC _ i' j').
      symmetry.
      normalize_bindA.
      setoid_rewrite (findC _ i' j').
      setoid_rewrite (findchkC j).
      setoid_rewrite (findchkfind j j').
      setoid_rewrite (findchkfindC j).
      rewrite !findchkfind.
      apply: bindfeqv => i1.
      apply: bind_eqv_guard => /eqP <- {i1}.
      apply: bindfeqv => j1.
      apply: bind_eqv_guard => /eqP <- {j1}.
      apply: bindfeqv => _.
      setoid_rewrite guardfindC.
      rewrite findfind.
      apply: bindfeqv => i2.
      apply: bind_eqv_guard => /orP[] /eqP <-.
      - by rewrite (negbTE Hai).
      - by rewrite (negbTE Haj).
    + rewrite Hbj.
      apply: bindfeqv => b0.
      apply: bind_eqv_guard => _ {b0}.
      do 2 setoid_rewrite (findchkC i).
      setoid_rewrite (findchkC j).
      apply: bindfeqv => a0.
      apply: bind_eqv_guard => /eqP <- {a0}.
      setoid_rewrite union_sym.
      setoid_rewrite <-(findunion_eq j' i').
      normalize_bindA.
      symmetry.
      normalize_bindA.
      setoid_rewrite (findchkC j).
      setoid_rewrite (findchkfind j j').
      setoid_rewrite (findchkfindC j).
      rewrite !findchkfind.
      apply: bindfeqv => i1.
      apply: bind_eqv_guard => /eqP <- {i1}.
      apply: bindfeqv => j1.
      apply: bind_eqv_guard => /eqP <- {j1}.
      apply: bindfeqv => _.
      setoid_rewrite guardfindC.
      rewrite findfind.
      apply: bindfeqv => j2.
      apply: bind_eqv_guard=> /orP[] /eqP <-.
      - by rewrite (negbTE Haj).
      - by rewrite (negbTE Hai).
  - case/norP: Hb => Hbi Hbj.
    setoid_rewrite (findchkC j).
    (* now we do the same as we did with a in the first part of the proof but with b*)
    do 2 setoid_rewrite (findchkC i).
    do 2 setoid_rewrite (findchkC b).
    apply: bindfeqv => a0.
    apply: bind_eqv_guard => /eqP <-.
    setoid_rewrite (add_neqfind  _ _ _ Hbi).
    do 3 setoid_rewrite findchk_neqfindC.
    setoid_rewrite (findchkC b).
    do 2 setoid_rewrite (findchkC j).
    setoid_rewrite (add_neqfind _ _ _ Hbj).
    do 3 setoid_rewrite <-(findchk_neqfindC _ _ b' i').
    rewrite -3![X in findchk j j' (fun=> X)]bindA.
    setoid_rewrite findunion_neq.
    rewrite !bindA.
    do 6 setoid_rewrite findchk_neqfindC.
    do 2 apply: bindfeqv => _.
    setoid_rewrite (findchkC b).
    setoid_rewrite findchkfind.
    apply: bindfeqv => i0.
    apply: bind_eqv_guard => _ {i0}.
    apply: bindfeqv => j0.
    apply: bind_eqv_guard => _ {j0}.
    apply: bindfeqv => b0.
    apply: bind_eqv_guard => /eqP <-.
    by rewrite (negbTE Hab).
Qed.

Lemma union_classes (i j a b : I):
 union i j >> (find a >>= fun a' => find b >>= fun b' => @guard M (a' == b')) ≈
 find a >>= fun a' => find b >>= fun b' =>
 find i >>= fun i' => find j >>= fun j' => union i' j' >>
 guard ((a' == b') || ((a' == i') && (b' == j')) || ((a' == j') && (b' == i'))).
Proof.
  setoid_rewrite <-(findunionl M i j).
  have -> : find i >>= union^~ j ≈ find i >>= fun i' => find j >>= union i'
    by move=>*; apply: bindfeqv => i'; rewrite findunion.
  rewrite bindA.
  setoid_rewrite (findC _ b i).
  setoid_rewrite (findC _ a i).
  rewrite [in eqvLHS](remember_find i) [in eqvRHS](remember_find i).
  apply: bindfeqv => i'.
  rewrite !bindA.
  setoid_rewrite (findC _ b j).
  setoid_rewrite (findC _ a j).
  do 2 (rewrite findchkfindC (remember_find j);symmetry).
  apply: bindfeqv=>{}j'.
  rewrite -bindA.
  setoid_rewrite <-findunionfind.
  rewrite bindA.
  do 2 setoid_rewrite (findchkfindC _ _ a).
  under eq_bind do rewrite bindA.
  transitivity
    (@find M a >>= fun a1 => findchk j j'
      (fun x => findchk i i' (fun y => union i' j' >>
      (find b >>= fun b' => find a1 >>= fun a' => guard (a' == b'))))).
    by setoid_rewrite (findC _ b).
  under eq_bind do rewrite -bindA.
  setoid_rewrite <-findunionfind.
  normalize_bindA.
  do 2 setoid_rewrite (findchkfindC _ _ b).
  rewrite [in eqvLHS]remember_find [in eqvRHS]remember_find.
  apply: bindfeqv => a'.
  rewrite /(findchk a).
  setoid_rewrite guardfindC.
  rewrite !(findC _ _ b).
  rewrite [in eqvLHS]remember_find [in eqvRHS]remember_find.
  apply: bindfeqv=>{}b'.
  rewrite -!/(findchk a a' _).
  case Hb: ((a' == b') || (a' == i') && (b' == j') || (a' == j') && (b' == i')).
  - do 4 (apply: bindfeqv => ?; apply: bind_eqv_guard => _).
    case /orP: Hb => [/orP[] |].
    + move/eqP ->.
      apply: bindfeqv => _.
      rewrite findfind.
      under eq_bind do rewrite eqxx.
      by rewrite guardT find_lookup.
    + case/andP => /eqP -> /eqP ->.
      rewrite -bindA -unionfind bindA.
      apply: bindfeqv => _.
      rewrite findfind.
      under eq_bind do rewrite eqxx.
      by rewrite guardT find_lookup.
    + case/andP => /eqP -> /eqP ->.
      rewrite -bindA unionfind bindA.
      apply: bindfeqv => _.
      rewrite findfind.
      under eq_bind do rewrite eqxx.
      by rewrite guardT find_lookup.
  - case /norP: Hb => /norP [Hb0].
    case /boolP: (a' == i') => Hai /= Hbj;
    case /boolP : (a' == j') => Haj /= Hbi.
    + rewrite !(findchkC b b' a a' _).
      rewrite union_axiom_neqcase //; last by rewrite eq_sym.
      setoid_rewrite (findC _ b' a' _).
      do 11 apply/bindfeqv=>?.
      by rewrite eq_sym.
    + have Ha2 : (b' != i') by move /eqP in Hai;rewrite -Hai eq_sym.
      rewrite !(findchkC b b' a a' _).
      rewrite union_axiom_neqcase //; last by rewrite eq_sym.
      setoid_rewrite (findC _ b' a' _).
      do 11 apply/bindfeqv=>?.
      by rewrite eq_sym.    
    + have Hb3 : (b' != j') by move /eqP in Haj;rewrite -Haj eq_sym.
      rewrite !(findchkC b b' a a' _).
      rewrite union_axiom_neqcase //; last by rewrite eq_sym.
      setoid_rewrite (findC _ b' a' _).
      do 11 apply/bindfeqv=>?.
      by rewrite eq_sym.
    + by rewrite union_axiom_neqcase.
Qed.

Definition union_iter  (l : seq (I*I)) : M unit  := 
  foldM (fun _  p => union p.1 p.2) tt l.

Definition lookup_vertex  n (l :n.-tuple (I*I)) (p : 'I_n*bool) :=
  let p' := tnth l p.1 in if p.2 then p'.1 else p'.2.

Definition exist_path n (l : n.-tuple (I*I)) a b (p: n.-bseq ('I_n*bool)) (p0 : 'I_n*bool) :=
(a == b) || (a == lookup_vertex l p0) && path (fun r s => lookup_vertex l s == lookup_vertex l (r.1, negb r.2)) p0 p && (b == lookup_vertex l (last p0 p)). 

Lemma union_iteration n (l : n.-tuple (I*I)) a b p p0:
(union_iter l >> find a >>= fun a' => find b >>= fun b' => Ret (a' == b') : M bool) ≈
find a >>= fun a' => find b >>= fun b' => union_iter l >> Ret ( exist_path l a' b' p p0).
Proof.
Abort.
End correction_proof.
