From mathcomp Require Import all_ssreflect.
Require Import preamble.
From mathcomp Require boolp.
Require Import hierarchy monad_lib  fail_lib state_lib.
Require Import monad_transformer.


Local Open Scope monae_scope.

Section extra_rules.
Context (S:UU0) (M: unionFailMonad S).
Local Notation I := hierarchy.UnionFind.I.

Lemma findunionl i j : (find i >>= union ^~ j) ≈ @union S M i j.
Proof. 
  by setoid_rewrite unionSymm;  rewrite findunion.
Qed.

Lemma finddup i : (find i >>= find : M I) ≈ find i.
Proof.
  rewrite -{2}(bindskipf (find i)) -(union_id i) -findunionfind.
  apply: bindfeqv => a.
  by rewrite -{1}(bindskipf (find a)) -(union_id i).
Qed.

Lemma uniondup i j : union i j >> union i j ≈ (union i j : M unit).
Proof.
  setoid_rewrite <-findunionl at 2.
  setoid_rewrite <-bindA.
  rewrite unionfind  bindA.
  setoid_rewrite findunionl.
  setoid_rewrite union_id.
  by rewrite bindmskip. 
Qed.

Lemma union_eq : forall a i j, find a ≈ (find j :M I) -> (union i a : M unit) ≈ union i j.
Proof.
  move=> a i j Hfind.
  rewrite -findunion -findunion.
  by apply: bindmeqv.
Qed.

(*not sure it is the right way to go*)
Lemma find_eq a i :  find a ≈ (find i : M I) -> neqfind a i ≈ (fail : M unit).
Proof.
  move=> Heq.
  rewrite neqfindE Heq findfind.
  under eq_bind => x.
  have H := @erefl I x.
  move/eqP in H; rewrite H=>/=.
  rewrite guardF.
  over.
  by rewrite find_lookup.
Qed.

Lemma find_neq_rec a i :  neqfind a i ≈ (skip : M unit) -> ~find a ≈ (find i : M I).
Proof.
  have H :  neqfind a i ≈ (skip : M unit) <-> ~ neqfind a i ≈ fail by admit. (* not provable unless ~skip ≈ fail*)
  rewrite H; apply (contra_not (find_eq a i)).
Abort.
End extra_rules.

Section equivLaws.
Context (S:UU0) (M: unionFailMonad S).
Local Notation I := hierarchy.UnionFind.I.

(* TODO M more generic + move into lib*)
Lemma bind_ext_guard_equiv [A : UU0] [b : bool] [m1 m2 : M A]:
(b -> m1 ≈ m2) -> guard b >> m1 ≈ guard b >> m2.
Proof.
  case b => H.
  by rewrite guardT !bindskipf; apply H.
  by rewrite guardF !bindfailf.
Qed.
End equivLaws.

Section correction_proof.
Context (S:UU0) (M: unionFailMonad S).
Local Notation I := hierarchy.UnionFind.I.

Lemma guardLem b : guard b ≈ (fail : M unit) \/ guard b ≈ (skip : M unit).
  case: b.
  by apply or_intror; rewrite guardT.
  by apply or_introl; rewrite guardF.
Qed.

Lemma neqfindLem a i : neqfind a i ≈ (fail : M unit) \/ neqfind a i ≈ (skip : M unit).
Proof.
  rewrite neqfindE.
Abort.

Lemma remember_find  B (a:I) (m :I-> M B): 
find a >>= (fun a' => m a') ≈
find a >>= (fun a0 => find a >>= fun a1 => guard (a0 == a1)>> m a0).
Proof.
  by rewrite findfind;
  apply: bindfeqv=>{}a0;
  rewrite eqxx guardT bindskipf.
Qed.

Lemma rewrite_under A B C (d1 d2 : M B) (f : M C) (g : B -> M A) : 
d1 ≈ (d2 : M B) -> 
(f >>= fun x => d1 >>= g : M A) ≈ f >>= fun x => d2 >>= g.
Proof.
  by move=> Heq;
  apply: bindfeqv=>_;
  apply: bindmeqv. 
Qed.

Lemma guardfindC A b a (f: I -> M A): 
  (guard b >> find a >>= f : M A)≈
  find a >>=(fun x => guard b >> f x).
Proof.
  case b.
  - rewrite guardT bindskipf.
    by symmetry; under eq_bind do rewrite bindskipf.
  - rewrite guardF !bindfailf.
    symmetry; under eq_bind do rewrite bindfailf.
    by rewrite find_lookup.
Qed.

Lemma pushfind B a a' b (m : I -> M B): 
find a >>=
(fun x : I =>
((guard (a' == x) >> find b) >>= (fun v : I => m v))) ≈
find b >>= fun v => (
find a >>= (fun x : I => ((guard (a' == x) >> m v)))).
Proof.
  rewrite (bindfeqv _ _ _ _ _ (fun a => guardfindC _ (a' == a) b _) ).
  by rewrite findC.
Qed.

Lemma union_axiome  (i j a b: I):
(union i j >> find a >>= fun a' => find b >>= fun b' => guard (a' == b'): M unit )≈
find a >>= fun a' => find b >>= fun b' => find i >>= fun i' => find j >>= fun j' => 
union i' j' >> guard ((a' == b') || ((a' == i') && (b' == j')) || ((a' == j') && (b' == i'))).
Proof.
(* ### Seaction i & j ###*)
    setoid_rewrite <-(findunionl S M i j).
  have : (find i >>= union^~ j ≈ (find i >>=(fun i'=> find j >>= union i'):M unit)).
  - apply: bindfeqv=>{}i'; symmetry;exact: findunion.
  move=>H.
  setoid_rewrite H.
  rewrite bindA.
  setoid_rewrite (findC _ b i).
  setoid_rewrite (findC _ a i).
  rewrite bindA. (*remember i root*)
  apply: bindfeqv=>{}i'.
  rewrite bindA.
  setoid_rewrite (findC _ b j).
  setoid_rewrite (findC _ a j). (*remember j root*)
  apply: bindfeqv=>{}j'.
(* ### Seaction a & b ###*)
  rewrite -bindA -findunionfind bindA.
  rewrite remember_find.
  symmetry;rewrite remember_find;symmetry.
  apply: bindfeqv=>{}a'.
  rewrite !bindA.
  setoid_rewrite findC at 1.
  rewrite -bindA.
  under bindfeqv do rewrite -bindA.
  rewrite -(rewrite_under _ _ _ _ _ _ _ (findunionfind i' j' b))
          bindA.
  under eq_bind do rewrite -bindA -bindA.
  setoid_rewrite guardfindC.
  rewrite -bindA findC.
  symmetry.
  under eq_bind do rewrite -bindA.
  rewrite (bindfeqv _ _ _ _ _ (fun a => guardfindC _ (a' == a) b _))
          (findC _ a) remember_find.
  symmetry.
  rewrite bindA remember_find.
  apply: bindfeqv=>{}b'.
  rewrite bindA.
  under eq_bind=>x. under eq_bind=>x0. under eq_bind=>x1. rewrite bindA.
  under eq_bind do rewrite bindA. over. over. over.
  symmetry.
  case Hb : ((a' == b') || (a' == i') && (b' == j') || (a' == j') && (b' == i')).
  - admit.
  - apply Bool.orb_false_elim in Hb.
    case Hb => [Hb0 Hb1].
    apply Bool.orb_false_elim in Hb0.
    case: Hb0 => Hb0 Hb2.
    symmetry.
Abort.


Definition union_iter  (l : seq (I*I)) : M unit  := 
  foldM (fun _  p => union p.1 p.2) tt l.

Definition lookup_vertex  n (l :n.-tuple (I*I)) (p : 'I_n*bool) :=
  let p' := tnth l p.1 in if p.2 then p'.1 else p'.2.

Definition exist_path n (l : n.-tuple (I*I)) a b (p: n.-bseq ('I_n*bool)) (p0 : 'I_n*bool) :=
(a == b) || (a == lookup_vertex n l p0) && path (fun r s => lookup_vertex n l s == lookup_vertex n l (r.1, negb r.2)) p0 p && (b == lookup_vertex n l (last p0 p)). 

Lemma union_iteration n (l : n.-tuple (I*I)) a b p p0:
(union_iter l >> find a >>= fun a' => find b >>= fun b' => Ret (a' == b') : M bool) ≈
find a >>= fun a' => find b >>= fun b' => union_iter l >> Ret ( exist_path n l a' b' p p0).
Proof.
Abort.
End correction_proof.