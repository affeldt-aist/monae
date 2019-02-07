Require Import FunctionalExtensionality Coq.Program.Tactics.
Require Classical.
Require Import ssreflect ssrmatching ssrfun ssrbool.
From mathcomp Require Import eqtype ssrnat seq path div choice fintype tuple.
From mathcomp Require Import finfun bigop.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* jones and duponcheel, composing monads, sect 2, 3 *)

Require Import monad.

Module Comp.
Section comp.
Variables (M N : monad).
Definition F : functor (M \o N) := FComp (fmap M) (fmap N).
Definition ret A : A -> M (N A) := Ret \o Ret.
Lemma fmap_ret (A B : Type) (h : A -> B) : (F # h) \o (@ret _) = (@ret _) \o h.
Proof.
rewrite /ret.
rewrite -[in RHS]compA.
rewrite -(fmap_ret N h).
rewrite [in RHS]compA.
rewrite [in LHS]compA.
by rewrite fmap_ret.
Qed.
End comp.
End Comp.
Arguments Comp.ret {M} {N} {A}.

Module Prod.
Section prod.
Variables M N(* NB: actually, premonad is enough for N*) : monad.
Variable prod : forall A, N (M (N A)) -> M (N A).
Arguments prod {A}.

Definition JOIN A : M (N (M (N A))) -> M (N A) := join \o fmap M # prod.
Arguments JOIN {A}.

Definition prod1 := forall A B (f : A -> B), prod \o fmap _ # (Comp.F M N # f) = Comp.F M N # f \o prod.
Definition prod2 := forall A, prod \o Ret = id :> (_ -> M (N A)).
Definition prod3 := forall A, prod \o fmap _ # Comp.ret = Ret :> (_ -> M (N A)).
Definition prod4 := forall A, prod \o fmap _ # JOIN = JOIN \o prod :> (_ -> M (N A)).
Hypothesis Hprod1 : prod1.
Hypothesis Hprod2 : prod2.
Hypothesis Hprod3 : prod3.
Hypothesis Hprod4 : prod4.

Lemma JOIN_naturality : join_functor_commutativity (@JOIN) (Comp.F M N).
Proof.
move=> A B g; apply/esym; rewrite {1}/JOIN -[in LHS]compA -functor_o Hprod1.
by rewrite functor_o compA -join_naturality -compA.
Qed.

Lemma JOIN_ret : join_left_unit (@Comp.ret _ _) (@JOIN).
Proof.
move=> A; rewrite /JOIN /Comp.ret /= compA -(compA join) fmap_ret.
by rewrite compA join_ret compidf Hprod2.
Qed.

Lemma JOIN_fmap_ret : join_right_unit (@Comp.ret _ _) (@JOIN) (Comp.F M N).
Proof.
move=> A.
by rewrite /JOIN /Comp.ret -compA -functor_o Hprod3 join_fmap_ret.
Qed.

Lemma JOIN_fmap_JOIN : join_associativity (@JOIN) (Comp.F M N).
Proof.
move=> A; rewrite {1 2}/JOIN -[in LHS]compA.
rewrite -functor_o Hprod4 {1}/JOIN -(compA join) 2!functor_o compA join_fmap_join.
by rewrite -compA (compA join (fmap _ # (fmap _ # prod)) (fmap _ # prod)) -join_naturality.
Qed.

End prod.
End Prod.

Module Dorp.
Section dorp.
Variables M  (* actually, premonad is enough for M *) N : monad.
Variable dorp : forall A, M (N (M A)) -> M (N A).
Arguments dorp {A}.

Definition JOIN A : M (N (M (N A))) -> M (N A) := fmap _ # join \o dorp.
Arguments JOIN {A}.

Definition dorp1 := forall A B (f : A -> B), dorp \o Comp.F M N # (fmap _ # f) = Comp.F M N # f \o dorp.
Definition dorp2 := forall A, (@dorp A) \o Comp.ret = fmap _ # Ret.
Definition dorp3 := forall A, (@dorp A) \o Comp.F M N # Ret = id.
Definition dorp4 := forall A, (@dorp A) \o JOIN = JOIN \o Comp.F M N # dorp.
Hypothesis Hdorp1 : dorp1.
Hypothesis Hdorp2 : dorp2.
Hypothesis Hdorp3 : dorp3.
Hypothesis Hdorp4 : dorp4.

Lemma join_naturality : join_functor_commutativity (@JOIN) (Comp.F M N).
Proof.
move=> A B g; apply/esym; rewrite {1}/JOIN -compA Hdorp1.
by rewrite compA -functor_o -join_naturality functor_o.
Qed.

Lemma JOIN_ret : join_left_unit (@Comp.ret _ _) (@JOIN).
Proof. by move=> A; rewrite /JOIN -compA Hdorp2 -functor_o join_ret functor_id. Qed.

Lemma JOIN_fmap_ret : join_right_unit (@Comp.ret _ _) (@JOIN) (Comp.F M N).
Proof.
move=> A; rewrite /JOIN /Comp.ret functor_o compA -(compA _ dorp) Hdorp3.
by rewrite compfid -functor_o join_fmap_ret functor_id.
Qed.

Lemma JOIN_fmap_JOIN : join_associativity (@JOIN) (Comp.F M N).
Proof.
move=> A; rewrite {1 2}/JOIN functor_o -compA (compA dorp) Hdorp1.
rewrite -(compA _ dorp) (compA (fmap M # join)) -functor_o.
rewrite join_fmap_join functor_o.
by rewrite -2!compA (compA (fmap _ # join) dorp) -/JOIN -Hdorp4 compA.
Qed.

End dorp.
End Dorp.

Module Swap.
Section swap.
Variables M N : monad.
Variable swap : forall A, N (M A) -> M (N A).
Arguments swap {A}.

Definition JOIN A := fmap _ # join \o join \o fmap _ # (@swap (N A)).

Lemma JOINE A : @JOIN A = join \o fmap _ # (fmap _ # join \o swap).
Proof. by rewrite /JOIN join_naturality -compA -functor_o. Qed.

Let prod A := fmap _ # (@join _ A) \o (@swap _).
Arguments prod {A}.
Let dorp A := join \o fmap _ # (@swap A).
Arguments dorp {A}.

Fact JOIN_prod A : @JOIN A = join \o fmap _ # prod.
Proof. by rewrite JOINE. Qed.

Fact JOIN_dorp A : @JOIN A = fmap _ # join \o dorp.
Proof. by rewrite /dorp compA. Qed.

Definition swap1 := forall A B (f : A -> B), swap \o fmap _ # (fmap _ # f) = fmap _ # (fmap _ # f) \o swap .
Definition swap2 := forall A, @swap A \o Ret = fmap _ # Ret :> (M A -> M (N A)).
Definition swap3 := forall A, @swap A \o fmap _ # Ret = Ret :> (N A -> M (N A)).
Definition swap4 := forall A, (@prod A) \o fmap _ # (@dorp _) = (@dorp _) \o (@prod _).
Hypothesis Hswap1 : swap1.
Hypothesis Hswap2 : swap2.
Hypothesis Hswap3 : swap3.
Hypothesis Hswap4 : swap4.

Lemma prod1 : Prod.prod1 (@prod).
Proof.
move=> A B f; rewrite {1}/prod.
rewrite -compA Hswap1 (compA (fmap M # join)) -functor_o.
by rewrite -join_naturality functor_o -compA.
Qed.

Lemma prod2 : Prod.prod2 (@prod).
Proof. by move=> A; rewrite /prod -compA Hswap2 -functor_o join_ret functor_id. Qed.

Lemma prod3 : Prod.prod3 (@prod).
Proof.
move=> A; rewrite /prod /Comp.ret functor_o compA -(compA (fmap _ # join)) Hswap3.
by rewrite fmap_ret -compA join_fmap_ret compfid.
Qed.

Lemma prod4 : Prod.prod4 (@prod).
Proof.
move=> A; rewrite {1}/Prod.JOIN -JOIN_prod JOIN_dorp {1}/prod functor_o.
rewrite compA -(compA (fmap _ # join)) Hswap1 compA -functor_o join_fmap_join functor_o.
rewrite -compA -(compA (fmap _ # join)) (compA (fmap _ # join) swap) -/prod Hswap4.
by rewrite compA /Prod.JOIN -JOIN_prod JOIN_dorp.
Qed.

Lemma dorp1 : Dorp.dorp1 (@dorp).
Proof.
move=> A B g; rewrite {1}/dorp -compA -functor_o.
by rewrite Hswap1 functor_o (compA join) -join_naturality -compA.
Qed.

Lemma dorp2 : Dorp.dorp2 (@dorp).
Proof.
move=> A; rewrite /dorp /Comp.ret compA -(compA join).
by rewrite fmap_ret compA join_ret compidf Hswap2.
Qed.

Lemma dorp3 : Dorp.dorp3 (@dorp).
Proof.
move=> A; by rewrite /dorp -compA -functor_o Hswap3 join_fmap_ret.
Qed.

Lemma dorp4 : Dorp.dorp4 (@dorp).
Proof.
move=> A; rewrite {1}/dorp {1}/Dorp.JOIN /= -JOIN_dorp JOIN_prod.
rewrite compA -(compA join) join_naturality.
rewrite compA -join_fmap_join -2!compA -2!functor_o.
by rewrite compA -/dorp -Hswap4 functor_o compA -JOINE JOIN_dorp.
Qed.

Lemma JOIN_naturality : join_functor_commutativity (@JOIN) (Comp.F M N).
Proof. by move=> ?? g; rewrite JOINE -/prod (Prod.JOIN_naturality prod1 g) JOINE. Qed.

Lemma JOIN_ret : join_left_unit (@Comp.ret _ _) (@JOIN).
Proof. by move=> A; rewrite JOINE -/prod (Prod.JOIN_ret prod2). Qed.

Lemma JOIN_fmap_ret : join_right_unit (@Comp.ret _ _) (@JOIN) (Comp.F M N).
Proof. by move=> A; rewrite JOINE -/prod (Prod.JOIN_fmap_ret prod3). Qed.

Lemma JOIN_fmap_JOIN : join_associativity (@JOIN) (Comp.F M N).
Proof. by move=> A; rewrite !JOINE -!/prod (Prod.JOIN_fmap_JOIN prod4). Qed.

End swap.
End Swap.
