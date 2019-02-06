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
Variables M N : monad.
Definition fmap : functor (M \o N) := Functor.mk (fun A B => (((@fmap M _ _) \o (@fmap N _ _)) : (A -> B) -> (M \o N) A -> (M \o N) B)).
Definition ret A : A -> M (N A) := Ret \o Ret.
Lemma fmap_o : Map_laws.comp fmap.
Proof.
rewrite /Map_laws.comp => A B C g h.
rewrite /fmap.
apply functional_extensionality => m.
rewrite [in RHS]compE.
rewrite /=.
unlock.
rewrite !bindA.
bind_ext => x.
rewrite /=.
rewrite bindretf.
rewrite /=.
rewrite !bindA.
congr (_ # _).
bind_ext => a.
rewrite /=.
by rewrite bindretf.
Qed.
(*Proof. rewrite /Map_laws.comp => *; by rewrite /fmap /= 2!fmap_o. Qed.*)
Lemma fmap_ret (A B : Type) (f : A -> B) : fmap # f \o (@ret _) = (@ret _) \o f.
Proof. by rewrite /fmap /ret /= compA fmap_ret -compA fmap_ret. Qed.
End comp.
End Comp.
Arguments Comp.ret {M} {N} {A}.

Module Prod.
Section prod.
Variables M N(* NB: actually, premonad is enough for N*) : monad.
Variable prod : forall A, N (M (N A)) -> M (N A).
Arguments prod {A}.

Definition JOIN A : M (N (M (N A))) -> M (N A) := join \o fmap \# prod.
Arguments JOIN {A}.

Definition prod1 := forall A B (f : A -> B), prod \o fmap \# (Comp.fmap M N _ _ f) = Comp.fmap M N _ _ f \o prod.
Definition prod2 := forall A, prod \o Ret = id :> (_ -> M (N A)).
Definition prod3 := forall A, prod \o fmap \# Comp.ret = Ret :> (_ -> M (N A)).
Definition prod4 := forall A, prod \o fmap \# JOIN = JOIN \o prod :> (_ -> M (N A)).
Hypothesis Hprod1 : prod1.
Hypothesis Hprod2 : prod2.
Hypothesis Hprod3 : prod3.
Hypothesis Hprod4 : prod4.

Lemma JOIN_naturality : join_fmap_commutativity (@JOIN) (@Comp.fmap _ _).
Proof.
move=> A B g; apply/esym; rewrite {1}/JOIN /= -[in LHS]compA -fmap_o Hprod1.
by rewrite fmap_o {1}/Comp.fmap /= compA -join_naturality -compA.
Qed.

Lemma JOIN_ret : join_left_unit (@Comp.ret _ _) (@JOIN).
Proof.
move=> A; rewrite /JOIN /Comp.ret /= compA -(compA join) fmap_ret.
by rewrite compA join_ret compidf Hprod2.
Qed.

Lemma JOIN_fmap_ret : join_right_unit (@Comp.ret _ _) (@JOIN) (@Comp.fmap _ _).
Proof.
move=> A.
by rewrite /JOIN /Comp.ret /Comp.fmap /= -compA -fmap_o Hprod3 join_fmap_ret.
Qed.

Lemma JOIN_fmap_JOIN : join_associativity (@JOIN) (@Comp.fmap _ _).
Proof.
move=> A; rewrite {1 2}/JOIN /Comp.fmap -[in LHS]compA.
rewrite -fmap_o Hprod4 {1}/JOIN -(compA join) 2!fmap_o compA join_fmap_join.
by rewrite -compA (compA join (fmap \# (fmap \# prod)) (fmap \# prod)) -join_naturality.
Qed.

End prod.
End Prod.

Module Dorp.
Section dorp.
Variables M  (* actually, premonad is enough for M *) N : monad.
Variable dorp : forall A, M (N (M A)) -> M (N A).
Arguments dorp {A}.

Definition JOIN A : M (N (M (N A))) -> M (N A) := fmap \# join \o dorp.
Arguments JOIN {A}.

Definition dorp1 := forall A B (f : A -> B), dorp \o Comp.fmap M N _ _ (fmap \# f) = Comp.fmap M N _ _ f \o dorp.
Definition dorp2 := forall A, (@dorp A) \o Comp.ret = fmap \# Ret.
Definition dorp3 := forall A, (@dorp A) \o Comp.fmap M N _ _ Ret = id.
Definition dorp4 := forall A, (@dorp A) \o JOIN = JOIN \o Comp.fmap M N _ _ dorp.
Hypothesis Hdorp1 : dorp1.
Hypothesis Hdorp2 : dorp2.
Hypothesis Hdorp3 : dorp3.
Hypothesis Hdorp4 : dorp4.

Lemma join_naturality : join_fmap_commutativity (@JOIN) (@Comp.fmap _ _).
Proof.
move=> A B g; apply/esym; rewrite {1}/JOIN {2}/Comp.fmap /= -compA Hdorp1.
by rewrite {1}/Comp.fmap /= compA -fmap_o -join_naturality fmap_o.
Qed.

Lemma JOIN_ret : join_left_unit (@Comp.ret _ _) (@JOIN).
Proof. by move=> A; rewrite /JOIN -compA Hdorp2 -fmap_o join_ret fmap_id. Qed.

Lemma JOIN_fmap_ret : join_right_unit (@Comp.ret _ _) (@JOIN) (@Comp.fmap _ _).
Proof.
move=> A; rewrite /JOIN /Comp.ret Comp.fmap_o compA -(compA _ dorp) Hdorp3.
by rewrite compfid /Comp.fmap /= -fmap_o join_fmap_ret fmap_id.
Qed.

Lemma JOIN_fmap_JOIN : join_associativity (@JOIN) (@Comp.fmap _ _).
Proof.
move=> A; rewrite {1 2}/JOIN Comp.fmap_o -compA (compA dorp) Hdorp1.
rewrite {1}/Comp.fmap /= 2!compA -fmap_o join_fmap_join fmap_o.
by rewrite -2!compA (compA (fmap \# join) dorp) -/JOIN -Hdorp4 compA.
Qed.

End dorp.
End Dorp.

Module Swap.
Section swap.
Variables M N : monad.
Variable swap : forall A, N (M A) -> M (N A).
Arguments swap {A}.

Definition JOIN A := fmap \# join \o join \o fmap \# (@swap (N A)).

Lemma JOINE A : @JOIN A = join \o fmap \# (fmap \# join \o swap).
Proof. by rewrite /JOIN join_naturality -compA -fmap_o. Qed.

Let prod A := fmap \# (@join _ A) \o (@swap _).
Arguments prod {A}.
Let dorp A := join \o fmap \# (@swap A).
Arguments dorp {A}.

Fact JOIN_prod A : @JOIN A = join \o fmap \# prod.
Proof. by rewrite JOINE. Qed.

Fact JOIN_dorp A : @JOIN A = fmap \# join \o dorp.
Proof. by rewrite /dorp compA. Qed.

Definition swap1 := forall A B (f : A -> B), swap \o fmap \# (fmap \# f) = fmap \# (fmap \# f) \o swap .
Definition swap2 := forall A, @swap A \o Ret = fmap \# Ret :> (M A -> M (N A)).
Definition swap3 := forall A, @swap A \o fmap \# Ret = Ret :> (N A -> M (N A)).
Definition swap4 := forall A, (@prod A) \o fmap \# (@dorp _) = (@dorp _) \o (@prod _).
Hypothesis Hswap1 : swap1.
Hypothesis Hswap2 : swap2.
Hypothesis Hswap3 : swap3.
Hypothesis Hswap4 : swap4.

Lemma prod1 : Prod.prod1 (@prod).
Proof.
move=> A B f; rewrite {1}/prod {1}/Comp.fmap /= -compA Hswap1 compA -fmap_o.
by rewrite -join_naturality fmap_o -compA.
Qed.

Lemma prod2 : Prod.prod2 (@prod).
Proof. by move=> A; rewrite /prod -compA Hswap2 -fmap_o join_ret fmap_id. Qed.

Lemma prod3 : Prod.prod3 (@prod).
Proof.
move=> A; rewrite /prod /Comp.ret fmap_o compA -(compA (fmap \# join)) Hswap3.
by rewrite fmap_ret -compA join_fmap_ret compfid.
Qed.

Lemma prod4 : Prod.prod4 (@prod).
Proof.
move=> A; rewrite {1}/Prod.JOIN -JOIN_prod JOIN_dorp {1}/prod fmap_o.
rewrite compA -(compA (fmap \# join)) Hswap1 compA -fmap_o join_fmap_join fmap_o.
rewrite -compA -(compA (fmap \# join)) (compA (fmap \# join) swap) -/prod Hswap4.
by rewrite compA /Prod.JOIN -JOIN_prod JOIN_dorp.
Qed.

Lemma dorp1 : Dorp.dorp1 (@dorp).
Proof.
move=> A B g; rewrite {1}/dorp {1}/Comp.fmap /=.
by rewrite -compA -fmap_o Hswap1 fmap_o compA -join_naturality -compA -/dorp.
Qed.

Lemma dorp2 : Dorp.dorp2 (@dorp).
Proof.
move=> A; rewrite /dorp /Comp.ret compA -(compA join).
by rewrite fmap_ret compA join_ret compidf Hswap2.
Qed.

Lemma dorp3 : Dorp.dorp3 (@dorp).
Proof.
move=> A; by rewrite /dorp /Comp.fmap /= -compA -fmap_o Hswap3 join_fmap_ret.
Qed.

Lemma dorp4 : Dorp.dorp4 (@dorp).
Proof.
move=> A; rewrite {1}/dorp {1}/Dorp.JOIN /= -JOIN_dorp JOIN_prod.
rewrite compA -(compA join) join_naturality.
rewrite compA -join_fmap_join -2!compA -2!fmap_o.
by rewrite compA -/dorp -Hswap4 fmap_o compA -JOINE JOIN_dorp.
Qed.

Lemma JOIN_naturality : join_fmap_commutativity (@JOIN) (@Comp.fmap _ _).
Proof. by move=> ?? g; rewrite JOINE -/prod (Prod.JOIN_naturality prod1 g) JOINE. Qed.

Lemma JOIN_ret : join_left_unit (@Comp.ret _ _) (@JOIN).
Proof. by move=> A; rewrite JOINE -/prod (Prod.JOIN_ret prod2). Qed.

Lemma JOIN_fmap_ret : join_right_unit (@Comp.ret _ _) (@JOIN) (@Comp.fmap _ _).
Proof. by move=> A; rewrite JOINE -/prod (Prod.JOIN_fmap_ret prod3). Qed.

Lemma JOIN_fmap_JOIN : join_associativity (@JOIN) (@Comp.fmap _ _).
Proof. by move=> A; rewrite !JOINE -!/prod (Prod.JOIN_fmap_JOIN prod4). Qed.

End swap.
End Swap.
