From mathcomp Require Import all_ssreflect.
Require Import monae_lib monad.

(* jones and duponcheel, composing monads, sect 2, 3 *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Comp.
Section comp.
Variables (M N : monad).
Definition ret : FId ~> M \O N.
apply: (@Natural.Pack FId (M \O N) (HComp Ret Ret) _).
apply: Natural.Class.
move=> A B h.
by rewrite -(natural (HComp Ret Ret)).
Defined.
(*Arguments ret {_}.*)
(*Lemma fmap_ret A B (h : A -> B) : ((M \O N) # h) \o ret = ret \o h.
Proof.
rewrite {2}/ret -[in RHS]compA -(ret_naturality N h) [in RHS]compA.
by rewrite {1}/ret [in LHS]compA ret_naturality FIdf.
Qed.*)
End comp.
End Comp.
(*Arguments Comp.ret _ _ {_}.*)
Notation CRet := (Comp.ret).

Module Prod.
Section prod.
Variables M N(* NB: actually, premonad is enough for N*) : monad.
Variable prod : N \O (M \O N) ~~> M \O N.
Arguments prod {_}.

Definition JOIN : (M \O N) \O (M \O N) ~~> M \O N := fun _ => Join \o M # prod.
Arguments JOIN {_}.

Definition prod1 := forall A B (f : A -> B), prod \o N # ((M \O N) # f) = (M \O N) # f \o prod.
Definition prod2 := forall A, prod \o Ret _ = id :> (_ -> (M \O N) A).
Definition prod3 := forall A, prod \o N # CRet M N _ = Ret _ :> (_ -> (M \O N) A).
Definition prod4 := forall A, prod \o N # JOIN = JOIN \o prod :> (_ -> (M \O N) A).
Hypothesis Hprod1 : prod1.
Hypothesis Hprod2 : prod2.
Hypothesis Hprod3 : prod3.
Hypothesis Hprod4 : prod4.

Lemma JOIN_naturality : Natural.P _ _ (@JOIN).
Proof.
move=> A B g; apply/esym; rewrite {1}/JOIN -[in LHS]compA.
transitivity (
  Join \o (M # prod \o M # ((N \O (M \O N)) # g))).
  by [].
rewrite -functor_o Hprod1.
rewrite functor_o compA /JOIN FCompE -(FCompE M M).
rewrite -(natural Monad.Exports.Join).
by rewrite -compA.
Qed.

Definition JOIN' : (M \O N) \O (M \O N) ~> M \O N :=
  @Natural.Pack _ _ _ (Natural.Class JOIN_naturality).

Lemma JOIN_ret : JoinLaws.left_unit (@CRet M N) (@JOIN').
Proof.
move=> A; rewrite /JOIN'.
rewrite /=.
rewrite /CRet.
rewrite compA.
rewrite -(compA Join (M # prod) (Ret _)).
rewrite (natural Ret).
by rewrite compA (compA Join) joinretM compidf Hprod2.
Qed.

Lemma JOIN_fmap_ret : JoinLaws.right_unit (@CRet M N) (@JOIN').
Proof.
move=> A.
rewrite /JOIN' /=.
rewrite -compA.
rewrite FCompE.
rewrite -(functor_o M).
by rewrite Hprod3 joinMret.
Qed.

Lemma JOIN_fmap_JOIN : JoinLaws.associativity (@JOIN').
Proof.
move=> A; rewrite {1 2}/JOIN' -[in LHS]compA /=.
rewrite -functor_o.
rewrite Hprod4.
rewrite {1}/JOIN.
rewrite -(compA Join (M # prod) prod).
rewrite functor_o.
rewrite compA.
rewrite joinA.
rewrite -compA.
rewrite functor_o.
rewrite (compA Join (M # (M # prod)) (M # prod)).
by rewrite -(natural _).
Qed.

End prod.
End Prod.

Module Dorp.
Section dorp.
Variables M  (* actually, premonad is enough for M *) N : monad.
Variable dorp : M \O (N \O M) ~~> M \O N.
Arguments dorp {_}.

Definition JOIN : (M \O N) \O (M \O N) ~~> M \O N := fun _ => M # Join \o dorp.
Arguments JOIN {_}.

Definition dorp1 := forall A B (f : A -> B), dorp \o (M \O N) # (M # f) = (M \O N) # f \o dorp.
Definition dorp2 := forall A, (@dorp A) \o CRet M N _ = M # Ret _.
Definition dorp3 := forall A, (@dorp A) \o (M \O N) # Ret _ = id.
Definition dorp4 := forall A, (@dorp A) \o JOIN = JOIN \o (M \O N) # dorp.
Hypothesis Hdorp1 : dorp1.
Hypothesis Hdorp2 : dorp2.
Hypothesis Hdorp3 : dorp3.
Hypothesis Hdorp4 : dorp4.

Lemma join_naturality : Natural.P _ _ (@JOIN).
Proof.
move=> A B g; apply/esym; rewrite {1}/JOIN -compA Hdorp1.
rewrite compA.
rewrite (FCompE M N (N # g)).
rewrite -(functor_o M).
rewrite -natural.
by rewrite functor_o.
Qed.

Definition JOIN' := Natural.Pack (Natural.Class join_naturality).

Lemma JOIN_ret : JoinLaws.left_unit (@CRet M N) (@JOIN').
Proof.
move=> A; rewrite /JOIN -compA Hdorp2.
rewrite -(functor_o M).
by rewrite joinretM functor_id.
Qed.

Lemma JOIN_fmap_ret : JoinLaws.right_unit (@CRet M N) (@JOIN').
Proof.
move=> A; rewrite /JOIN /Comp.ret.
rewrite -(compA (M # Join) dorp).
rewrite (functor_o (M \O N)).
rewrite (compA dorp) Hdorp3.
rewrite compidf -functor_o.
by rewrite joinMret functor_id.
Qed.

Lemma JOIN_fmap_JOIN : JoinLaws.associativity (@JOIN').
Proof.
move=> A; rewrite {1 2}/JOIN'.
rewrite FCompE.
rewrite (functor_o N).
rewrite -compA.
rewrite functor_o.
rewrite (compA dorp).
rewrite Hdorp1.
rewrite -(compA _ dorp).
rewrite (compA (M # Join)) -functor_o.
rewrite joinA.
rewrite functor_o.
rewrite -compA (compA (M # Join) dorp).
rewrite -/JOIN.
rewrite -Hdorp4.
by rewrite compA.
Qed.

End dorp.
End Dorp.

Module Swap.
Section swap.
Variables M N : monad.
Variable swap : N \O M ~~> M \O N.
Arguments swap {_}.

Definition JOIN : (M \O N) \O (M \O N) ~~> M \O N :=
  fun A => M # Join \o Join \o M # (@swap (N A)).

Lemma JOINE A : @JOIN A = Join \o M # (M # Join \o swap).
Proof.
rewrite /JOIN.
rewrite natural.
rewrite -(compA Join) FCompE.
by rewrite -(functor_o M).
Qed.

Let prod A := M # (@Monad.Exports.Join N A) \o (@swap _).
Arguments prod {A}.
Let dorp A := Join \o M # (@swap A).
Arguments dorp {A}.

Fact JOIN_prod A : @JOIN A = Join \o M # prod.
Proof. by rewrite JOINE. Qed.

Fact JOIN_dorp A : @JOIN A = M # Join \o dorp.
Proof. by rewrite /dorp. Qed.

Definition swap1 := forall A B (f : A -> B), swap \o N # (M # f) = M # (N # f) \o swap .
Definition swap2 := forall A, @swap A \o Ret _ = M # Ret _ :> (M A -> (M \O N) A).
Definition swap3 := forall A, @swap A \o N # Ret _ = Ret _ :> (N A -> (M \O N) A).
Definition swap4 := forall A, (@prod A) \o N # (@dorp _) = (@dorp _) \o (@prod _).
Hypothesis Hswap1 : swap1.
Hypothesis Hswap2 : swap2.
Hypothesis Hswap3 : swap3.
Hypothesis Hswap4 : swap4.

Lemma prod1 : Prod.prod1 (@prod).
Proof.
move=> A B f; rewrite {1}/prod.
rewrite -compA Hswap1 (compA (M # Join)) -functor_o.
by rewrite -natural functor_o -compA.
Qed.

Lemma prod2 : Prod.prod2 (@prod).
Proof. by move=> A; rewrite /prod -compA Hswap2 -(functor_o M) joinretM functor_id. Qed.

Lemma prod3 : Prod.prod3 (@prod).
Proof.
move=> A; rewrite /prod /Comp.ret.
rewrite (functor_o N) (compA (M # Join \o swap)) -(compA (_ # Join)) Hswap3.
by rewrite (natural Ret) -compA joinMret compfid.
Qed.

Lemma prod4 : Prod.prod4 (@prod).
Proof.
move=> A; rewrite {1}/Prod.JOIN -JOIN_prod JOIN_dorp {1}/prod (functor_o N).
rewrite (compA (M # Join \o swap)) -(compA (_ # Join)) Hswap1.
rewrite (compA (M # Join)) -functor_o joinA functor_o.
rewrite -compA -(compA (_ # Join)) (compA (M # Join) swap) -/prod Hswap4.
by rewrite compA /Prod.JOIN -JOIN_prod JOIN_dorp.
Qed.

Lemma dorp1 : Dorp.dorp1 (@dorp).
Proof.
move=> A B g; rewrite {1}/dorp -compA.
rewrite -(functor_o M).
by rewrite Hswap1 functor_o (compA Join) -natural -compA.
Qed.

Lemma dorp2 : Dorp.dorp2 (@dorp).
Proof.
move=> A; rewrite /dorp /Comp.ret (compA (Join \o M # swap)) -(compA Join).
by rewrite (natural Ret) (compA Join) joinretM compidf Hswap2.
Qed.

Lemma dorp3 : Dorp.dorp3 (@dorp).
Proof.
move=> A; rewrite /dorp -compA.
by rewrite -(functor_o M) Hswap3 joinMret.
Qed.

Lemma dorp4 : Dorp.dorp4 (@dorp).
Proof.
move=> A; rewrite {1}/dorp {1}/Dorp.JOIN -JOIN_dorp JOIN_prod.
rewrite (compA (Join \o M # swap)) -(compA Join).
rewrite (natural Monad.Exports.Join).
rewrite (compA Join Join) -joinA -2!compA FCompE.
rewrite -(functor_o M) -(functor_o M).
by rewrite compA -/dorp -Hswap4 functor_o compA -JOINE JOIN_dorp.
Qed.

Lemma JOIN_naturality : @Natural.P _ _ (JOIN).
Proof. by move=> ?? g; rewrite JOINE -/prod (Prod.JOIN_naturality prod1 g) JOINE. Qed.

Definition JOIN' := Natural.Pack (Natural.Class JOIN_naturality).

Lemma JOIN_ret : JoinLaws.left_unit (@CRet M N) (@JOIN').
Proof.
move=> A.
rewrite [JOIN' _]/=.
rewrite JOINE -/prod.
by rewrite (Prod.JOIN_ret prod1 prod2).
Qed.

Lemma JOIN_fmap_ret : JoinLaws.right_unit (@CRet M N) (@JOIN').
Proof.
move=> A.
rewrite [JOIN' _]/=.
by rewrite JOINE -/prod (Prod.JOIN_fmap_ret prod1 prod3).
Qed.

Lemma JOIN_fmap_JOIN : JoinLaws.associativity (@JOIN').
Proof.
move=> A.
rewrite [JOIN' _]/=.
rewrite [X in _ = _ \o X]/=.
by rewrite !JOINE -!/prod (Prod.JOIN_fmap_JOIN prod1 prod4).
Qed.

End swap.
End Swap.
