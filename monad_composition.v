From mathcomp Require Import all_ssreflect.
Require Import monae_lib monad.

(* jones and duponcheel, composing monads, sect 2, 3 *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Comp.
Section comp.
Variables (M N : monad).
Lemma naturality_ret : naturality FId (M \O N) ((@RET M) \h (@RET N)).
Proof. by move=> A B h; rewrite -(natural ((@RET M) \h (@RET N))). Qed.
Definition ret : FId ~> M \O N := Natural.Pack naturality_ret.
End comp.
End Comp.
Notation CRet := (Comp.ret).

Module Prod.
Section prod.
Variables M N(* NB: actually, premonad is enough for N*) : monad.
Variable prod : N \O (M \O N) ~~> M \O N.
Arguments prod {_}.

Definition JOIN : (M \O N) \O (M \O N) ~~> M \O N := fun _ => Join \o M # prod.
Arguments JOIN {_}.

Definition prod1 := forall A B (f : A -> B), prod \o N # ((M \O N) # f) = (M \O N) # f \o prod.
Definition prod2 := forall A, prod \o Ret = id :> (_ -> (M \O N) A).
Definition prod3 := forall A, prod \o N # CRet M N _ = Ret :> (_ -> (M \O N) A).
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
rewrite -(natural Monad.Exports.JOIN).
by rewrite -compA.
Qed.

Definition JOIN' : (M \O N) \O (M \O N) ~> M \O N :=
  @Natural.Pack _ _ _ JOIN_naturality.

Lemma JOIN_ret : JoinLaws.left_unit (@CRet M N) (@JOIN').
Proof.
move=> A; rewrite /JOIN'.
rewrite /=.
rewrite /CRet.
rewrite compA.
rewrite -(compA Join (M # prod) Ret) (natural RET).
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
Definition dorp2 := forall A, (@dorp A) \o CRet M N _ = M # Ret.
Definition dorp3 := forall A, (@dorp A) \o (M \O N) # Ret = id.
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

Definition JOIN' := Natural.Pack join_naturality.

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

Let prod A := M # (@Monad.Exports.JOIN _ A) \o (@swap _).
Arguments prod {A}.
Let dorp A := Join \o M # (@swap A).
Arguments dorp {A}.

Fact JOIN_prod A : @JOIN A = Join \o M # prod.
Proof. by rewrite JOINE. Qed.

Fact JOIN_dorp A : @JOIN A = M # Join \o dorp.
Proof. by rewrite /dorp. Qed.

Definition swap1 := forall A B (f : A -> B), swap \o N # (M # f) = M # (N # f) \o swap .
Definition swap2 := forall A, @swap A \o Ret = M # Ret :> (M A -> (M \O N) A).
Definition swap3 := forall A, @swap A \o N # Ret = Ret :> (N A -> (M \O N) A).
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
by rewrite (natural RET) -compA joinMret compfid.
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
by rewrite (natural RET) (compA Join) joinretM compidf Hswap2.
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
rewrite (natural Monad.Exports.JOIN).
rewrite (compA Join Join) -joinA -2!compA FCompE.
rewrite -(functor_o M) -(functor_o M).
by rewrite compA -/dorp -Hswap4 functor_o compA -JOINE JOIN_dorp.
Qed.

Lemma JOIN_naturality : @Natural.P _ _ (JOIN).
Proof. by move=> ?? g; rewrite JOINE -/prod (Prod.JOIN_naturality prod1 g) JOINE. Qed.

Definition JOIN' := Natural.Pack JOIN_naturality.

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

(* wip *)

Section nattrans_cast_lemmas.
Variables (F G : functor).
Lemma IV : FId \O G ~> F -> G ~> F.
Proof. case=> m H; apply: (@Natural.Pack G F m H). Qed.
Lemma VI : G \O FId ~> F -> G ~> F.
Proof. case=> m H; apply: (@Natural.Pack G F m H). Qed.
Variable K J : functor.
Lemma AV : G \O K \O J ~> F -> G \O (K \O J) ~> F.
Proof. case=> m H; apply: (@Natural.Pack (G \O (K \O J)) F m H). Qed.
Lemma AV' : G \O (K \O J) ~> F -> G \O K \O J ~> F.
Proof. case=> m H; apply: (@Natural.Pack (G \O K \O J) F m H). Qed.
Lemma VA : F ~> G \O K \O J -> F ~> G \O (K \O J).
Proof. case=> m H; apply: (@Natural.Pack F (G \O (K \O J)) m H). Qed.
Lemma VA' : F ~> G \O (K \O J) -> F ~> G \O K \O J.
Proof. case=> m H; apply: (@Natural.Pack F (G \O K \O J) m H). Qed.
End nattrans_cast_lemmas.

Module DistributiveLaw.
Section distributivelaw.
Variables S T : monad.
Record t := mk {
  f : S \O T ~> T \O S ;
  unit1 : IV (f \v (@RET S \h NId T)) = VI (NId T \h @RET S) ;
  unit2 : VI (f \v (NId S \h @RET T)) = IV (@RET T \h NId S) ;
  multiplication1 :
    AV (f \v (@JOIN S \h NId T)) =
    (NId T \h @JOIN S) \v VA ((f \h NId S) \v VA' (NId S \h f)) ;
  multiplication2 :
    AV' (f \v (NId S \h @JOIN T)) =
    (@JOIN T \h NId S) \v VA' ((NId T \h f) \v VA (f \h NId T))
}.
End distributivelaw.
End DistributiveLaw.
Coercion DistributiveLaw.f : DistributiveLaw.t >-> Natural.t.

(* TODO *)
Definition beck (S T : monad) (f : DistributiveLaw.t S T) : monad.
have @join : (T \O S) \O (T \O S) ~> T \O S.
  apply: (VComp ((@JOIN T) \h (@JOIN S)) _).
  apply VA.
  apply AV.
  apply HComp.
  exact: NId.
  apply VA'.
  apply AV'.
  apply HComp.
  exact: f.
  exact: NId.
apply: (Monad.Pack (@Monad.Class _ _ (@Monad.Mixin _ (Comp.ret T S) join _ _ _))).
move=> A.
rewrite /join.
Abort.
