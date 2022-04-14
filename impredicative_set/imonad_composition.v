(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2020 monae authors, license: LGPL-2.1-or-later               *)
From mathcomp Require Import all_ssreflect.
From HB Require Import structures.
Require Import imonae_lib ihierarchy imonad_lib.

(******************************************************************************)
(*                          Composing monads                                  *)
(*                                                                            *)
(* formalization of [Jones and Duponcheel, Composing Monads, Yale RR 1993]    *)
(* (Sections 2 and 3)                                                         *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.

Section comp.
Variables (M N : monad).
Definition ret_comp : FId ~~> [the functor of M \o N] := (@ret M) \h (@ret N).
Lemma naturality_ret : naturality FId [the functor of M \o N] ret_comp.
Proof. by move=> A B h; rewrite -(natural ((@ret M) \h (@ret N))). Qed.
HB.instance Definition _ := isNatural.Build
  FId [the functor of (M \o N)] ret_comp naturality_ret.
End comp.
Definition CRet (M N : monad) := [the FId ~> [the functor of M \o N] of ret_comp M N].

Module Prod.
Section prod.
Variables M N(* NB: actually, premonad is enough for N*) : monad.
Variable prod : N \o (M \o N) ~~> M \o N.
Arguments prod {_}.

Definition JOIN : (M \o N) \o (M \o N) ~~> M \o N := fun _ => Join \o M # prod.
Arguments JOIN {_}.

Definition prod1 := forall (A B : UU0) (f : A -> B), prod \o N # ([the functor of M \o N] # f) = [the functor of M \o N] # f \o prod.
Definition prod2 := forall A, prod \o Ret = id :> (_ -> (M \o N) A).
Definition prod3 := forall A, prod \o N # CRet M N _ = Ret :> (_ -> (M \o N) A).
Definition prod4 := forall A, prod \o N # JOIN = JOIN \o prod :> (_ -> (M \o N) A).
Hypothesis Hprod1 : prod1.
Hypothesis Hprod2 : prod2.
Hypothesis Hprod3 : prod3.
Hypothesis Hprod4 : prod4.

Lemma JOIN_naturality : naturality _ _ (@JOIN).
Proof.
move=> A B g; apply/esym; rewrite {1}/JOIN -[in LHS]compA.
transitivity (
  Join \o (M # prod \o M # ([the functor of N \o (M \o N)] # g))).
  by [].
rewrite -functor_o Hprod1.
rewrite functor_o [LHS]compA /JOIN FCompE -(FCompE M M).
rewrite -(natural join).
by rewrite -compA.
Qed.

HB.instance Definition _ := isNatural.Build
  [the functor of (M \o N) \o (M \o N)] [the functor of M \o N] (@JOIN) JOIN_naturality.

Definition JOIN' : [the functor of (M \o N) \o (M \o N)] ~> [the functor of M \o N] :=
  [the nattrans _ _ of @JOIN].

Lemma JOIN_ret : JoinLaws.left_unit (CRet M N) (@JOIN').
Proof.
move=> A; rewrite /JOIN'.
rewrite /=.
rewrite /CRet.
rewrite compA.
rewrite -(compA Join (M # prod) Ret) (natural ret).
by rewrite [LHS]compA (compA Join) joinretM compidf Hprod2.
Qed.

Lemma JOIN_fmap_ret : JoinLaws.right_unit (@CRet M N) (@JOIN').
Proof.
move=> A.
rewrite /JOIN' /=.
rewrite -compA.
rewrite FCompE.
rewrite -(@functor_o M).
by rewrite Hprod3 joinMret.
Qed.

Lemma JOIN_fmap_JOIN : JoinLaws.associativity (@JOIN').
Proof.
move=> A; rewrite {1 2}/JOIN' -[LHS]compA /=.
rewrite -functor_o.
rewrite Hprod4.
rewrite {1}/JOIN.
rewrite -(compA Join (M # prod) prod).
rewrite functor_o.
rewrite [LHS]compA.
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
Variable dorp : M \o (N \o M) ~~> M \o N.
Arguments dorp {_}.

Definition JOIN : (M \o N) \o (M \o N) ~~> M \o N := fun _ => M # Join \o dorp.
Arguments JOIN {_}.

Definition dorp1 := forall (A B : UU0) (f : A -> B), dorp \o [the functor of M \o N] # (M # f) = [the functor of M \o N] # f \o dorp.
Definition dorp2 := forall A, (@dorp A) \o CRet M N _ = M # Ret.
Definition dorp3 := forall A, (@dorp A) \o [the functor of M \o N] # Ret = id.
Definition dorp4 := forall A, (@dorp A) \o JOIN = JOIN \o [the functor of M \o N] # dorp.
Hypothesis Hdorp1 : dorp1.
Hypothesis Hdorp2 : dorp2.
Hypothesis Hdorp3 : dorp3.
Hypothesis Hdorp4 : dorp4.

Lemma join_naturality : naturality _ _ (@JOIN).
Proof.
move=> A B g; apply/esym; rewrite {1}/JOIN -compA Hdorp1.
rewrite [LHS]compA.
rewrite (FCompE M N (N # g)).
rewrite -(@functor_o M).
rewrite -natural.
by rewrite functor_o.
Qed.

HB.instance Definition _ := isNatural.Build
  [the functor of ((M \o N) \o (M \o N))] [the functor of (M \o N)] (@JOIN) join_naturality.

Definition JOIN' : [the functor of (M \o N) \o (M \o N)] ~> [the functor of M \o N] :=
  [the nattrans _ _ of (@JOIN)].

Lemma JOIN_ret : JoinLaws.left_unit (@CRet M N) (@JOIN').
Proof.
move=> A; rewrite /JOIN -[LHS]compA Hdorp2.
rewrite -(@functor_o M).
by rewrite joinretM functor_id.
Qed.

Lemma JOIN_fmap_ret : JoinLaws.right_unit (@CRet M N) (@JOIN').
Proof.
move=> A; rewrite /JOIN /CRet.
rewrite -(compA (M # Join) dorp).
rewrite (@functor_o [the functor of M \o N]).
rewrite (compA dorp) Hdorp3.
rewrite compidf -functor_o.
by rewrite joinMret functor_id.
Qed.

Lemma JOIN_fmap_JOIN : JoinLaws.associativity (@JOIN').
Proof.
move=> A; rewrite {1 2}/JOIN'.
rewrite FCompE.
rewrite (@functor_o N).
rewrite -[LHS]compA.
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
by rewrite [LHS]compA.
Qed.

End dorp.
End Dorp.

Module Swap.
Section swap.
Variables M N : monad.
Variable swap : N \o M ~~> M \o N.
Arguments swap {_}.

Definition JOIN : (M \o N) \o (M \o N) ~~> M \o N :=
  fun A => M # Join \o Join \o M # (@swap (N A)).

Lemma JOINE A : @JOIN A = Join \o M # (M # Join \o swap).
Proof.
rewrite /JOIN.
rewrite natural.
rewrite -(compA Join) FCompE.
by rewrite -(@functor_o M).
Qed.

Let prod A := M # (join A) \o (@swap _).
Arguments prod {A}.
Let dorp A := Join \o M # (@swap A).
Arguments dorp {A}.

Fact JOIN_prod A : @JOIN A = Join \o M # prod.
Proof. by rewrite JOINE. Qed.

Fact JOIN_dorp A : @JOIN A = M # Join \o dorp.
Proof. by rewrite /dorp. Qed.

Definition swap1 := forall (A B : UU0) (f : A -> B), swap \o N # (M # f) = M # (N # f) \o swap .
Definition swap2 := forall A, @swap A \o Ret = M # Ret :> (M A -> (M \o N) A).
Definition swap3 := forall A, @swap A \o N # Ret = Ret :> (N A -> (M \o N) A).
Definition swap4 := forall A, (@prod A) \o N # (@dorp _) = (@dorp _) \o (@prod _).
Hypothesis Hswap1 : swap1.
Hypothesis Hswap2 : swap2.
Hypothesis Hswap3 : swap3.
Hypothesis Hswap4 : swap4.

Lemma prod1 : Prod.prod1 (@prod).
Proof.
move=> A B f; rewrite {1}/prod.
rewrite -[LHS]compA Hswap1 (compA (M # Join)) -functor_o.
by rewrite -natural functor_o -compA.
Qed.

Lemma prod2 : Prod.prod2 (@prod).
Proof.
by move=> A; rewrite /prod -[LHS]compA Hswap2 -(@functor_o M) joinretM functor_id.
Qed.

Lemma prod3 : Prod.prod3 (@prod).
Proof.
move=> A; rewrite /prod /CRet.
rewrite (@functor_o N) (compA (M # Join \o swap)) -(compA (_ # Join)) Hswap3.
by rewrite (natural ret) -[LHS]compA joinMret compfid.
Qed.

Lemma prod4 : Prod.prod4 (@prod).
Proof.
move=> A; rewrite {1}/Prod.JOIN -JOIN_prod JOIN_dorp {1}/prod (@functor_o N).
rewrite (compA (M # Join \o swap)) -(compA (_ # Join)) Hswap1.
rewrite (compA (M # Join)) -functor_o joinA functor_o.
rewrite -[LHS]compA -(compA (_ # Join)) (compA (M # Join) swap) -/prod Hswap4.
by rewrite [LHS]compA /Prod.JOIN -JOIN_prod JOIN_dorp.
Qed.

Lemma dorp1 : Dorp.dorp1 (@dorp).
Proof.
move=> A B g; rewrite {1}/dorp -[LHS]compA.
rewrite -(@functor_o M).
by rewrite Hswap1 functor_o (compA Join) -natural -[LHS]compA.
Qed.

Lemma dorp2 : Dorp.dorp2 (@dorp).
Proof.
move=> A; rewrite /dorp /CRet (compA (Join \o M # swap)) -(compA Join).
by rewrite (natural ret) (compA Join) joinretM compidf Hswap2.
Qed.

Lemma dorp3 : Dorp.dorp3 (@dorp).
Proof.
move=> A; rewrite /dorp -[LHS]compA.
by rewrite -(@functor_o M) Hswap3 joinMret.
Qed.

Lemma dorp4 : Dorp.dorp4 (@dorp).
Proof.
move=> A; rewrite {1}/dorp {1}/Dorp.JOIN -JOIN_dorp JOIN_prod.
rewrite (compA (Join \o M # swap)) -(compA Join).
rewrite (natural join).
rewrite (compA Join Join) -joinA.
rewrite -2![LHS]compA FCompE.
rewrite -(@functor_o M) -(@functor_o M).
rewrite (compA Join (M # swap) prod) -/dorp -Hswap4 functor_o.
by rewrite [LHS]compA -JOINE JOIN_dorp.
Qed.

Lemma JOIN_naturality : @naturality _ _ (JOIN).
Proof. by move=> ?? g; rewrite JOINE -/prod (Prod.JOIN_naturality prod1 g) JOINE. Qed.

HB.instance Definition _ := isNatural.Build
  [the functor of ((M \o N) \o (M \o N))] [the functor of (M \o N)] (@JOIN) JOIN_naturality.

Definition JOIN' : [the functor of (M \o N) \o (M \o N)] ~> [the functor of M \o N] :=
  [the nattrans _ _ of (@JOIN)].

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
Lemma IV : [the functor of idfun \o G] ~> F -> G ~> F.
Proof.
(*case=> m [H]; apply: (@Natural.Pack G F m _).
exact: Natural.Mixin.
Qed.*) Admitted.
Lemma VI : [the functor of G \o idfun] ~> F -> G ~> F.
Proof.
(*case=> m [H]; apply: (@Natural.Pack G F m _).
exact: Natural.Mixin.
Qed.*) Admitted.
Variable K J : functor.
Lemma AV : [the functor of G \o K \o J] ~> F -> [the functor of G \o (K \o J)] ~> F.
Proof.
(*case=> m [H]; apply: (@Natural.Pack (G \O (K \O J)) F m _).
exact: Natural.Mixin.
Qed.*) Admitted.
Lemma AV' : [the functor of G \o (K \o J)] ~> F -> [the functor of G \o K \o J] ~> F.
Proof.
(*case=> m [H]; apply: (@Natural.Pack (G \O K \O J) F m _).
exact: Natural.Mixin.
Qed.*) Admitted.
Lemma VA : F ~> [the functor of G \o K \o J] -> F ~> [the functor of G \o (K \o J)].
Proof.
(*case=> m [H]; apply: (@Natural.Pack F (G \O (K \O J)) m _).
exact: Natural.Mixin.
Qed.*) Admitted.
Lemma VA' : F ~> [the functor of G \o (K \o J)] -> F ~> [the functor of G \o K \o J].
Proof.
(*case=> m [H]; apply: (@Natural.Pack F (G \O K \O J) m _).
exact: Natural.Mixin.
Qed.*) Admitted.
End nattrans_cast_lemmas.

Module DistributiveLaw.
Section distributivelaw.
Variables S T : monad.
Record t := mk {
  f : [the functor of S \o T] ~> [the functor of T \o S] ;
  unit1 : IV (f \v (@ret S \h [the nattrans _ _ of NId T])) =
          VI ([the nattrans _ _ of NId T] \h @ret S) ;
  unit2 : VI (f \v ([the nattrans _ _ of NId S] \h @ret T)) =
          IV (@ret T \h [the nattrans _ _ of NId S]) ;
  multiplication1 :
    AV (f \v (@join S \h [the nattrans _ _ of NId T])) =
    ([the nattrans _ _ of NId T] \h @join S) \v
    VA ((f \h [the nattrans _ _ of NId S]) \v VA' ([the nattrans _ _ of NId S] \h f)) ;
  multiplication2 :
    AV' (f \v ([the nattrans _ _ of NId S] \h @join T)) =
    (@join T \h [the nattrans _ _ of NId S]) \v
    VA' (([the nattrans _ _ of NId T] \h f) \v VA (f \h [the nattrans _ _ of NId T]))
}.
End distributivelaw.
End DistributiveLaw.
Coercion DistributiveLaw.f : DistributiveLaw.t >-> nattrans.

(* TODO *)
Definition beck (S T : monad) (f : DistributiveLaw.t S T) : monad.
have @join : [the functor of (T \o S) \o (T \o S)] ~> [the functor of T \o S].
  apply: (VComp ((@join T) \h (@join S)) _).
  apply VA.
  apply AV.
  apply HComp.
(*  exact: NId.*)admit.
  apply VA'.
  apply AV'.
  apply HComp.
  exact: f.
(*  exact: NId.*) admit.
apply: (Monad.Pack (Monad.Class (isMonad.Axioms_ (CRet T S) join _ _ _ _ _ _))).
move=> A.
rewrite /join.
Abort.
