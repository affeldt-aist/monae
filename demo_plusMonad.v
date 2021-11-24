From mathcomp Require Import all_ssreflect.
From mathcomp Require boolp.
Require Import monae_lib hierarchy monad_lib fail_lib example_quicksort.
From infotheo Require Import ssr_ext.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope order_scope.
Import Order.TTheory.
Close Scope do_notation.
Local Open Scope mprog.
Local Open Scope monae_scope.
Local Open Scope tuple_ext_scope.

Section specificationDemo.
Variable M : plusMonad.

(* perm *)
Example perm1 : (@qperm M nat [::]) = Ret [::].
rewrite qperm_nil. done. Qed.
Example perm2 : (@qperm M nat [:: 1]%N) = Ret [:: 1]%N.
rewrite qperm_cons /=.
rewrite bindretf.
rewrite qperm_nil.
rewrite /liftM2.
rewrite bindretf.
rewrite bindretf.
rewrite /=. done. Qed.
Example perm3 : (@qperm M nat [:: 2; 1]%N) = Ret [:: 1; 2]%N [~] Ret [:: 2; 1]%N.
rewrite qpermE !bindA bindretf alt_bindDl bindretf /liftM2.
by repeat rewrite !qpermE !bindA bindretf !bindretf /=. Qed.
Example perm4 : (@qperm M nat [:: 3; 2; 1]%N) = Ret [:: 1; 2; 3]%N [~] Ret [:: 1; 3; 2]%N [~]
                                                Ret [:: 2; 1; 3]%N [~] Ret [:: 2; 3; 1]%N [~]
                                                Ret [:: 3; 1; 2]%N [~] Ret [:: 3; 2; 1]%N.
rewrite qpermE !bindA.
repeat rewrite bindretf alt_bindDl.
rewrite bindretf /liftM2.
repeat rewrite !qpermE /= !bindA !bindretf !alt_bindDl !bindretf /= !/liftM2.
repeat rewrite !qpermE !bindA bindretf !bindretf /=.
rewrite -altA altACA !altA //. Qed.

(* split *)
Example split1 : (@splits M nat [::]) = Ret ([::], [::]).
by []. Qed.
Example split2 : (@splits M nat [:: 1; 2]%N) =
  Ret ([:: 1; 2]%N, [::]%N) [~] Ret ([:: 2]%N, [:: 1]%N) [~]
  Ret ([:: 1]%N, [:: 2]%N) [~] Ret ([::]%N, [:: 1; 2]%N).
Proof.
rewrite /splits bindA.
repeat rewrite bindretf alt_bindDl !bindretf.
by rewrite altA.
Qed.

(* sorted *)
Example sorted1 : (@sorted nat (<=%O) [::]%N) = true.
by []. Qed.
Example sorted2 : (@sorted nat (<=%O) [:: 1; 2; 3; 4]%N) = true.
Proof.
rewrite /sorted.
rewrite /path.
rewrite /= //. Qed.
Example sorted3 : (@sorted nat (<=%O) [:: 1; 2; 4; 3]%N) = false.
Proof.
rewrite /sorted /path.
rewrite /= //. Qed.

(* filt *)
Example filt1 : (@assert M _ (sorted <=%O)) [:: 1; 2; 3]%N = Ret ([:: 1; 2; 3]%N).
rewrite /assert /guard /sorted /path /=; unlock.
rewrite bindskipf //. Qed.
Example filt2 : (@assert M _ (sorted (<=%O))) [:: 2; 1; 3]%N = fail.
rewrite /sorted /assert /guard /path /=; unlock.
rewrite bindfailf //. Qed.

Variables (d : unit) (T : porderType d).
(* slowsort *)
Definition bindskipE := (bindskipf, bindmskip).
(* Definition bindfailE := (bindfailf, bindmfail).
Definition altfailE := (altfailm, altmfail). *)

Ltac sub := repeat rewrite !alt_bindDl !bindretf; rewrite bindA; repeat rewrite !qpermE !bindA !bindretf /=.
Ltac bindSF := rewrite !bindskipf !bindfailf.
Ltac slowsort_process :=
  rewrite /slowsort kleisliE;
  rewrite !qpermE /bindA /= !bindretf;
  repeat sub;
  rewrite /sorted /assert /guard /path /=; unlock;
  (* repeat rewrite bindfailE; *)
  repeat rewrite bindskipE.
  (* repeat rewrite altfailE. *)

Example slowsort0 : (@slowsort M _ T [::]) = Ret [::].
by slowsort_process.
Qed.

(* Example slowsort1 : (@slowsort M _ _ [:: 1; 2]%N) = Ret [:: 1; 2]%N.
by slowsort_process.
Qed. *)

Example slowsort2 : (@slowsort M _ _ [:: 2; 1]%N) = Ret [:: 1; 2]%N.
(* by slowsort_process. *)
rewrite /slowsort kleisliE.
rewrite !qpermE /bindA /= !bindretf.
repeat sub.
rewrite /sorted /assert /guard /path /=; unlock.
bindSF.
rewrite altmfail.
done.
Qed.
End specificationDemo.

Section monadDemo.
Variable M : monad.

Definition ret : nat -> M nat :=
    fun n => Ret n.
Definition func : nat -> M nat :=
    fun n => Ret (n+1).
Example bind1 : ret 1 >>= ret = ret 1.
rewrite /ret bindretf. done. Qed.
Example __ : ret 1 >>= func = ret 2.
rewrite /ret /func bindretf. done. Qed.

End monadDemo.

Section plusMonadDemo.
    Variable M : plusMonad.
    Variable A : UU0.

Example alt1 : @fail M _ [~] @fail M _ = fail :> M A.
Proof. by rewrite altfailm. Qed.
Example alt2 : @fail M _ [~] @ret M 1 = @ret M 1 :> M nat.
Proof. by rewrite altfailm. Qed.

End plusMonadDemo.
