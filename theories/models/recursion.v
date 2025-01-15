From mathcomp Require Import all_ssreflect.
From HB Require Import structures.
Require Import hierarchy.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.
Local Open Scope do_notation.

Section fixop.
Variable M : delayExceptMonad.

Definition f_iter_body A B (a : A)(F : (A -> M B) -> A -> M B) :=
  catch ((F (fun a => fail) a) >>= (Ret \o inl)) (Ret (inr (fun f => F (F f)))).
Check f_iter_body.

Definition fixop A B (F : (A -> M B) -> A -> M B) :=
  fun (a : A) => while (f_iter_body a) F.

Section example.
Let factrial_def :=
  fun (f : _ -> M _) n =>
    if n is m.+1 then do k <- f m; Ret (k * n)
                 else Ret 1.
Definition factorial := fixop factrial_def.

End example.
End fixop.
