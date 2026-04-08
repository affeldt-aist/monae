From mathcomp Require Import ssreflect ssrfun.
Require Import monad_lib hierarchy.
From HB Require Import structures.

Local Open Scope monae_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module FreerMonadMod.
  Section freer.

    Variable F : UU0 -> UU0.

    Inductive Freer (X : UU0) :=
    | Pure : X -> Freer X
    | Impure : forall Y, F Y -> (Y -> Freer X) -> Freer X
    .

    Definition acto := fun X : UU0 => Freer X.

    Local Notation M := acto.

    Let ret : idfun ~~> M := fun _ x => Pure x.

    Local Fixpoint bind [A B : UU0] (m : M A) (f : A -> M B) := 
    match m with 
    | Pure x => f x
    | Impure Y fy k => Impure fy (fun y => bind (k y) f)
    end.

  Let left_neutral: BindLaws.left_neutral bind ret .
  Proof.
    rewrite /BindLaws.left_neutral.
     by [].
  Qed.

  Let right_neutral : BindLaws.right_neutral bind ret.
  Proof.
    move=>/=A.
    elim=>[x|Y fy k IHm]//=.
    congr Impure;
    exact/boolp.funext.
  Qed.

Let assoc : BindLaws.associative bind.
Proof.
    move=>/=A B C m f g.
    elim:m=>//=Y fy k IHm.
    congr Impure;
    exact/boolp.funext.
Qed.

HB.instance Definition _ :=
  isMonad_ret_bind.Build M left_neutral right_neutral assoc.

  End freer.

End FreerMonadMod.

HB.export FreerMonadMod.

Module FreerMod.
Section freer.

Variable F : UU0 -> UU0.

Local Notation M := (acto F).

Let trigger : F ~~> M := fun X fx => Impure fx (fun x => Pure F x).

Local Fixpoint denote {cm : monad} (denote_effect : F ~~> cm) (X : UU0) (m : M X):cm X:=
match m with 
| Pure x => Ret x
| Impure Y fy k => denote_effect Y fy >>= fun y => denote denote_effect (k y)
end. 

Let denote_ret : forall (cm : monad) (denote_effect : F ~~> cm) X (x : X),
        denote denote_effect (Ret x) = Ret x.
Proof.
  by [].
Qed.

Let denote_bind (cm : monad) (denote_effect : F ~~> cm) X Y m (f : X -> M Y) : 
        denote denote_effect (m >>= f) = ( denote denote_effect m) >>= (fun x => denote denote_effect (f x)) .
Proof.
    elim:m=>[x | Z fz k]/=.
    - by rewrite !bindretf.
    rewrite bindA=>H.
    congr bind;
    exact/boolp.funext/H.
Qed.

Let denote_trigger : forall (cm : monad) (denote_effect : F ~~> cm) X (fx : F X), 
        denote denote_effect (trigger fx) = denote_effect X fx.
Proof.
    move=>cm denote_effect X fx /=.
    by rewrite bindmret.
Qed.

Let denote_unique : forall (cm : monad) (denote_effect : F ~~> cm) (denote' : M ~~> cm),
            (forall X (x : X), denote' X (ret X x) = @hierarchy.ret cm X x) ->
            (forall X Y (m : M X) (f : X -> M Y), denote' Y (m >>= f) = (denote' X m) >>= (fun x => denote' Y (f x))) ->
            (forall X (fx : F X), (denote' X (trigger fx)) = denote_effect X fx) ->
        forall X (m : M X), denote' X m = denote denote_effect m.
Proof.
    move=>cm denote_effect denote' dret' dbind' dtrigger' X m.
    rewrite/denote.
    elim:m=>[x| Y fy k Hy]/=.
    - exact/dret'.
    by under [in RHS]eq_bind do rewrite -Hy;
      rewrite -dtrigger'-dbind'.
Qed.

HB.instance Definition _ := isFreerMonad.Build F M 
  denote_ret 
  denote_bind 
  denote_trigger
  denote_unique.

    End freer.
End FreerMod.

HB.export FreerMod.

Lemma denote_if : forall (F : UU0 -> UU0) (M : freerMonad F) (cm : monad) (denote_effect : F ~~> cm) X (m m' : M X) b, 
        denote cm denote_effect X (if b then m else m') = if b then ( denote cm denote_effect X m) else ( denote cm denote_effect X m').
Proof.
    by move=>? ? ? ? ? ? ?; case.
Qed.

HB.export denote_if.
