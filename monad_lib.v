Ltac typeof X := type of X.

Require Import ssrmatching.
From mathcomp Require Import all_ssreflect.
From mathcomp Require boolp.
Require Import monae_lib hierarchy.

(******************************************************************************)
(*  Properties and examples of functors, natural transformations, and monads  *)
(*                                                                            *)
(*                    s \h g == horizontal composition                        *)
(*                    F ## n == application of functor F to natural           *)
(*                              transformation n                              *)
(*                    F -| G == adjoint functors                              *)
(*   Module monad_of_adjoint == derivation of a monad from an adjunction      *)
(* Section composite_adjoint == composition of adjunctions                    *)
(*            E.-operation M == sigma operation                               *)
(*  Module Monad_of_ret_bind == construction of a monad from ret and bind     *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "A `2" (format "A `2", at level 3).
Reserved Notation "f ^`2" (format "f ^`2", at level 3).
Reserved Notation "F ## g" (at level 11).
Reserved Notation "E .-operation M" (at level 2, format "E  .-operation  M").

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.

Definition Squaring (A : Type) := (A * A)%type.
Notation "A `2" := (Squaring A).
Definition squaring_f (A B : Type) (f : A -> B) : A`2 -> B`2 := fun x => (f x.1, f x.2).
Lemma squaring_f_id : FunctorLaws.id squaring_f.
Proof. by move=> A /=; rewrite boolp.funeqE => -[x1 x2]. Qed.
Lemma squaring_f_comp : FunctorLaws.comp squaring_f.
Proof. by move=> A B C g h /=; rewrite boolp.funeqE => -[x1 x2]. Qed.
Definition squaring : functor :=
  Functor.Pack (Functor.Mixin squaring_f_id squaring_f_comp).
Notation "f ^`2" := (squaring # f).
Lemma squaringE (A B : Type) (f : A -> B) x : (f ^`2) x = (f x.1, f x.2).
Proof. by []. Qed.

Section curry_functor.
Definition curry_M (X : Type) : Type -> Type := fun B => (X * B)%type.
Definition curry_f (X A B : Type) (f : A -> B) : curry_M X A -> curry_M X B :=
  fun x : X * A => (x.1, f x.2).
Lemma curry_f_id X : FunctorLaws.id (@curry_f X).
Proof.
by rewrite /FunctorLaws.id => A; rewrite /curry_f boolp.funeqE; case.
Qed.
Lemma curry_f_comp X : FunctorLaws.comp (@curry_f X).
Proof.
by rewrite /FunctorLaws.comp => A B C g h; rewrite /curry_f boolp.funeqE; case.
Qed.
Definition curry_F X : functor :=
  Functor.Pack (Functor.Mixin (curry_f_id X) (curry_f_comp X)).
End curry_functor.

Section uncurry_functor.
Definition uncurry_M (X : Type) : Type -> Type := fun B => X -> B.
Definition uncurry_f (X A B : Type) (f : A -> B) : uncurry_M X A -> uncurry_M X B :=
  fun g : X -> A => f \o g.
Lemma uncurry_f_id X : FunctorLaws.id (@uncurry_f X).
Proof.
rewrite /FunctorLaws.id => A; rewrite /uncurry_f boolp.funeqE => ?.
by rewrite compidf.
Qed.
Lemma uncurry_f_comp X : FunctorLaws.comp (@uncurry_f X).
Proof.
rewrite /FunctorLaws.comp => A B C g h; rewrite /uncurry_f boolp.funeqE => ?.
by rewrite compE compA.
Qed.
Definition uncurry_F X : functor :=
  Functor.Pack (Functor.Mixin (uncurry_f_id X) (uncurry_f_comp X)).
End uncurry_functor.

Section exponential_functor.
Variable A : Type.
Definition exponential_M (X : Type) := A -> X.
Definition exponential_f (X Y : Type) (f : X -> Y) :
  exponential_M X -> exponential_M Y := fun e => f \o e.
Lemma exponential_f_id : FunctorLaws.id exponential_f. Proof. by []. Qed.
Lemma exponential_f_comp : FunctorLaws.comp exponential_f.
Proof. by []. Qed.
Definition exponential_F : functor :=
  Functor.Pack (Functor.Mixin exponential_f_id exponential_f_comp).
End exponential_functor.

Lemma fmap_oE (M : functor) (A B C : Type) (f : A -> B) (g : C -> A) (m : M C) :
  (M # (f \o g)) m = (M # f) ((M # g) m).
Proof. by rewrite functor_o. Qed.

Section id_natural_transformation.
Variables C : functor.
Definition natural_id : naturality _ _ (fun A => @id (C A)). Proof. by []. Qed.
Definition NId : C ~> C := Natural.Pack (Natural.Mixin natural_id).
End id_natural_transformation.

Section vertical_composition.
Variables C D E : functor.
Variables (g : D ~> E) (f : C ~> D).
Definition ntcomp := fun A => g A \o f A.
Definition natural_vcomp : naturality _ _ ntcomp.
Proof. by move=> A B h; rewrite compA (natural g) -compA (natural f). Qed.
Definition VComp : C ~> E := Natural.Pack (Natural.Mixin natural_vcomp).
End vertical_composition.

Notation "f \v g" := (VComp f g).

Lemma vassoc (F1 F2 G H : functor) (f : F1 ~> F2) (g : G ~> F1) (h : H ~> G) :
  f \v g \v h = f \v (g \v h).
Proof. by apply nattrans_ext => a /=. Qed.

Lemma vcompE (F G H : functor) (n1 : F ~> H) (n2 : G ~> F) X :
  (n1 \v n2) X = n1 X \o n2 X.
Proof. by []. Qed.

Section horizontal_composition.
Variables (F G F' G' : functor) (s : F ~> G) (t : F' ~> G').
Lemma natural_hcomp :
  naturality (F' \O F) (G' \O G) (fun A => @t (G A) \o F' # (@s A)).
Proof.
move=> A B h; rewrite compA (natural t) -compA -[in RHS]compA.
by congr (_ \o _); rewrite FCompE -2!functor_o (natural s).
Qed.
Definition HComp : (F' \O F) ~> (G' \O G) := Natural.Pack (Natural.Mixin natural_hcomp).
End horizontal_composition.

Notation "f \h g" := (HComp g f).

Section functor_natural_transformation.
Variables (S F G : functor) (nt : F ~> G).
Definition fun_app_nt : S \O F ~~> S \O G :=
  fun (A : Type) => S # (nt A).
Lemma natural_fun_app_nt : naturality (S \O F) (S \O G) fun_app_nt.
Proof.
by move=> *; rewrite /fun_app_nt 2!FCompE -2!(functor_o S) natural.
Qed.
Definition functor_app_natural : (S \O F) ~> (S \O G) :=
  Natural.Pack (Natural.Mixin natural_fun_app_nt).
End functor_natural_transformation.
Arguments functor_app_natural S {_} {_}.
Notation "F '##' g" := (functor_app_natural F g).

Lemma functor_app_naturalE (S F G : functor) (nt : F ~> G) X :
  (S ## nt) X = S # nt X.
Proof. by []. Qed.

Lemma functor_app_natural_hcomp (S F G : functor) (nt : F ~> G) :
  S ## nt = NId S \h nt.
Proof. by apply nattrans_ext => a; rewrite functor_app_naturalE. Qed.

Section natural_transformation_example.
Definition fork' : FId ~~> squaring := fun A (a : A) => (a, a).
Lemma fork_natural : naturality _ _ fork'. Proof. by []. Qed.
Definition fork : FId ~> squaring := Natural.Pack (Natural.Mixin fork_natural).
End natural_transformation_example.

Definition eta_type (f g : functor) := FId ~> g \O f.
Definition eps_type (f g : functor) := f \O g ~> FId.
Module TriangularLaws.
Section triangularlaws.
Variables (F G : functor).
Variables (eps : eps_type F G) (eta : eta_type F G).
Definition left := forall A, @eps (F A) \o (F # @eta A) = @id (F A).
Definition right := forall A, (G # @eps A) \o @eta (G A) = @id (G A).
End triangularlaws.
End TriangularLaws.

Module AdjointFunctor.
Section adjointfunctor.
Variables F G : functor.
Record t := mk {
  eta : eta_type F G ;
(*  nat_eta : naturality _ _ eta ;*)
  eps : eps_type F G ;
(*  nat_eps : naturality _ _ eps ;*)
  tri_left : TriangularLaws.left eps eta ;
  tri_right : TriangularLaws.right eps eta}.
End adjointfunctor.
Section lemmas.
Variables (F G : functor) (H : t F G).
Definition hom_iso (A B : Type) (h : F A -> B) : A -> G B := (G # h) \o @eta _ _ H A.
Definition hom_inv (A B : Type) (h : A -> G B) : F A -> B := @eps _ _ H B \o (F # h).
End lemmas.
End AdjointFunctor.
Arguments AdjointFunctor.t : clear implicits.

Notation "F -| G" := (AdjointFunctor.t F G).

Section adjoint_example.
Variable (X : Type).
Lemma curry_naturality :
  naturality (curry_F X \O uncurry_F X) FId (fun A (af : X * (X -> A)) => af.2 af.1).
Proof. by []. Qed.
Definition curry_eps : eps_type (curry_F X) (uncurry_F X) := Natural.Pack (Natural.Mixin curry_naturality).
Lemma curry_naturality2 :
  naturality FId (uncurry_F X \O curry_F X) (fun (A : Type) (a : A) => pair^~ a).
Proof. by []. Qed.
Definition curry_eta : eta_type (curry_F X) (uncurry_F X) := Natural.Pack (Natural.Mixin curry_naturality2).
Lemma adjoint_currry : curry_F X -| uncurry_F X.
Proof.
apply: (@AdjointFunctor.mk _ _ curry_eta curry_eps).
by move=> A; rewrite /TriangularLaws.left boolp.funeqE; case.
move=> A; rewrite /TriangularLaws.right /uncurry_F /curry_eps /curry_eta /uncurry_M.
by rewrite /= /uncurry_f /= /comp /= boolp.funeqE => f; rewrite boolp.funeqE.
Qed.
End adjoint_example.

Module monad_of_adjoint.
Section def.
Variables (F G : functor) (eps : eps_type F G) (eta : eta_type F G).
Definition M := G \O F.
Definition mu : M \O M ~~> M := fun A => G # (@eps (F A)).
Definition bind A B (m : M A) (f : A -> M B) : M B := mu ((M # f) m).
End def.
Section prop.
Variables (f g : functor).
Hypothesis Had : f -| g.
Let eps : eps_type f g := AdjointFunctor.eps Had.
Let eta : eta_type f g := AdjointFunctor.eta Had.
Section mu_eps_natural.
Notation M := (M f g).
Notation mu := (mu eps).
Lemma muM_natural : naturality _ _ mu.
Proof.  move => A B h.
rewrite (_ : (M \O M) # h = g # ((f \O g) # (f # h))) //.
rewrite (_ : _ \o g # ((f \O g) # (f # h)) =
  g # (@eps (f B) \o ((f \O g) # (f # h)))); last by rewrite -functor_o.
by rewrite -natural FIdf FCompE functor_o.
Qed.
Lemma epsC A : @eps _ \o @eps _ = @eps _ \o f # (g # (@eps _)) :> ((f \o g) ((f \o g) A) -> A).
Proof. by rewrite -natural. Qed.
Lemma muMA A : @mu A \o @mu (M A) = @mu A \o (M # @mu A).
Proof.
have -> : g # @eps (f A) \o g # @eps (f (M A)) =
  g # (@eps (f A) \o @eps (f (M A))) by rewrite functor_o.
by rewrite epsC functor_o.
Qed.
End mu_eps_natural.
Lemma bindetaf : BindLaws.left_neutral (bind eps) eta.
Proof.
rewrite /BindLaws.left_neutral => A B a h.
rewrite /bind /mu.
rewrite -(compE ((g \O f) # h)) (natural eta) -(compE (g # _)) compA.
by rewrite AdjointFunctor.tri_right.
Qed.
Lemma bindmeta : BindLaws.right_neutral (bind eps) eta.
Proof.
rewrite /BindLaws.right_neutral => A m.
rewrite /bind /mu -(compE (g # _)).
by rewrite -functor_o AdjointFunctor.tri_left functor_id.
Qed.
Lemma law3 : BindLaws.associative (bind eps).
Proof.
rewrite /BindLaws.associative => A B C x ab bc.
rewrite /bind.
set N := M f g.  set j := mu eps.
rewrite [X in _ = j C X](_ : _ = (N # (j C)) ((N # (N # bc)) ((N # ab) x))); last first.
  rewrite functor_o /comp.
  congr (N # j C).
  by rewrite functor_o.
move: muMA (muM_natural bc).
rewrite -/N -/j.
move=> muMA.
rewrite FCompE.
have -> : (N # bc) (j B ((N # ab) x)) = (N # bc \o j B) ((N # ab) x) by [].
move=> ->.
rewrite compE.
rewrite [LHS](_ : _ = (j C \o j (N C)) ((N # (N # bc)) ((N # ab) x))) //.
by rewrite muMA.
Qed.
End prop.
End monad_of_adjoint.

Section composite_adjoint.
Variables (F0 U0 : functor).
Hypothesis H0 : F0 -| U0.
Let eta0 : eta_type F0 U0 := AdjointFunctor.eta H0.
Let eps0 : eps_type F0 U0 := AdjointFunctor.eps H0.
Variables (F U : functor).
Hypothesis H : F -| U.
Let eta : eta_type F U := AdjointFunctor.eta H.
Let eps : eps_type F U := AdjointFunctor.eps H.

Lemma uni_naturality :
  naturality FId ((U0 \O U) \O (F \O F0)) (fun A : Type => U0 # eta (F0 A) \o eta0 A).
Proof.
move=> A B h; rewrite FIdf.
rewrite -[in RHS]compA -[in RHS](natural (AdjointFunctor.eta H0)) compA [in RHS]compA.
congr (_ \o _).
rewrite (FCompE U0 F0).  rewrite -[in RHS](functor_o U0).
rewrite -[in LHS](functor_o U0).
congr (_ # _).
by rewrite -(natural (AdjointFunctor.eta H)).
Qed.

Let uni : @eta_type (F \O F0) (U0 \O U) := Natural.Pack (Natural.Mixin uni_naturality).

Lemma couni_naturality :
  naturality ((F \O F0) \O (U0 \O U)) FId (fun A : Type => eps A \o F # eps0 (U A)).
Proof.
move=> A B h.
rewrite [in LHS]compA {}(natural (AdjointFunctor.eps H)) -compA.
rewrite -[in RHS]compA; congr (_ \o _).
rewrite [in LHS]FCompE -[in LHS](functor_o F) [in LHS](natural (AdjointFunctor.eps H0)).
by rewrite -[in RHS](functor_o F).
Qed.

Let couni : @eps_type (F \O F0) (U0 \O U) := Natural.Pack (Natural.Mixin couni_naturality).

Lemma composite_adjoint : F \O F0 -| U0 \O U.
Proof.
apply: (@AdjointFunctor.mk _ _ uni couni).
rewrite /TriangularLaws.left => A.
rewrite /couni /uni /=.
rewrite FCompE -compA -functor_o.
rewrite (_ : @eps0 _ \o F0 # _ = @eta (F0 A)); first exact: (AdjointFunctor.tri_left H).
rewrite functor_o compA -FCompE.
by rewrite -(natural (AdjointFunctor.eps H0)) /= FIdf -compA (AdjointFunctor.tri_left H0) compfid.
rewrite /TriangularLaws.right => A.
rewrite /couni /uni /=.
rewrite compA -[RHS](AdjointFunctor.tri_right H0 (U A)); congr (_ \o _).
rewrite FCompE -functor_o; congr (_ # _).
rewrite functor_o -compA -FCompE.
by rewrite (natural (AdjointFunctor.eta H)) FIdf compA (AdjointFunctor.tri_right H) compidf.
Qed.

End composite_adjoint.

Definition operation (E : functor) (M : monad) := E \O M ~> M.
Notation "E .-operation M" := (operation E M).

Module Monad_of_ret_bind.
Section monad_of_ret_bind.
Variable M : functor.
Variable ret : FId ~> M.
Variable bind : forall (A B : Type), M A -> (A -> M B) -> M B.
Hypothesis bindretf : BindLaws.left_neutral bind ret.
Hypothesis bindmret : BindLaws.right_neutral bind ret.
Hypothesis bindA : BindLaws.associative bind.

Definition Map (A B : Type) (f : A -> B) (m : M A) := bind m (@ret B \o f).
Lemma Map_id : FunctorLaws.id Map.
Proof. by move=> A; rewrite boolp.funeqE => m; rewrite /Map bindmret. Qed.
Lemma Map_o : FunctorLaws.comp Map.
Proof.
move=> A B C g h; rewrite boolp.funeqE => m.
rewrite /Map compE bindA; congr bind.
by rewrite boolp.funeqE => a; rewrite bindretf.
Qed.
Definition functor_mixin := Functor.Mixin Map_id Map_o.
Let M' := Functor.Pack functor_mixin.

Lemma MapE (A B : Type) (f : A -> B) m : (M' # f) m = bind m (ret B \o f).
Proof. by []. Qed.

Lemma naturality_ret : naturality FId M' ret.
Proof.
move=> A B h; rewrite FIdf boolp.funeqE => ?.
by rewrite compE /= /Map MapE /= bindretf.
Qed.

Let ret' : FId ~> M' := Natural.Pack (Natural.Mixin naturality_ret).

Let bind_Map (A B C : Type) (f : A -> B) (m : M A) (g : B -> M C) :
  bind (Map f m) g = bind m (g \o f).
Proof.
rewrite /Map bindA; congr bind; by rewrite boolp.funeqE => ?; rewrite bindretf.
Qed.

Lemma naturality_join : naturality (M' \O M') M' (fun A : Type => (bind (B:=A))^~ id).
Proof.
move=> A B h; rewrite boolp.funeqE => mma.
by rewrite /Actm 2!compE /Map bind_Map [in LHS]bindA.
Qed.

Definition join : M' \O M' ~> M' := Natural.Pack (Natural.Mixin naturality_join).

Let bindE (A B : Type) m (f : A -> M' B) : bind m f = join _ ((M' # f) m).
Proof. by rewrite /join /= bind_Map. Qed.

Lemma joinretM : JoinLaws.left_unit ret' join.
Proof.
rewrite /join => A; rewrite boolp.funeqE => ma /=.
by rewrite bindretf. Qed.

Lemma joinMret : JoinLaws.right_unit ret' join.
Proof.
rewrite /join => A; rewrite boolp.funeqE => ma /=.
by rewrite bind_Map compidf bindmret.
Qed.

Lemma joinA : JoinLaws.associativity join.
Proof.
move=> A; rewrite boolp.funeqE => mmma.
by rewrite /join /= bind_Map compidf bindA.
Qed.

Definition monad_mixin := Monad.Mixin joinretM joinMret joinA.
End monad_of_ret_bind.
Module Exports.
Definition Monad_of_ret_bind M ret bind a b c :=
  Monad.Pack (Monad.Class (@monad_mixin M ret bind a b c)).
End Exports.
End Monad_of_ret_bind.
Export Monad_of_ret_bind.Exports.

(*
(* monads on Type are strong monads *)
Section strength.
Variable M : monad.
Definition strength A B (xy : (A * M B)%type) : M (A * B)%type :=
  let (x,my) := xy in my >>= (fun y => Ret (x,y)).
Lemma strengthE A B (x:A) (my:M B) : strength (x,my) = my >>= (fun y => Ret (x,y)).
Proof. done. Qed.
Lemma strength_unit A : snd = M # snd \o strength (A:=unit) (B:=A).
Proof.
apply functional_extensionality => x.
case: x => i ma.
rewrite compE strengthE.
rewrite -fmapE fmap_bind fcomp_def.
rewrite bindE.
have ->: Join ((M # (M # snd \o (fun y : A => Ret (i, y)))) ma) =
((M # snd \o Join) \o M # (fun y : A => Ret (i, y))) ma
  by rewrite functor_o join_naturality.
rewrite functor_o.
have ->: ((M # snd \o Join) \o (M # Ret \o M # pair i)) ma =
(M # snd \o (Join \o M # Ret) \o M # pair i) ma by done.
rewrite joinMret compfid.
rewrite -functor_o.
have ->: snd \o pair i = id by done.
by rewrite functor_id.
Qed.
End strength.
*)

Definition mpair {M : monad} {A} (xy : (M A * M A)%type) : M (A * A)%type :=
  let (mx, my) := xy in
  mx >>= (fun x => my >>= fun y => Ret (x, y)).

Lemma mpairE (M : monad) A (mx my : M A) :
  mpair (mx, my) = mx >>= (fun x => my >>= fun y => Ret (x, y)).
Proof. by []. Qed.

Lemma naturality_mpair (M : monad) (A B : Type) (f : A -> B) (g : A -> M A):
  (M # f^`2) \o (mpair \o g^`2) = mpair \o ((M # f) \o g)^`2.
Proof.
rewrite boolp.funeqE => -[a0 a1].
rewrite compE fmap_bind.
rewrite compE mpairE compE bind_fmap; bind_ext => a2.
rewrite fcompE fmap_bind 2!compE bind_fmap; bind_ext => a3.
by rewrite fcompE -(compE (M # f^`2)) (natural RET) FIdf.
Qed.

(*Local Notation "[ \o f , .. , g , h ]" := (f \o .. (g \o h) ..)
  (at level 0) (*, format "[ \o '['  f , '/' .. , '/' g , '/' h ']' ]"
  ).*) : test_scope.

Local Open Scope test_scope.

Lemma naturality_mpair' (M : monad) A B (f : A -> B) (g : A -> M A):
  (M # f^`2) \o (mpair \o g^`2) = mpair \o ((M # f) \o g)^`2.
Proof.
rewrite funeqE => -[a0 a1].
change ((M # f^`2 \o (mpair \o g^`2)) (a0, a1)) with
    ((M # f^`2) (mpair (g a0, g a1))).
change ((mpair \o (M # f \o g)^`2) (a0, a1)) with
    (mpair ((M # f \o g) a0,(M # f \o g) a1)).
rewrite !mpairE.
rewrite !bindE.
evar (T : Type);evar (RHS : A -> T).
have ->: (fun x : A => do y <- g a1; Ret (x, y)) = RHS.
  rewrite funeqE => x; rewrite bindE.
  rewrite functor_o.
  change (Join ([\o M # Ret,M # pair x] (g a1))) with
        ([\o Join,M # Ret,M # pair x] (g a1)).
    rewrite joinMret'.
  exact: erefl.
rewrite /RHS {RHS}; rewrite {T}.
change ((M # f^`2) (Join ((M # (fun x : A => (M # pair x) (g a1))) (g a0)))) with
    ((M # f^`2 \o Join) ((M # (fun x : A => (M # pair x) (g a1))) (g a0))).
rewrite join_naturality.
evar (T : Type);evar (RHS : T).
have->:(M # (fun x : B => do y <- (M # f \o g) a1; Ret (x, y))) = RHS.
- rewrite functor_o.
  rewrite bindE'.
  rewrite functor_o.
  exact: erefl.
rewrite/RHS{RHS};rewrite{T}.
change
  (
    Join
    (((M # Join \o M # (Fun M (B:=M (B * B)%type))^~ ((M # f \o g) a1)) \o
        M # (fun x y : B => Ret (x, y))) ((M # f \o g) a0))
  ) with
    (
      (
        [ \o Join ,
          (M # Join) ,
          (M # (Fun M (B:=M (B * B)%type))^~ ((M # f \o g) a1)) ,
          (M # (fun x y : B => Ret (x, y))) ,
          (M # f \o g) ]
      ) a0)
    .
rewrite joinA'.
(*
rewrite fmap_bind. compE [in RHS]/= bind_fmap; bind_ext => a2.
rewrite fcompE fmap_bind compE bind_fmap; bind_ext => a3.
by rewrite fcompE -(compE (fmap M # f^`2)) fmap_ret.
Qed.
*)
Abort.

Local Close Scope test_scope.
*)

Section rep.

Variable M : monad.

Fixpoint rep (n : nat) (mx : M unit) : M unit :=
  if n is n.+1 then mx >> rep n mx else skip.

Lemma repS mx n : rep n.+1 mx = rep n mx >> mx.
Proof.
elim: n => /= [|n IH]; first by rewrite bindmskip bindskipf.
by rewrite bindA IH.
Qed.

Lemma rep1 mx : rep 1 mx = mx. Proof. by rewrite repS bindskipf. Qed.

Lemma rep_addn m n mx : rep (m + n) mx = rep m mx >> rep n mx.
Proof.
elim: m n => [|m IH /=] n; by
  [rewrite bindskipf add0n | rewrite -addnE IH bindA].
Qed.

End rep.

Section MonadCount.

Variable M : monad.
Variable tick : M unit.

Fixpoint hanoi n : M unit :=
  if n is n.+1 then hanoi n >> tick >> hanoi n else skip.

Lemma hanoi_rep n : hanoi n = rep (2 ^ n).-1 tick.
Proof.
elim: n => // n IH /=.
rewrite IH -repS prednK ?expn_gt0 // -rep_addn.
by rewrite -subn1 addnBA ?expn_gt0 // addnn -muln2 -expnSr subn1.
Qed.

End MonadCount.
