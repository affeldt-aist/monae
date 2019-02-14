Ltac typeof X := type of X.
Require Import FunctionalExtensionality Coq.Program.Tactics ProofIrrelevance.
Require Classical.
Require Import ssreflect ssrmatching ssrfun ssrbool.
From mathcomp Require Import eqtype ssrnat seq path div choice fintype tuple.
From mathcomp Require Import finfun bigop.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "A `2" (format "A `2", at level 3).
Reserved Notation "f ^`2" (format "f ^`2", at level 3).
Reserved Notation "l \\ p" (at level 50).
Reserved Notation "m >>= f" (at level 50).
Reserved Notation "f =<< m" (at level 50).
Reserved Notation "'do' x <- m ; e"
  (at level 60, x ident, m at level 200, e at level 60).
Reserved Notation "'do' x : T <- m ; e"
  (at level 60, x ident, m at level 200, e at level 60).
Reserved Notation "m >=> n" (at level 50).
Reserved Notation "n <=< m" (at level 50).
Reserved Notation "x '[~]' y" (at level 50).
Reserved Notation "'[~p]'".
Reserved Notation "f ($) m" (at level 11).
Reserved Notation "f (o) g" (at level 11).

Notation "l \\ p" := ([seq x <- l | x \notin p]).

Section funcomp_lemmas.
Lemma compA {A B C D} (f : C -> D) (g : B -> C) (h : A -> B) : f \o (g \o h) = (f \o g) \o h.
Proof. by []. Qed.

Lemma compfid A B (f : A -> B) : f \o id = f. Proof. by []. Qed.

Lemma compidf A B (f : A -> B) : id \o f = f. Proof. by []. Qed.

Lemma compE A B C (g : B -> C) (f : A -> B) a : (g \o f) a = g (f a).
Proof. by []. Qed.
End funcomp_lemmas.

Section misc_lemmas.
Lemma funextP (T U : Type) (f g: T->U) : f = g <-> (forall x, f x = g x).
split; first by move->.
by apply:functional_extensionality.
Qed.
End misc_lemmas.

(* Our `category' is always concrete; morphisms are just functions. *)
Module Category.
Record class_of (T : Type) : Type := Class {
  obj : T -> Type ; (* T and obj is like a ``universe a la Tarski'' *)
  hom : forall A B, (obj A -> obj B) -> Prop ; (* subset of morphisms *)
(*  _ : injective obj ; (* NB: do we need this? *)*)
  _ : forall (A : T), hom (A:=A) (B:=A) id ; (* id is in hom *)
  _ : forall (A B C : T) (f : obj A -> obj B) (g : obj B -> obj C),
      hom f -> hom g -> hom (g \o f) ; (* hom is closed under composition *)
}.
Structure t : Type := Pack { car : Type ; class : class_of car }.
Module Exports.
Notation category := t.
Coercion car : category >-> Sortclass.
Definition El (C : t) : C -> Type :=
  let: Pack _ (Class x _ _ _) := C in x.
End Exports.
End Category.
Export Category.Exports.

Module Hom.
Section ClassDef.
Variables (C : category) (U V : C).
Local Notation U' := (El U).
Local Notation V' := (El V).
Let hom (X : category) : forall (A B : X), (El A -> El B) -> Prop :=
  let: Category.Pack _ (Category.Class _ x _ _) := X in x.
Definition axiom (f : U' -> V') := hom f.
Structure map (phUV : phant (U' -> V')) := Pack {apply; _ : axiom apply}.
Local Coercion apply : map >-> Funclass.
Variables (phUV : phant (U' -> V')) (f g : U' -> V') (cF : map phUV).
Definition class := let: Pack _ c as cF' := cF return axiom cF' in c.
Definition clone fA of phant_id g (apply cF) & phant_id fA class :=
  @Pack phUV f fA.
End ClassDef.
Module Exports.
Notation hom f := (axiom f).
Coercion apply : map >-> Funclass.
Add Printing Coercion apply.
Notation "[ 'fun' 'of' f ]" := (apply f)
  (at level 0, format "[ 'fun'  'of'  f ]") : category_scope.
Notation Hom fA := (Pack (Phant _) fA).
Notation "{ 'hom' U , V }" := (map (Phant (El U -> El V)))
  (at level 0, format "{ 'hom'  U , V }") : category_scope.
Notation "[ 'hom' 'of' f 'as' g ]" := (@clone _ _ _ _ f g _ _ idfun id)
  (at level 0, format "[ 'hom'  'of'  f  'as'  g ]") : category_scope.
Notation "[ 'hom' 'of' f ]" := (@clone _ _ _ _ f f _ _ id id)
  (at level 0, format "[ 'hom'  'of'  f ]") : category_scope.
End Exports.
End Hom.
Export Hom.Exports.

Open Scope category_scope.

Section category_interface.
Variable C : category.

Lemma category_idfun_proof : forall (a : C), hom (idfun : El a -> El a).
Proof. by case: C => [? []]. Qed.
Canonical idfun_hom a := Hom (category_idfun_proof a).
Lemma category_comp_proof : forall (a b c : C) (f : {hom b,c}) (g : {hom a,b}),
    hom (f \o g).
Proof.
case: C => [car [el hom ? hom_comp]] a b c f g.
by apply/hom_comp;case:f;case:g.
Qed.
Canonical comp_hom (a b c : C) (f : {hom b, c}) (g : {hom a, b}) := Hom (category_comp_proof f g).
End category_interface.
(*
Notation "'Id' a" := (category_id a) (at level 10) : category_scope.
Notation "f '\\o' g" := (category_comp f g) (at level 50) : category_scope.
*)

Section category_lemmas.
Variable C : category.
(*
Lemma hom_ext' (a b : C) (f g : El a -> El b) (p : hom f) (q : hom g) (H : f = g)
  : Hom p = Hom q.
Proof.
move:p q.
rewrite H=>p q.
by have->:p=q by apply/proof_irrelevance.
Qed.
Lemma hom_extext' (a b : C) (f g : El a -> El b) (p : hom f) (q : hom g)
      : (forall x, f x = g x) -> Hom p = Hom q.
Proof. by move/functional_extensionality=>H; apply hom_ext'. Qed.
*)

Lemma hom_ext (a b : C) (f g : {hom a,b})
  : f = g <-> [fun of f] = [fun of g].
Proof.
split; first by move->.
case:f=>f Hf;case:g=>g Hg.
rewrite/Hom.apply=>H.
move:H Hf Hg=>->Hf Hg.
  by have->:Hf=Hg by apply proof_irrelevance.
Qed.
Lemma hom_extext (a b : C) (f g : {hom a,b}) :
  f = g <-> (forall x, [fun of f] x = [fun of g] x).
Proof. split. by move->. by move/functional_extensionality=>H; apply hom_ext. Qed.

Lemma hom_compA (a b c d : C) (h : {hom c, d}) (g : {hom b, c}) (f : {hom a, b})
  : [hom of [hom of h \o g] \o f] = [hom of h \o [hom of g \o f]].
Proof. by case:f=>f Hf;case:g=>g Hg;case:h=>h Hh; apply hom_ext. Qed.

Lemma hom_idfunE (a : C) : [hom of idfun] = idfun :> (El a -> El a).
Proof. done. Qed.
Lemma hom_compE (a b c : C) (g : {hom b,c}) (f : {hom a,b})
  : [hom of g \o f] = g \o f :> (El a -> El c).
Proof. done. Qed.
End category_lemmas.

Section Type_category.
Definition Type_category_class : Category.class_of Type :=
@Category.Class Type id (fun _ _ _ => True) (fun _ => I) (fun _ _ _ _ _ _ _ => I).
Canonical Type_category := Category.Pack Type_category_class.
Definition hom_Type (a b : Type) (f : a -> b) : {hom a,b} := Hom (I : hom (f : El a -> El b)).
End Type_category.

(*** functor ***)
Module FunctorLaws.
Section def.
Variable (C D : category).
Variable (M : C -> D) (f : forall A B, {hom A,B} -> {hom M A, M B}).
Definition id := forall A, f [hom of idfun] = [hom of idfun] :> {hom M A,M A}.
Definition comp := forall A B C (g : {hom B,C}) (h : {hom A,B}),
  f [hom of g \o h] = [hom of f g \o f h] :> {hom M A,M C}.
End def.
End FunctorLaws.

Module Functor.
Record class_of (C D : category) (m : C -> D) : Type := Class {
  f : forall A B, {hom A,B} -> {hom m A, m B} ;
  _ : FunctorLaws.id f ;
  _ : FunctorLaws.comp f
}.
Structure t (C D : category) : Type := Pack { m : C -> D ; class : class_of m }.
Module Exports.
Section exports.
Variables (C D : category).
Definition Fun (F : t C D) : forall A B, {hom A, B} -> {hom m F A, m F B} :=
  let: Pack _ (Class f _ _) := F return forall A B, {hom A, B} -> {hom m F A, m F B} in f.
Arguments Fun _ [A] [B].
End exports.
Notation functor := t.
Coercion m : functor >-> Funclass.
End Exports.
End Functor.
Export Functor.Exports.
Notation "F # f" := (Fun F f) (at level 11).

Section functor_lemmas.
Variable C D : category.
Variable F : functor C D.
Lemma functor_id : FunctorLaws.id (Fun F).
Proof. by case: F => [? []]. Qed.
Lemma functor_o : FunctorLaws.comp (Fun F).
Proof. by case: F => [? []]. Qed.

Lemma functor_id_fun a : F # [hom of idfun] = idfun :> (El (F a) -> El (F a)).
Proof. by rewrite functor_id. Qed.
Lemma functor_o_fun a b c (g : {hom b,c}) (h : {hom a,b}) :
  F # [hom of g \o h] = F # g \o F # h :> (El (F a) -> El (F c)).
Proof. by rewrite functor_o. Qed.
End functor_lemmas.

Section squaring.
Definition Squaring (A : Type) := (A * A)%type.
Notation "A `2" := (Squaring A).
Definition squaring_f A B (f : {hom A, B}) : {hom A`2,B`2} := hom_Type (fun x => (f x.1, f x.2)).
Lemma squaring_f_id : FunctorLaws.id squaring_f.
Proof. by move=> A /=; apply hom_extext => -[x1 x2]. Qed.
Lemma squaring_f_comp : FunctorLaws.comp squaring_f.
Proof. by move=> A B C g h /=; apply hom_extext => -[x1 x2]. Qed.
Definition squaring : functor _ _ :=
  Functor.Pack (Functor.Class squaring_f_id squaring_f_comp).
Notation "f ^`2" := (squaring # f).
End squaring.

Section functorid.
Variables C : category.
Definition id_f (A B : C) (f : {hom A,B}) := f.
Lemma id_id : FunctorLaws.id id_f. Proof. by move=>A. Qed.
Lemma id_comp : FunctorLaws.comp id_f. Proof. by move=>*. Qed.
Definition FId : functor _ _ := Functor.Pack (Functor.Class id_id id_comp).
Lemma FIdf (A B : C) (f : {hom A,B}) : FId # f = f.
Proof. by []. Qed.
End functorid.

Section functorcomposition.
Variables (C0 C1 C2 : category) (F : functor C1 C2) (G : functor C0 C1).
Definition functorcomposition a b := fun h : {hom a,b} => F # (G # h).
Lemma functorcomposition_id : FunctorLaws.id functorcomposition.
Proof.
by rewrite /FunctorLaws.id => A; rewrite /functorcomposition 2!functor_id.
Qed.
Lemma functorcomposition_comp : FunctorLaws.comp functorcomposition.
Proof.
rewrite /FunctorLaws.comp => a b c g h; rewrite /functorcomposition.
by rewrite 2!functor_o.
Qed.
Definition FComp : functor C0 C2:=
  Functor.Pack (Functor.Class functorcomposition_id functorcomposition_comp).
End functorcomposition.

Section functorcomposition_lemmas.
Variables (C0 C1 C2 C3 : category).
Lemma FCompId (F : functor C0 C1) : FComp F (FId C0) = F.
Proof.
destruct F as [m [f0 f1 f2]]; congr Functor.Pack; congr Functor.Class => //;
  exact/ProofIrrelevance.proof_irrelevance.
Qed.
Lemma FIdComp (F : functor C0 C1) : FComp (FId _) F = F.
Proof.
destruct F as [m [f0 f1 f2]]; congr Functor.Pack; congr Functor.Class => //;
  exact/ProofIrrelevance.proof_irrelevance.
Qed.
Lemma FCompA (F : functor C2 C3) (G : functor C1 C2) (H : functor C0 C1)
  : FComp (FComp F G) H = FComp F (FComp G H).
Proof.
destruct F as [m [f0 f1 f2]].
destruct G as [n [g0 g1 g2]].
destruct H as [o [h0 h1 h2]].
congr Functor.Pack; congr Functor.Class => //;
  exact/ProofIrrelevance.proof_irrelevance.
Qed.
Lemma FCompE (F : functor C1 C2) (G : functor C0 C1) a b (k : {hom a, b}) : (FComp F G) # k = F # (G # k).
Proof. by []. Qed.
End functorcomposition_lemmas.

(*** natural transformation ***)
Section natural_transformation.
Variables (C D : category) (F G : functor C D).
Definition transformation_type := forall a, {hom F a ,G a}.
Definition naturalP (phi : transformation_type) :=
  forall a b (h : {hom a,b}),
    (G # h) \o (phi a) = (phi b) \o (F # h).
End natural_transformation.
Arguments naturalP [C D] F G.

Section natural_transformation_example.
Definition fork' A (a : A) := (a, a).
Definition fork A := hom_Type (@fork' A).
(* fork is a natural transformation FId -> squaring *)
Lemma fork_natural : naturalP (FId _) squaring fork.
Proof. done. Qed.
End natural_transformation_example.

(*** adjoint functor ***)
(* We define adjointness F -| G in terms of its unit and counit (η and ε). *)
Section adjoint_functors.
Variables (C D : category) (F : functor C D) (G : functor D C).
Definition eta_type := forall c, {hom c, (G \o F) c}.
Definition eps_type := forall d, {hom (F \o G) d, d}.
Definition triangular_law1 (eps : eps_type) (eta : eta_type) :=
  forall c, (eps (F c)) \o (F # eta c) = idfun.
Definition triangular_law2 (eps : eps_type) (eta : eta_type) :=
  forall d, (G # eps d) \o (eta (G d)) = idfun.
Definition adjointP (eps : eps_type) (eta : eta_type) :=
  naturalP (FComp F G) (FId D) eps /\ naturalP (FId C) (FComp G F) eta
  /\ triangular_law1 eps eta /\ triangular_law2 eps eta.
Definition phi c d (eta : eta_type) : {hom F c, d} -> {hom c, G d} :=
  fun h => [hom of (G # h) \o (@eta c)].
Definition psi c d (eps : eps_type) : {hom c, G d} -> {hom F c, d} :=
  fun h => [hom of (@eps d) \o (F # h)].
End adjoint_functors.

(* monad *)
Module JoinLaws.
Section join_laws.
Variables (C : category) (M : functor C C) .
Variables (ret : transformation_type (FId C) M)
          (join : transformation_type (FComp M M) M).

Definition ret_naturality := naturalP (FId C) M ret.

Definition join_naturality := naturalP (FComp M M) M join.

Definition join_left_unit :=
  forall a, @join a \o @ret (M a) = idfun :> (El (M a) -> El (M a)).

Definition join_right_unit :=
  forall a, @join _ \o M # @ret _ = idfun :> (El (M a) -> El (M a)).

Definition join_associativity :=
  forall a, @join _ \o M # @join _ = @join _ \o @join _ :> (El (M (M (M a))) -> El (M a)).
End join_laws.
End JoinLaws.

Module BindLaws.
Section bindlaws.
Variables (C : category) (M : functor C C) .

Variable b : forall A B, {hom A, M B} -> {hom M A, M B}.
Local Notation "m >>= f" := (b f m).
(*
NB(saikawa)
I am not convinced if the above typing of `bind' makes sense from the
category-theoretical point of view.  It is rather an ad hoc change needed for
stating the associavitity below.  I am not sure either if it works well in
further formalizations.  Both should be checked with careful thoughts and
examples.

Original and usual definition is :
Variable b : forall A B, M A -> (A -> M B) -> M B.
Local Notation "m >>= f" := (b m f).

This original definition seems to be valid only in closed categories, which
would be a mix-in structure over categories.
*)

Fact associative_aux x y z (f : {hom x, M y}) (g : {hom y, M z})
  : (fun w => (f w >>= g)) = (b g \o f).
Proof. reflexivity. Qed.

Definition associative := forall A B C (m : El (M A)) (f : {hom A, M B}) (g : {hom B, M C}),
  (m >>= f) >>= g = m >>= [hom of b g \o f].

Definition left_neutral (r : forall A, {hom A, M A}) :=
  forall A B (f : {hom A, M B}), [hom of (b f \o r A)] = f.

Definition right_neutral (r : forall A, {hom A, M A}) :=
  forall A (m : El (M A)), m >>= r _ = m.
End bindlaws.

Section bindlaws_on_Type.
Variable M : functor Type_category Type_category.

Variable b : forall A B, (A -> M B) -> M A -> M B.
Local Notation "m >>= f" := (b f m).

Definition bind_right_distributive (add : forall B, M B -> M B -> M B) :=
  forall A B (m : M A) (k1 k2 : A -> M B),
    m >>= (fun x => add _ (k1 x) (k2 x)) = add _ (m >>= k1) (m >>= k2).

Definition bind_left_distributive (add : forall B, M B -> M B -> M B) :=
  forall A B (m1 m2 : M A) (k : A -> M B),
    (add _ m1 m2) >>= k = add _ (m1 >>= k) (m2 >>= k).

Definition right_zero (f : forall A, M A) :=
  forall A B (g : M B), g >>= (fun _ => f A) = f A.

Definition left_zero (f : forall A, M A) := forall A B g, f A >>= g = f B.

Definition left_id (r : forall A, M A) (add : forall B, M B -> M B -> M B) :=
  forall A (m : M A), add _ (r _) m = m.

Definition right_id (r : forall A, M A) (add : forall B, M B -> M B -> M B) :=
  forall A (m : M A), add _ m (r _) = m.
End bindlaws_on_Type.
End BindLaws.

Section bind_lemmas.
Variables (C : category) (M : functor C C) .
Variable b : forall A B, {hom A, M B} -> {hom M A, M B}.
Local Notation "m >>= f" := (b f m).
Lemma bind_left_neutral_hom_fun (r : forall A, {hom A, M A})
  : BindLaws.left_neutral b r
    <-> forall A B (f : {hom A, M B}), b f \o r A = [fun of f].
Proof. by split; move=>H A B f; move: (H A B f); move/hom_ext. Qed.
End bind_lemmas.

Module Monad.
Section monad.
Variable (C : category).
Record mixin_of (M : functor C C) : Type := Mixin {
  ret : forall A, {hom A, M A} ;
  join : forall A, {hom M (M A), M A} ;
  _ : JoinLaws.ret_naturality ret ;
  _ : JoinLaws.join_naturality join ;
  _ : JoinLaws.join_left_unit ret join ;
  _ : JoinLaws.join_right_unit ret join ;
  _ : JoinLaws.join_associativity join;
  }.
Record class_of (M : C -> C) := Class {
  base : Functor.class_of M ; mixin : mixin_of (Functor.Pack base) }.
Structure t : Type := Pack { m : C -> C ; class : class_of m }.
Definition baseType (M : t) := Functor.Pack (base (class M)).
End monad.
Module Exports.
Definition Ret (C : category ) (M : t C) : forall A, {hom A, m M A} :=
  let: Pack _ (Class _ (Mixin ret _ _ _ _ _ _) ) := M return forall A, {hom A, m M A} in ret.
Arguments Ret {C M A} : simpl never.
Definition Join (C : category) (M : t C) : forall A ,{hom m M (m M A), m M A} :=
  let: Pack _ (Class _ (Mixin _ join _ _ _ _ _)) := M in join.
Arguments Join {C M A} : simpl never.
Notation monad := t.
Coercion baseType : monad >-> functor.
Canonical baseType.
End Exports.
End Monad.
Export Monad.Exports.

Section monad_interface.
Variable (C : category) (M : monad C).
Lemma ret_naturality : JoinLaws.ret_naturality (@Ret C M).
Proof. by case: M => ? [? []]. Qed.
Lemma join_naturality : JoinLaws.join_naturality (@Join C M).
Proof. by case: M => ? [? []]. Qed.
Lemma joinretM : JoinLaws.join_left_unit (@Ret C M) (@Join C M).
Proof. by case: M => ? [? []]. Qed.
Lemma joinMret : JoinLaws.join_right_unit (@Ret C M) (@Join C M).
Proof. by case: M => ? [? []]. Qed.
Lemma joinA : JoinLaws.join_associativity (@Join C M).
Proof. by case: M => ? [? []]. Qed.
End monad_interface.

Section from_join_laws_to_bind_laws.
Variable (C : category) (F : functor C C).
Variable (ret : forall A, {hom A, F A}) (join : forall A, {hom F (F A), F A}).

Hypothesis ret_naturality : JoinLaws.ret_naturality ret.
Hypothesis join_naturality : JoinLaws.join_naturality join.
Hypothesis joinretM : JoinLaws.join_left_unit ret join.
Hypothesis joinMret : JoinLaws.join_right_unit ret join.
Hypothesis joinA : JoinLaws.join_associativity join.

Let bind (A B : C) (f : {hom A, F B}) : {hom F A, F B} := [hom of (@join B) \o (F # f)].

Lemma bindretf_derived : BindLaws.left_neutral bind ret.
Proof.
move=> A B f.
apply hom_ext=>/=.
rewrite -(compA (join _)) ret_naturality compA.
by rewrite joinretM compidf /FId /id_f /=.
Qed.

Lemma bindmret_derived : BindLaws.right_neutral bind ret.
Proof.
move=>A;rewrite /bind.
have->: [hom of join A \o F # ret A] = [hom of idfun]=>//.
apply hom_ext=>/=.
by rewrite joinMret.
Qed.

Lemma bindA_derived : BindLaws.associative bind.
Proof.
move=> a b c m f g; rewrite /bind /=.
rewrite [LHS](_ : _ = ((@join _ \o (F # g \o @join _) \o F # f) m)) //.
rewrite join_naturality (compA (@join c)) -joinA -(compE (@join _)).
  by have->:F # [hom of ([fun of join c] \o [fun of F # g]) \o [fun of f]]
     = [hom of F # join c \o FComp F F # g \o F # f] by rewrite 2!functor_o.
Qed.
End from_join_laws_to_bind_laws.

Section monad_lemmas.
Variable (C : category) (M : monad C).

Definition Bind A B (f : {hom A, M B}) : {hom M A, M B} := [hom of Join \o (M # f)].
Arguments Bind {A B} : simpl never.
Local Notation "m >>= f" := (Bind f m).
Lemma bindE (A B:C) : Bind = fun (f : {hom A,M B}) => [hom of Join \o M # f].
Proof. by []. Qed.
Lemma bindretf : BindLaws.left_neutral (@Bind) (@Ret C M).
Proof. apply: bindretf_derived; [exact: ret_naturality | exact: joinretM]. Qed.
Lemma bindretf_fun : 
  (forall (A B : C) (f : {hom A,M B}),
      [fun of (@Bind) A B f] \o [fun of (@Ret C M) A] = [fun of f]).
Proof. by apply/bind_left_neutral_hom_fun/bindretf. Qed.
Lemma bindmret : BindLaws.right_neutral (@Bind) (@Ret C M).
Proof. apply: bindmret_derived; exact: joinMret. Qed.
Lemma bindA : BindLaws.associative (@Bind).
Proof. apply bindA_derived; [exact: join_naturality | exact: joinA]. Qed.

Lemma bindE_ext A B : forall x (f : {hom A, M B}), x >>= f = Join ((M # f) x).
Proof. by []. Qed.

(* *_seqcomp lemmas are for the head of a chain of funcomps f \o (g \o (h \o ..))*)
Lemma joinretM_seqcomp a (c:C) (f:El c->_) : @Join C M a \o (@Ret C M (M a) \o f) = f.
Proof. by rewrite compA joinretM. Qed.
Lemma joinMret_seqcomp a (c:C) (f:El c->_) : @Join C M a \o (M # @Ret C M a \o f) = f.
Proof. by rewrite compA joinMret. Qed.
Lemma joinA_seqcomp a (c:C) (f:El c->_) : @Join C M a \o (M # @Join C M a \o f) = @Join C M a \o (@Join C M (M a) \o f).
Proof. by rewrite compA joinA. Qed.
End monad_lemmas.
Arguments Bind {C M A B} : simpl never.
Notation "m >>= f" := (Bind f m).
