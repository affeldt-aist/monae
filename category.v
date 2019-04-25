Ltac typeof X := type of X.
Require Import ProofIrrelevance ssreflect ssrmatching ssrfun ssrbool.
From mathcomp Require Import eqtype ssrnat seq path div choice fintype tuple.
From mathcomp Require Import finfun bigop.
From mathcomp Require Import boolp.

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
Reserved Notation "f (o) g" (at level 11).

Notation "l \\ p" := ([seq x <- l | x \notin p]).

(*** flist (list of composable functions) and funcomp ***)
Module FList.
Inductive T (A:Type) (B:Type) : Type :=
| Just (f:A->B) : T A B
| Cons (X:Type) (f:X->B) (fs:T A X) : T A B.

Fixpoint apply A B (fs : T A B) (x : A) {struct fs} : B
 :=
  match fs with
  | Just f => f x
  | Cons _ f fs' => f (apply fs' x)
  end.

Module Exports.
Notation "[ \f f , .. , g , h ]" := (apply (Cons f ( .. (Cons g (Just h)) ..)))
  (at level 0, format "[ \f '['  f ,  '/' .. ,  '/' g ,  '/' h ']' ]") : flist_scope.
End Exports.

Local Notation "[ \o f , .. , g , h ]" := (f \o .. (g \o h) ..)
  (at level 0).
Local Notation "[ \f f , .. , g , h ]" := (apply (Cons f ( .. (Cons g (Just h)) ..)))
  (at level 0).
Example apply_FList_is_funcomp :
  forall A B C (f:A->B) (g:B->C), [\o g,f] = [\f g,f].
Proof. reflexivity. Qed.
End FList.
Export FList.Exports.
Open Scope flist_scope.

Section flist_lemmas.
Variables (A B C D : Type) (h : C -> D) (g : B -> C) (f : A -> B).
Lemma flistA1 : [\f [\f h,g],f] = [\f h,g,f].
Proof. reflexivity. Qed.
Lemma flistA2 : [\f h,[\f g,f]] = [\f h,g,f].
Proof. reflexivity. Qed.
Lemma flistfid : [\f f,id] = f.
Proof. reflexivity. Qed.
Lemma flistidf : [\f id,f] = f.
Proof. reflexivity. Qed.
Lemma flistE : [\f g,f] = g \o f.
Proof. reflexivity. Qed.
End flist_lemmas.

Section funcomp_lemmas.
Lemma compA {A B C D} (f : C -> D) (g : B -> C) (h : A -> B) : f \o (g \o h) = (f \o g) \o h.
Proof. by []. Qed.

Lemma compfid A B (f : A -> B) : f \o id = f. Proof. by []. Qed.

Lemma compidf A B (f : A -> B) : id \o f = f. Proof. by []. Qed.

Lemma compE A B C (g : B -> C) (f : A -> B) a : (g \o f) a = g (f a).
Proof. by []. Qed.
End funcomp_lemmas.

(*** category ***)
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
  (at level 0, format "{ 'hom'  U ,  V }") : category_scope.
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

Section category_lemmas.
Variable C : category.

Lemma homfunK (a b : C) (f : {hom a,b}) : [hom of [fun of f]] = f.
Proof. by case:f. Qed.

Lemma comp_homE (a b c:C) (g:{hom b,c}) (f:{hom a,b}) : comp_hom g f = [hom of g \o f].
Proof. done. Qed.

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
  f = g <-> [fun of f] =1 [fun of g].
Proof. split => [->//|]; rewrite -funeqE => ?; by apply hom_ext. Qed.

Lemma hom_compA (a b c d : C) (h : {hom c, d}) (g : {hom b, c}) (f : {hom a, b})
  : [hom of [hom of h \o g] \o f] = [hom of h \o [hom of g \o f]].
Proof. by case:f=>f Hf;case:g=>g Hg;case:h=>h Hh; apply hom_ext. Qed.
Lemma hom_idfunE (a : C) : [hom of idfun] = idfun :> (El a -> El a).
Proof. done. Qed.

(* experiment: to avoid "_ \o id" or "id \o _" popping out when we rewrite !compA.
 "homp" = "\h"
 g \h f = [fun of g] \o [fun of f]
*)
Local Notation "[ \h f , .. , g , h ]" := ([fun of f] \o .. ([fun of g] \o [fun of h]) ..)
  (at level 0, format "[ \h '['  f ,  '/' .. ,  '/' g ,  '/' h ']' ]") : category_scope.
Lemma hompA (a b c d : C) (h : {hom c, d}) (g : {hom b, c}) (f : {hom a, b})
  : (h \o g) \o f = [\h h, g, f].
Proof. done. Qed.
Lemma hompE (a b c : C) (g : {hom b,c}) (f : {hom a,b}) x : g (f x) = (g \o f) x.
Proof. done. Qed.
Lemma homp_idfun (a b : C) (f : {hom a,b}) : f = [\h f, [hom of idfun]] :> (El a -> El b).
Proof. done. Qed.
Lemma hom_homp (a b c : C) (g : {hom b,c}) (f : {hom a,b})
  : [fun of [hom of g \o f]] = g \o f :> (El a -> El c).
Proof. done. Qed.
Lemma hom_homp_head (a b c x: C) (g : {hom b,c}) (f : {hom a,b}) (e : {hom x,a})
  : [\h [hom of g \o f], e] = [\h g, f, e] :> (El x -> El c).
Proof. done. Qed.

(* example *)
Example hompA' (a b c d : C) (h : {hom c, d}) (g : {hom b, c}) (f : {hom a, b})
  : (h \o g) \o f = [\h h, g, f].
Proof.
(*
If we issue
 rewrite !compA.
here, the result is :
  C : category
  a, b, c, d : C
  h : {hom c,d}
  g : {hom b,c}
  f : {hom a,b}
  ============================
  ((((((((((((((((((((((((((((((((((((((((((((... \o id) \o id) \o id) \o id) \o
                                            id) \o id) \o id) \o id) \o id) \o
                                       id) \o id) \o id) \o id) \o id) \o id) \o
                                 id) \o id) \o id) \o id) \o id) \o id) \o id) \o
                          id) \o id) \o id) \o id) \o id) \o id) \o id) \o id) \o
                  id) \o id) \o id) \o id) \o id) \o id) \o id) \o id) \o id) \o
         id) \o id) \o id) \o id) \o id) \o id =
  ((((((((((((((((((((((((((((((((((((((((((((... \o id) \o id) \o id) \o id) \o
                                            id) \o id) \o id) \o id) \o id) \o
                                       id) \o id) \o id) \o id) \o id) \o id) \o
                                 id) \o id) \o id) \o id) \o id) \o id) \o id) \o
                          id) \o id) \o id) \o id) \o id) \o id) \o id) \o id) \o
                  id) \o id) \o id) \o id) \o id) \o id) \o id) \o id) \o id) \o
         id) \o id) \o id) \o id) \o id) \o id
*)
by rewrite !hompA.
(* rewrite !hompA blocks id's from coming in, thanks to {hom _,_} conditions on arguments. *)
Abort.
End category_lemmas.
(*
Notation "[ \h f , .. , g , h ]" := ([fun of f] \o .. ([fun of g] \o [fun of h]) ..)
  (at level 0, format "[ \h '['  f ,  '/' .. ,  '/' g ,  '/' h ']' ]") : category_scope.
*)

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
Arguments Fun _ [A] [B] : simpl never.
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
Lemma squaringE A B (f : {hom A, B}) x : (f ^`2) x = (f x.1, f x.2).
Proof. by []. Qed.
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
Local Notation "[ \h f , .. , g , h ]" := ([fun of f] \o .. ([fun of g] \o [fun of h]) ..)
  (at level 0, format "[ \h '['  f ,  '/' .. ,  '/' g ,  '/' h ']' ]") : category_scope.
Definition naturalP_head (phi : transformation_type) :=
  forall a b c (h : {hom a,b}) (f : {hom c,F a}),
    [\h (G # h), (phi a), f] = [\h (phi b), (F # h), f].
End natural_transformation.
Arguments naturalP [C D] F G.
Arguments naturalP_head [C D] F G.

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
Variables (C : category) (M : C -> C).

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
Variables (C : category) (M : C -> C).
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

(* *_head lemmas are for [fun of f] \o ([fun of g] \o ([fun of h] \o ..))*)
Local Notation "[ \h f , .. , g , h ]" := ([fun of f] \o .. ([fun of g] \o [fun of h]) ..)
  (at level 0, format "[ \h '['  f ,  '/' .. ,  '/' g ,  '/' h ']' ]") : category_scope.
Lemma ret_naturality_head : naturalP_head (FId C) M (@Ret C M).
Proof. by move=>*; rewrite -hompA ret_naturality. Qed.
Lemma join_naturality_head : naturalP_head (FComp M M) M (@Join C M).
Proof. by move=>*; rewrite -hompA join_naturality. Qed.
Lemma joinretM_head a (c:C) (f:{hom c,M a}) : [\h Join, Ret, f] = f.
Proof. by rewrite compA joinretM. Qed.
Lemma joinMret_head a (c:C) (f:{hom c,M a}) : [\h Join, M # Ret, f] = f.
Proof. by rewrite compA joinMret. Qed.
Lemma joinA_head a (c:C) (f:{hom c,M (M (M a))})
  :[\h Join, M # Join, f] = [\h Join, Join, f].
Proof. by rewrite compA joinA. Qed.
End monad_interface.

Section from_join_laws_to_bind_laws.
Variable (C : category) (F : functor C C).
Variable (ret : forall A, {hom A, F A}) (join : forall A, {hom F (F A), F A}).

Hypothesis ret_naturality : JoinLaws.ret_naturality ret.
Hypothesis join_naturality : JoinLaws.join_naturality join.
Hypothesis joinretM : JoinLaws.join_left_unit ret join.
Hypothesis joinMret : JoinLaws.join_right_unit ret join.
Hypothesis joinA : JoinLaws.join_associativity join.

Local Notation "[ \h f , .. , g , h ]" := ([fun of f] \o .. ([fun of g] \o [fun of h]) ..)
  (at level 0, format "[ \h '['  f ,  '/' .. ,  '/' g ,  '/' h ']' ]") : category_scope.

Let ret_naturality_head : naturalP_head (FId C) F ret.
Proof. by move=>*; rewrite -hompA ret_naturality. Qed.
Let join_naturality_head : naturalP_head (FComp F F) F join.
Proof. by move=>*; rewrite -hompA join_naturality. Qed.
Let joinretM_head a (c:C) (f:{hom c,F a}) : [\h @join _, @ret _, f] = f.
Proof. by rewrite compA joinretM. Qed.
Let joinMret_head a (c:C) (f:{hom c,F a}) : [\h @join _, F # @ret _, f] = f.
Proof. by rewrite compA joinMret. Qed.
Let joinA_head a (c:C) (f:{hom c,F (F (F a))})
  :[\h @join _, F # @join _, f] = [\h @join _, @join _, f].
Proof. by rewrite compA joinA. Qed.

Let bind (A B : C) (f : {hom A, F B}) : {hom F A, F B} := [hom of (@join B) \o (F # f)].

Lemma bindretf_derived : BindLaws.left_neutral bind ret.
Proof.
move=> A B f.
apply hom_ext=>/=.
by rewrite hompA ret_naturality joinretM_head.
Qed.

Lemma bindmret_derived : BindLaws.right_neutral bind ret.
Proof.
by move=>A m;rewrite /bind/= !hompE joinMret.
Qed.

Lemma bindA_derived : BindLaws.associative bind.
Proof.
move=>a b c m f g; rewrite /bind.
(* LHS *)
rewrite hompE.
rewrite hom_homp_head.
rewrite hom_homp.
(* RHS *)
rewrite 2!functor_o.
rewrite !hom_compA.
rewrite 3!hom_homp.
(* NB : Changing the order of lemmas above easily leads to a dependency error.
   Can we fix this fragility? *)
by rewrite join_naturality_head joinA_head.
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
End monad_lemmas.
Arguments Bind {C M A B} : simpl never.
Notation "m >>= f" := (Bind f m).

(*** monad defined by adjointness ***)
Module MonadOfAdjoint.
Section monad_of_adjoint.
Local Notation "[ \h f , .. , g , h ]" := ([fun of f] \o .. ([fun of g] \o [fun of h]) ..)
  (at level 0, format "[ \h '['  f ,  '/' .. ,  '/' g ,  '/' h ']' ]") : category_scope.
Variables C D : category.
Variables (f : functor C D) (g : functor D C).
Variables (eps : eps_type f g) (eta : eta_type f g).
Definition M := FComp g f.
Definition join A : {hom M (M A), M A} := g # (@eps (f A)).
Definition ret A : {hom A, M A} := @eta A.
Hypothesis Had : adjointP eps eta.
Let Heps := let: conj x (conj _ (conj _ _)) := Had in x.
Let Heta := let: conj _ (conj x (conj _ _)) := Had in x.
Let Ht1 : triangular_law1 eps eta := let: conj _ (conj _ (conj x _)) := Had in x.
Let Ht2 : triangular_law2 eps eta := let: conj _ (conj _ (conj _ x)) := Had in x.
Let joinE : join = fun A => g # (@eps (f A)).
Proof. done. Qed.
Lemma join_natural : JoinLaws.join_naturality join.
Proof.
rewrite !joinE => A B h.
rewrite/M.
rewrite !FCompE.
have->:g#(f#(g#(f#h)))=g#((FComp f g)#(f#h))=>//.
rewrite /= -2!functor_o_fun.
congr (Fun g).
by rewrite hom_ext/= -Heps.
Qed.
Let join_associativity' A : join A \o join (M A) = join A \o (M # join A).
Proof.
rewrite joinE.
have->: g # eps (f A) \o g # eps (f (M A)) =
        g # [hom of eps (f A) \o eps (f (M A))] by rewrite functor_o.
by rewrite /= -functor_o_fun; congr (Fun g); rewrite hom_ext/= Heps.
Qed.
Lemma join_associativity : JoinLaws.join_associativity join.
Proof. by move=>A; rewrite join_associativity'. Qed.
Lemma ret_natural : JoinLaws.ret_naturality ret.
Proof. by move=>*; rewrite Heta. Qed.
Lemma join_left_unit : JoinLaws.join_left_unit ret join.
Proof. by move=>a;rewrite joinE Ht2. Qed.
Lemma join_right_unit : JoinLaws.join_right_unit ret join.
Proof.
move=>a;rewrite joinE. rewrite/M FCompE.
rewrite /= -functor_o_fun  -[in RHS]functor_id_fun.
congr (Fun g).
by rewrite hom_ext/= Ht1.
Qed.
Definition monad_of_adjoint_mixin : Monad.mixin_of M
  := Monad.Mixin ret_natural
                 join_natural
                 join_left_unit
                 join_right_unit
                 join_associativity.
End monad_of_adjoint.
Module Exports.
Definition Monad_of_adjoint C D (f:functor C D) (g:functor D C) (eps:eps_type f g) (eta:eta_type f g) (Had:adjointP eps eta) := Monad.Pack (Monad.Class (monad_of_adjoint_mixin Had)).
End Exports.
End MonadOfAdjoint.
Export MonadOfAdjoint.Exports.

(*** monad defined by bind and ret ***)
Module Monad_of_bind_ret.
Local Notation "[ \h f , .. , g , h ]" := ([fun of f] \o .. ([fun of g] \o [fun of h]) ..)
  (at level 0, format "[ \h '['  f ,  '/' .. ,  '/' g ,  '/' h ']' ]") : category_scope.
Section monad_of_bind_ret.
Variables C : category.
Variable M : C -> C.
Variable bind : forall A B, {hom A,M B} -> {hom M A,M B}.
Variable ret : forall A, {hom A, M A}.
Hypothesis bindretf : BindLaws.left_neutral bind ret.
Hypothesis bindmret : BindLaws.right_neutral bind ret.
Hypothesis bindA : BindLaws.associative bind.

Lemma bindretf_fun : 
  (forall (A B : C) (f : {hom A,M B}),
      [fun of bind f] \o [fun of ret A] = [fun of f]).
Proof. by apply bind_left_neutral_hom_fun. Qed.

Definition fmap A B (f : {hom A,B}) := bind [hom of ret B \o f].
Lemma fmap_id : FunctorLaws.id fmap.
Proof.
move=> A; apply hom_extext=>m. rewrite /fmap.
rewrite/idfun/=.
rewrite /funcomp.
rewrite -[in RHS](bindmret m).
congr (fun f => bind f m).
by rewrite hom_ext.
Qed.
Lemma fmap_o : FunctorLaws.comp fmap.
Proof.
move=> a b c g h; apply hom_extext=>m; rewrite /fmap/=.
rewrite bindA/=.
congr (fun f => bind f m); rewrite hom_ext/=.
by rewrite -[in RHS]hompA bindretf_fun.
Qed.
Definition functor_mixin := Functor.Class fmap_id fmap_o.
Let M' := Functor.Pack functor_mixin.

Let ret' : forall A, {hom A, M' A} := ret.
Definition join A : {hom M' (M' A), M' A} := bind [hom of idfun].

Let bind_fmap a b c (f : {hom a,b}) (m : El (M a)) (g : {hom b, M c}) :
  bind g (fmap f m) = bind [hom of g \o f] m .
Proof.
rewrite /fmap bindA. congr (fun f => bind f m).
rewrite homfunK comp_homE /= hom_ext/=.
rewrite -hompA. congr (fun x => x \o [fun of f]).
by rewrite bindretf_fun.
Qed.

Lemma bind_fmap_fun a b c (f : {hom a,b}) (g : {hom b, M c}) :
  bind g \o fmap f = bind [hom of g \o f].
Proof. rewrite funeqE => ?; exact: bind_fmap. Qed.

Lemma ret_naturality : naturalP (FId C) M' ret.
Proof. by move=> A B h; rewrite FIdf bindretf_fun. Qed.

Let bindE A B (f : {hom A, M' B}) : bind f = [hom of (join B) \o (M' # f)].
Proof.
rewrite /join.
rewrite hom_extext=>m.
rewrite /=bind_fmap/idfun/=.
congr (fun f => bind f m).
by rewrite hom_ext.
Qed.

Let fmap_bind a b c (f : {hom a,b}) m (g : {hom c,M a}) :
  (fmap f) (bind g m) = bind [hom of fmap f \o g] m.
Proof. by rewrite /fmap bindA bindE. Qed.

Lemma join_naturality : naturalP (FComp M' M') M' join.
Proof.
move => A B h.
rewrite /join /= funeqE => m /=.
rewrite fmap_bind bindA/=.
congr (fun f => bind f m).
rewrite hom_ext/=.
rewrite -[in RHS]hompA.
by rewrite bindretf_fun.
Qed.

Lemma joinretM : JoinLaws.join_left_unit ret' join.
Proof.
rewrite /join => A.
by rewrite bindretf_fun.
Qed.

Lemma joinMret : JoinLaws.join_right_unit ret' join.
Proof.
rewrite /join => A; rewrite funeqE => ma.
rewrite bind_fmap_fun/= -[in RHS](bindmret ma).
congr (fun f => bind f ma).
by rewrite hom_ext.
Qed.

Lemma joinA : JoinLaws.join_associativity join.
Proof.
move => A; rewrite funeqE => mmma.
rewrite /join.
rewrite bind_fmap_fun/= bindA/=.
congr (fun f => bind f mmma).
by rewrite hom_ext.
Qed.

Definition monad_mixin := Monad.Mixin
  ret_naturality join_naturality joinretM joinMret joinA.
End monad_of_bind_ret.
Module Exports.
Definition Monad_of_bind_ret C M bind ret a b c :=
  Monad.Pack (Monad.Class (@monad_mixin C M bind ret a b c)).
End Exports.
End Monad_of_bind_ret.
Export Monad_of_bind_ret.Exports.

(* wip *)
Section fmap_and_join.
Variable (C : category) (M : monad C).

Definition fmap A B (f : {hom A,B}) (m : El (M _)) := (M # f) m.

Lemma fmapE A B (f : {hom A, B}) (m : El (M _)) : fmap f m = m >>= [hom of (Ret \o f)].
Proof. by rewrite bindE functor_o (hom_homp Join) -hompA joinMret compidf. Qed.

End fmap_and_join.