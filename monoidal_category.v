From mathcomp Require Import all_ssreflect.
From mathcomp Require Import boolp.
Require Import monae_lib category.

(*
In this file:

- product category (product of two categories)

M1. monoidal cateogories
M2. monoidal closed categories
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope category_scope.

(* A concrete category isomorphic to the product category of C and D *)
(* sum version *)
Module ProductCategory.
Section def.
Variable C D : category.
Definition obj := (C * D)%type.
Definition el_prod (X : obj) : Type := (el X.1 + el X.2)%type.
Definition separated (X Y : obj) (f : el_prod X -> el_prod Y) : Prop :=
  (forall x : el X.1, exists y : el Y.1, f (inl x) = inl y) /\
  (forall x : el X.2, exists y : el Y.2, f (inr x) = inr y).

Section sepfstsnd.
Let _sepfst (X Y : obj) (f : el_prod X -> el_prod Y) : separated f -> el X.1 -> el Y.1.
case=> H _ x.
move/cid: (H x)=> [] y _.
exact y.
Defined.
Definition sepfst := Eval hnf in _sepfst.
Let _sepsnd (X Y : obj) (f : el_prod X -> el_prod Y) : separated f -> el X.2 -> el Y.2.
case=> _ H x.
move/cid: (H x)=> [] y _.
exact y.
Defined.
Definition sepsnd := Eval hnf in _sepsnd.
End sepfstsnd.

Lemma sepfstK X Y (f : el_prod X -> el_prod Y) (Hf : separated f) (x : el X.1) :
  inl (sepfst Hf x) = f (inl x).
Proof.
move: f Hf x.
case: X=> X1 X2; case:Y=> Y1 Y2 /= f [] /= Hf1 Hf2 x.
by case: (cid (Hf1 x))=> y ->.
Qed.
Lemma sepsndK X Y (f : el_prod X -> el_prod Y) (Hf : separated f) (x : el X.2) :
  inr (sepsnd Hf x) = f (inr x).
Proof.
move: f Hf x.
case: X=> X1 X2; case:Y=> Y1 Y2 /= f [] /= Hf1 Hf2 x.
by case: (cid (Hf2 x))=> y ->.
Qed.
Definition inhom (A B : obj) (f : el_prod A -> el_prod B) : Prop :=
  exists H : separated f, InHom (sepfst H) /\ InHom (sepsnd H).
Lemma idfun_separated (X : obj) : @separated X X idfun.
Proof. by split; move=> x; exists x. Qed.
Lemma comp_separated (X Y Z : obj) (f :el_prod X -> el_prod Y) (g : el_prod Y -> el_prod Z) :
  separated f -> separated g -> separated (g \o f).
Proof.
move: f g.
case: X=> X1 X2; case: Y=> Y1 Y2; case: Z=> Z1 Z2 f g [] /= Hf1 Hf2 [] /= Hg1 Hg2; split.
- by move=> x; case/cid: (Hf1 x)=> y /= ->; case/cid: (Hg1 y)=> z /= ->; exists z.
- by move=> x; case/cid: (Hf2 x)=> y /= ->; case/cid: (Hg2 y)=> z /= ->; exists z.
Qed.
Lemma sepfst_idfun X : sepfst (idfun_separated X) = idfun.
Proof.
apply funext=> x /=.
suff: inl (B:=el X.2) (sepfst (idfun_separated X) x) = inl x by move=> [=].
by rewrite sepfstK.
Qed.
Lemma sepsnd_idfun X : sepsnd (idfun_separated X) = idfun.
Proof.
apply funext=> x /=.
suff: inr (A:=el X.1) (sepsnd (idfun_separated X) x) = inr x by move=> [=].
by rewrite sepsndK.
Qed.
Lemma sepfst_comp X Y Z (f : el_prod X -> el_prod Y) (g : el_prod Y -> el_prod Z)
      (Hf : separated f) (Hg : separated g) :
  sepfst (comp_separated Hf Hg) = sepfst Hg \o sepfst Hf.
Proof.
apply funext=> x /=.
suff: inl (B:=el Z.2) (sepfst (comp_separated Hf Hg) x) = inl (sepfst Hg (sepfst Hf x))
  by move => [=].
by rewrite 3!sepfstK.
Qed.
Lemma sepsnd_comp X Y Z (f : el_prod X -> el_prod Y) (g : el_prod Y -> el_prod Z)
      (Hf : separated f) (Hg : separated g) :
  sepsnd (comp_separated Hf Hg) = sepsnd Hg \o sepsnd Hf.
Proof.
apply funext=> x /=.
suff: inr (A:=el Z.1) (sepsnd (comp_separated Hf Hg) x) = inr (sepsnd Hg (sepsnd Hf x))
  by move => [=].
by rewrite 3!sepsndK.
Qed.
Definition mixin : Category.mixin_of (C * D).
refine (@Category.Mixin obj el_prod inhom _ _).
- by move=> X; exists (idfun_separated X); rewrite sepfst_idfun sepsnd_idfun; split; apply idfun_in_hom.
- by move=> X Y Z f g [] sf [] homfl homfr [] sg [] homgl homgr ; exists (comp_separated sf sg); rewrite sepfst_comp sepsnd_comp; split; apply funcomp_in_hom.
Defined.
End def.
End ProductCategory.
Definition productCategory (C D : category) := Category.Pack (ProductCategory.mixin C D).

Canonical productCategory.

Section prodcat_homfstsnd.
Variables A B : category.
Section homfstsnd.
Let _homfst (x y : A * B) (f : {hom x,y}) : {hom x.1, y.1}.
case:f => f.
case/cid=> sf [] Hf _.
exact: (HomPack _ _ _ Hf).
Defined.
Definition homfst := Eval hnf in _homfst.
Let _homsnd (x y : A * B) (f : {hom x,y}) : {hom x.2, y.2}.
case:f => f.
case/cid=> sf [] _ Hf.
exact: (HomPack _ _ _ Hf).
Defined.
Definition homsnd := Eval hnf in _homsnd.
End homfstsnd.
Lemma homfst_idfun x : homfst (x:=x) [hom idfun] = [hom idfun].
Proof.
apply/hom_ext; rewrite boolp.funeqE => x1 /=.
case: cid => i [i1 i2] /=.
rewrite (_ : i = ProductCategory.idfun_separated _) ?ProductCategory.sepfst_idfun //.
exact/Prop_irrelevance.
Qed.
Lemma homsnd_idfun x : homsnd (x:=x) [hom idfun] = [hom idfun].
Proof.
apply/hom_ext; rewrite boolp.funeqE => x1 /=.
case: cid => i [i1 i2] /=.
rewrite (_ : i = ProductCategory.idfun_separated _) ?ProductCategory.sepsnd_idfun //.
exact/Prop_irrelevance.
Qed.
Lemma homfst_comp (x y z : A * B) (f : {hom x,y}) (g : {hom y,z}) :
  homfst [hom g \o f] = [hom homfst g \o homfst f].
Proof.
rewrite /homfst /=.
case: cid => //= gh [gh1 gh2].
apply/hom_ext => /=.
destruct g as [g g'].
destruct f as [f f'].
case: cid => g_ [g1 g2].
case: cid => f_ [f1 f2] /=.
rewrite -ProductCategory.sepfst_comp.
congr (ProductCategory.sepfst _ _).
exact/Prop_irrelevance.
Qed.
Lemma homsnd_comp (x y z : A * B) (f : {hom x,y}) (g : {hom y,z}) :
  homsnd [hom g \o f] = [hom homsnd g \o homsnd f].
Proof.
rewrite /homsnd /=.
case: cid => //= gh [gh1 gh2].
apply/hom_ext => /=.
destruct g as [g g'].
destruct f as [f f'].
case: cid => g_ [g1 g2].
case: cid => f_ [f1 f2] /=.
rewrite -ProductCategory.sepsnd_comp.
congr (ProductCategory.sepsnd _ _).
exact/Prop_irrelevance.
Qed.
Lemma homfstK (x y : A * B) (f : {hom x,y}) (i : el x.1) : inl (homfst f i) = f (inl i).
Proof.
case: f=> /= f Hf.
case: (cid _)=> -[] sf1 sf2 [] Hf1 Hf2 /=.
by case: (cid _)=> j ->.
Qed.
Lemma homsndK (x y : A * B) (f : {hom x,y}) (i : el x.2) : inr (homsnd f i) = f (inr i).
Proof.
case: f=> /= f Hf.
case: (cid _)=> -[] sf1 sf2 [] Hf1 Hf2 /=.
by case: (cid _)=> j ->.
Qed.
End prodcat_homfstsnd.

Section prodCat_pairhom.
Variables A B : category.
Variables a1 a2 : A.
Variables b1 b2 : B.
Variables (f : {hom a1, a2}) (g : {hom b1, b2}).
Let C := productCategory A B.
Definition pairhom' (ab : el a1 + el b1) : el a2 + el b2 :=
  match ab with
  | inl a => inl (f a)
  | inr b => inr (g b)
  end.
Lemma pairhom'_in_hom :
  @InHom C _ _ (pairhom' : el (a1,b1).1 + el (a1,b1).2 ->
                           el (a2,b2).1 + el (a2,b2).2).
Proof.
rewrite /InHom /= /ProductCategory.inhom /=.
set s := ProductCategory.separated _.
have [/= s1 s2] : s by split => /= x; [exists (f x) | exists (g x)].
exists (conj s1 s2); split.
- set h := ProductCategory.sepfst _.
  rewrite (_ : h = f); first exact: Hom.class.
  by rewrite boolp.funeqE => ?; rewrite /h /=; case: cid => ? [].
- set h := ProductCategory.sepsnd _.
  rewrite (_ : h = g); first exact: Hom.class.
  by rewrite boolp.funeqE => ?; rewrite /h /=; case: cid => ? [].
Qed.
Definition pairhom : {hom (a1, b1), (a2, b2)} := Hom.Pack _ _ pairhom'_in_hom.
End prodCat_pairhom.

Section pairhom_idfun.
Variables (A B : category) (a : A) (b : B).
Lemma pairhom_idfun : pairhom (a1:=a) (b1:=b) [hom idfun] [hom idfun] = [hom idfun].
Proof. by apply/hom_ext/funext=> -[] x /=. Qed.
End pairhom_idfun.

Section pairhom_comp.
Variables (A B : category) (a1 a2 a3 : A) (b1 b2 b3 : B).
Variables (fa : {hom a1,a2}) (ga : {hom a2,a3}) (fb : {hom b1,b2}) (gb : {hom b2,b3}).
Lemma pairhom_comp : pairhom [hom ga \o fa] [hom gb \o fb] =
                     [hom pairhom ga gb \o pairhom fa fb].
Proof. by apply /hom_ext/funext=> -[] x. Qed.
End pairhom_comp.

(* couldn't avoid the horrible eq_rect *)
(*
Section pairhomK'.
Variables A B : category.
Variables x y : A * B.
Definition pairhomK'_eq : {hom x,y} = {hom (x.1, x.2), (y.1, y.2)}.
refine (match x with (x1,x2)=> _ end).
refine (match y with (y1,y2)=> _ end).
exact erefl.
Defined.
Lemma pairhomK' (f : {hom x,y}) : pairhom (homfst f) (homsnd f) =
                                 eq_rect _ id f _ pairhomK'_eq.
Proof.
rewrite /pairhomK'_eq.
move: x y f=> [] x1 x2 [] y1 y2 f /=.
apply/hom_ext/funext=> -[] i /=.
by rewrite -homfstK.
by rewrite -homsndK.
Qed.
End pairhomK'.
*)
Section pairhomK.
Variables A B : category.
Variables x1 x2 : A.
Variables y1 y2 : B.
Lemma pairhomK (f : {hom (x1,y1),(x2,y2)}) : pairhom (homfst f) (homsnd f) = f.
Proof.
apply/hom_ext/funext=> -[] i /=.
by rewrite -homfstK.
by rewrite -homsndK.
Qed.
End pairhomK.

Module papply_left.
Section def.
Variables A B C : category.
Variable F' : {functor (productCategory A B) -> C}.
Variable a : A.
Definition F_obj : B -> C := fun b => F' (a, b).
Definition F_mor (b1 b2 : B) (f : {hom b1, b2}) : {hom F_obj b1, F_obj b2} :=
  F' # pairhom (homid0 a) f.
Program Definition mixin_of := @Functor.Mixin _ _ F_obj F_mor _ _.
Next Obligation.
move=> D; rewrite /F_mor; set h := pairhom _ _.
rewrite (_ : h = [hom idfun]) ?functor_id_hom //.
by apply/hom_ext => /=; rewrite boolp.funeqE; case.
Qed.
Next Obligation.
move=> b b0 b1 g h; rewrite /F_mor; set i := pairhom _ _.
rewrite (_ : i = [hom (pairhom (homid0 a) g) \o
                         (pairhom (homid0 a) h)]) ?functor_o_hom //.
by apply/hom_ext => /=; rewrite boolp.funeqE; case.
Qed.
Definition F := Functor.Pack (Phant _) mixin_of.
End def.
End papply_left.

Module papply_right.
Section def.
Variables A B C : category.
Variable F' : {functor (productCategory A B) -> C}.
Variable b : B.
Definition F_obj : A -> C := fun a => F' (a, b).
Definition F_mor (a1 a2 : A) (f : {hom a1, a2}) : {hom F_obj a1, F_obj a2} :=
  F' # pairhom f (homid0 b).
Program Definition mixin_of := @Functor.Mixin _ _ F_obj F_mor _ _.
Next Obligation.
move=> D; rewrite /F_mor; set h := pairhom _ _.
rewrite (_ : h = [hom idfun]) ?functor_id_hom //.
by apply/hom_ext => /=; rewrite boolp.funeqE; case.
Qed.
Next Obligation.
move=> a a0 a1 g h; rewrite /F_mor; set i := pairhom _ _.
rewrite (_ : i = [hom (pairhom g (homid0 b)) \o
                         (pairhom h (homid0 b))]) ?functor_o_hom //.
by apply/hom_ext => /=; rewrite boolp.funeqE; case.
Qed.
Definition F := Functor.Pack (Phant _) mixin_of.
End def.
End papply_right.

Module ProductFunctor.
(* This notion does not have a proper name in the literature.
   "Product functor" is just a tentative naming,
   which unfortunately suffers a collision to another notion:
   the functor which maps two objects a, b \in C to their product a*b \in C
*)
Section def.
Variables A1 B1 A2 B2 : category.
Variables (F1 : {functor A1 -> B1}) (F2 : {functor A2 -> B2}).
Local Notation A := (A1 * A2)%type.
Local Notation B := (B1 * B2)%type.
Definition acto (x : A) : B := pair (F1 x.1) (F2 x.2).
Definition actm (x y : A) (f : {hom x,y}) : {hom acto x, acto y} :=
  pairhom (F1 # homfst f) (F2 # homsnd f).
Program Definition mixin_of := @Functor.Mixin _ _ acto actm _ _.
Next Obligation.
move=> a.
by rewrite /actm homfst_idfun homsnd_idfun 2!functor_id_hom pairhom_idfun.
Qed.
Next Obligation.
move=> [] a1 a2 [] b1 b2 [] c1 c2 g h.
by rewrite /actm homfst_comp homsnd_comp 2!functor_o_hom pairhom_comp.
Qed.
Definition F := Functor.Pack (Phant _) mixin_of.
End def.
End ProductFunctor.

Module alpha_left.
Section alpha_left.
Variables A B C D : category.
Variable F' : {functor (productCategory (productCategory A B) C) -> D}.
Variables (a : A) (b : B).
Definition acto : C -> D := papply_left.F F' (a, b).
Definition actm (c1 c2 : C) (f : {hom c1, c2}) : {hom acto c1, acto c2} :=
  F' # pairhom (homid0 (a, b)) f.
Program Definition mixin_of := @Functor.Mixin _ _ acto actm _ _.
Next Obligation.
move=> c0; rewrite /actm; set h := pairhom _ _.
rewrite (_ : h = [hom idfun]) ?functor_id_hom //.
by apply/hom_ext => /=; rewrite boolp.funeqE; case.
Qed.
Next Obligation.
move=> c c0 c1 g h; rewrite /actm; set i := pairhom _ _.
rewrite (_ : i = [hom (pairhom (homid0 (a, b)) g) \o
                         (pairhom (homid0 (a, b)) h)]) ?functor_o_hom //.
by apply/hom_ext => /=; rewrite boolp.funeqE; case.
Qed.
Definition F : {functor C -> D} := Functor.Pack (Phant _) mixin_of.
End alpha_left.
End alpha_left.

Module alpha_right.
Section alpha_right.
Variables A B C D : category.
Variable F' : {functor (productCategory A (productCategory B C)) -> D}.
Variables (a : A) (b : B).
Definition acto : C -> D := papply_left.F (papply_left.F F' a) b.
Definition actm (c1 c2 : C) (f : {hom c1, c2}) : {hom acto c1, acto c2}.
Admitted.
Program Definition mixin_of := @Functor.Mixin _ _ acto actm _ _.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Definition F : {functor C -> D} := Functor.Pack (Phant _) mixin_of.
End alpha_right.
End alpha_right.

Module prod_left.
Section prod_left.
Variable C : category.
Variable F' : {functor (productCategory C C) -> C}.
Let CCC := productCategory (productCategory C C) C.
Definition acto : CCC -> C := fun ccc => F' (F' ccc.1, ccc.2).
Definition actm (c1 c2 : CCC) (f : {hom c1, c2}) : {hom acto c1, acto c2}.
Admitted.
Program Definition mixin_of := @Functor.Mixin _ _ acto actm _ _.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Definition F : {functor CCC -> C} := Functor.Pack (Phant _) mixin_of.
End prod_left.
End prod_left.

Module prod_right.
Section prod_right.
Variable C : category.
Variable F' : {functor (productCategory C C) -> C}.
Let CCC := productCategory C (productCategory C C).
Definition acto : CCC -> C := fun ccc => F' (ccc.1, F' ccc.2).
Definition actm (c1 c2 : CCC) (f : {hom c1, c2}) : {hom acto c1, acto c2} :=
  F' # (pairhom (homfst f) (F' # (homsnd f))).
Program Definition mixin_of := @Functor.Mixin _ _ acto actm _ _.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Definition F : {functor (productCategory C (productCategory C C)) -> C}.
Admitted.
End prod_right.
End prod_right.

Module ProductCategoryAssoc.
Section def.
Variables A B C : category.
Definition acto (x : A * (B * C)) : A * B * C :=  match x with (a,(b,c)) => ((a,b),c) end.
Definition actm (x y : A * (B * C)) : {hom x,y} -> {hom acto x, acto y} :=
match x with (xa,(xb,xc)) => match y with (ya,(yb,yc)) => fun f => pairhom (pairhom (homfst f) (homfst (homsnd f))) (homsnd (homsnd f)) end end.
Program Definition mixin_of := @Functor.Mixin _ _ acto actm _ _ .
Next Obligation.
case=> a [] b c.
by rewrite /actm 2!homsnd_idfun 2!homfst_idfun 2!pairhom_idfun.
Qed.
Next Obligation.
case=> xa [] xb xc [] ya [] yb yc [] za [] zb zc g h.
by rewrite /actm !homsnd_comp !homfst_comp !pairhom_comp.
Qed.
Definition F := Functor.Pack (Phant _) mixin_of.
End def.
End ProductCategoryAssoc.

Module MonoidalCategory.
Section def.
Import comps_notation.
Record mixin_of (C : category) : Type := Mixin {
  I : C;
  prod : {functor (productCategory C C) -> C};
  lambda : papply_left.F prod I ~> FId ;
  rho : papply_right.F prod I ~> FId ;
(*  alpha' : forall (x y z : C), el (prod (prod (x,y), z)) -> el (prod (x, prod (y, z))) ;*)
  (*alpha : forall a b, alpha_left.F (prod_left.F prod) a b ~> alpha_right.F (prod_right.F prod) a b ;*)
  alpha : prod \O (ProductFunctor.F FId prod) ~> prod \O (ProductFunctor.F prod FId) \O ProductCategoryAssoc.F _ _ _
}.
Section scratch_pad.
Variable C : category.
Variable m : mixin_of C.
Variable x : C.
Variable y : C.
Check (prod m # pairhom (rho m x) (NId FId y)).
Definition h : {hom alpha_right.F (prod_right.F (prod m)) x (I m) y, prod m (FId x, papply_left.F (prod m) (I m) y)}.
have f : el (alpha_right.F (prod_right.F (prod m)) x (I m) y) -> el (prod m (FId x, papply_left.F (prod m) (I m) y)).
  rewrite /alpha_right.F /=.
  rewrite /alpha_right.acto /=.
  rewrite /papply_left.F_obj /=.
Abort.
End scratch_pad.
Record class_of (T : Type) : Type := Class {
 base : Category.mixin_of T;
 mixin : mixin_of (Category.Pack base);
}.
Structure t : Type := Pack { T : Type; class : class_of T }.
End def.
Module Exports.
End Exports.
End MonoidalCategory.
Export MonoidalCategory.Exports.


(* TODO *)
(*
Module BifunctorLaws.
Section def.
Variable (A B C : category).
Variable (M : A * B -> C) (f : forall A B, {hom A,B} -> {hom M A, M B}).
Definition id := forall A, f [hom idfun] = [hom idfun] :> {hom M A,M A}.
Definition comp := forall A B C (g : {hom B,C}) (h : {hom A,B}),
  f [hom g \o h] = [hom f g \o f h] :> {hom M A,M C}.
End def.
End FunctorLaws.

Module Bifunctor.
Record mixin_of (C D : category) (m : C -> D) : Type := Mixin {
  f : forall A B, {hom A, B} -> {hom m A, m B} ;
  _ : FunctorLaws.id f ;
  _ : FunctorLaws.comp f }.
Structure t (C D : category) : Type := Pack { m : C -> D ; class : mixin_of m }.
Module Exports.
Section exports.
Variables (C D : category).
Definition Fun (F : t C D) : forall A B, {hom A, B} -> {hom m F A, m F B} :=
  let: Pack _ (Mixin f _ _) := F return forall A B, {hom A, B} -> {hom m F A, m F B} in f.
Arguments Fun _ [A] [B] : simpl never.
End exports.
Notation functor := t.
Coercion m : functor >-> Funclass.
End Exports.
End Functor.
Export Functor.Exports.
Notation "F # f" := (Fun F f).
 *)

(*
(* TODO: figure out what the construction below is *)
(* A similar construction.
   Related to another tensor product in Cat, like the funny tensor? *)
Module WeirdProductCategory.
Section def.
Variable C D : category.
Definition obj := (C * D)%type.
Definition el_prod (X : obj) : Type := (el X.1 * el X.2)%type.
Definition independent (X Y : obj) (f : el_prod X -> el_prod Y) : Prop :=
  (forall (x : el X.1) (y y' : el X.2), fst (f (x,y)) = fst (f (x,y'))) /\
  (forall (x x': el X.1) (y : el X.2), snd (f (x,y)) = snd (f (x',y))).

Section homfstsnd.
Let _homfst (X Y : obj) (f : el_prod X -> el_prod Y) : independent f -> el X.1 -> el Y.1.
case=> H _ x.
move/cid: (H x)=> [] y _.
exact y.
Defined.
Definition homfst := Eval hnf in _homfst.
Let _homsnd (X Y : obj) (f : el_prod X -> el_prod Y) : separated f -> el X.2 -> el Y.2.
case=> _ H x.
move/cid: (H x)=> [] y _.
exact y.
Defined.
Definition homsnd := Eval hnf in _homsnd.
End homfstsnd.

Lemma homfstK X Y (f : el_prod X -> el_prod Y) (Hf : separated f) (x : el X.1) :
  inl (homfst Hf x) = f (inl x).
Proof.
move: f Hf x.
case: X=> X1 X2; case:Y=> Y1 Y2 /= f [] /= Hf1 Hf2 x.
by case: (cid (Hf1 x))=> y ->.
Qed.
Lemma homsndK X Y (f : el_prod X -> el_prod Y) (Hf : separated f) (x : el X.2) :
  inr (homsnd Hf x) = f (inr x).
Proof.
move: f Hf x.
case: X=> X1 X2; case:Y=> Y1 Y2 /= f [] /= Hf1 Hf2 x.
by case: (cid (Hf2 x))=> y ->.
Qed.
Definition inhom (A B : obj) (f : el_prod A -> el_prod B) : Prop :=
  exists H : separated f, InHom (homfst H) /\ InHom (homsnd H).
Lemma idfun_separated (X : obj) : @separated X X idfun.
Proof. by split; move=> x; exists x. Qed.
Lemma comp_separated (X Y Z : obj) (f :el_prod X -> el_prod Y) (g : el_prod Y -> el_prod Z) :
  separated f -> separated g -> separated (g \o f).
Proof.
move: f g.
case: X=> X1 X2; case: Y=> Y1 Y2; case: Z=> Z1 Z2 f g [] /= Hf1 Hf2 [] /= Hg1 Hg2; split.
- by move=> x; case/cid: (Hf1 x)=> y /= ->; case/cid: (Hg1 y)=> z /= ->; exists z.
- by move=> x; case/cid: (Hf2 x)=> y /= ->; case/cid: (Hg2 y)=> z /= ->; exists z.
Qed.
Lemma homfst_idfun X : homfst (idfun_separated X) = idfun.
Proof.
apply funext=> x /=.
suff: inl (B:=el X.2) (homfst (idfun_separated X) x) = inl x by move=> [=].
by rewrite homfstK.
Qed.
Lemma homsnd_idfun X : homsnd (idfun_separated X) = idfun.
Proof.
apply funext=> x /=.
suff: inr (A:=el X.1) (homsnd (idfun_separated X) x) = inr x by move=> [=].
by rewrite homsndK.
Qed.
Lemma homfst_comp X Y Z (f : el_prod X -> el_prod Y) (g : el_prod Y -> el_prod Z)
      (Hf : separated f) (Hg : separated g) :
  homfst (comp_separated Hf Hg) = homfst Hg \o homfst Hf.
Proof.
apply funext=> x /=.
suff: inl (B:=el Z.2) (homfst (comp_separated Hf Hg) x) = inl (homfst Hg (homfst Hf x))
  by move => [=].
by rewrite 3!homfstK.
Qed.
Lemma homsnd_comp X Y Z (f : el_prod X -> el_prod Y) (g : el_prod Y -> el_prod Z)
      (Hf : separated f) (Hg : separated g) :
  homsnd (comp_separated Hf Hg) = homsnd Hg \o homsnd Hf.
Proof.
apply funext=> x /=.
suff: inr (A:=el Z.1) (homsnd (comp_separated Hf Hg) x) = inr (homsnd Hg (homsnd Hf x))
  by move => [=].
by rewrite 3!homsndK.
Qed.
Definition mixin : Category.mixin_of (C * D).
refine (@Category.Mixin obj el_prod inhom _ _).
- by move=> X; exists (idfun_separated X); rewrite homfst_idfun homsnd_idfun; split; apply idfun_in_hom.
- by move=> X Y Z f g [] sf [] homfl homfr [] sg [] homgl homgr ; exists (comp_separated sf sg); rewrite homfst_comp homsnd_comp; split; apply funcomp_in_hom.
Defined.
End def.
End WeirdProductCategory.
*)
