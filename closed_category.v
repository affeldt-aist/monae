From mathcomp Require Import all_ssreflect.
From mathcomp Require Import boolp.
Require Import monae_lib category.

(*
In this file:
1. categories with finite products
2. categories with pullbacks
2.99. universal arrow (for defining 3)
3. finitely complete categories (categories with finite limits)
4. categories with morphism comprehension
5. cartesian closed categories

3 subsumes 1 and 2.
5 = 1 + 4 + exponentiation axiom.


In monoidal_category.v:
M1. monoidal cateogories
M2. monoidal closed categories

M2 subsumes 5.
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope category_scope.

Module CatWithFinProd.
Section def.
Record mixin_of (C : category) : Type := Mixin {
 prod : C -> C -> C;
 fst : forall a b, {hom prod a b, a};
 snd : forall a b, {hom prod a b, b};
 univ : forall c a b, {hom c,a} -> {hom c,b} -> {hom c, prod a b};
 _ : forall c a b (f : {hom c,a}) (g : {hom c,b}),
     f = [hom (fst a b) \o (univ f g)];
}.
Record class_of (T : Type) : Type := Class {
 base : Category.mixin_of T;
 mixin : mixin_of (Category.Pack base);
}.
Structure t : Type := Pack { T : Type; class : class_of T }.
End def.
Module Exports.
End Exports.
End CatWithFinProd.
Export CatWithFinProd.Exports.
