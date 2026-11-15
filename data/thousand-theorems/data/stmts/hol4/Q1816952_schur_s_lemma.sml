(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1816952, "Schur's lemma": over an algebraically closed field, the
  finite-dimensional endomorphism space of a simple object in a linear
  preadditive category with kernels is one-dimensional. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory listTheory;

val q1816952_hom_def = new_definition (
  "q1816952_hom_def",
  ``q1816952_hom
      (dom : 'mor -> 'obj) (cod : 'mor -> 'obj)
      (f : 'mor) (X : 'obj) (Y : 'obj) <=>
      dom f = X /\ cod f = Y``);

val q1816952_field_def = new_definition (
  "q1816952_field_def",
  ``q1816952_field
      (kzero : 'k) (kone : 'k)
      (kadd : 'k -> 'k -> 'k) (kmul : 'k -> 'k -> 'k)
      (kneg : 'k -> 'k) (kinv : 'k -> 'k) <=>
      kzero <> kone /\
      (!a b. kadd a b = kadd b a) /\
      (!a b c. kadd (kadd a b) c = kadd a (kadd b c)) /\
      (!a. kadd kzero a = a) /\
      (!a. kadd (kneg a) a = kzero) /\
      (!a b. kmul a b = kmul b a) /\
      (!a b c. kmul (kmul a b) c = kmul a (kmul b c)) /\
      (!a. kmul kone a = a) /\
      (!a b c. kmul a (kadd b c) = kadd (kmul a b) (kmul a c)) /\
      kinv kzero = kzero /\
      (!a. a <> kzero ==> kmul (kinv a) a = kone)``);

val q1816952_poly_eval_def = new_definition (
  "q1816952_poly_eval_def",
  ``q1816952_poly_eval
      (kzero : 'k) (kadd : 'k -> 'k -> 'k)
      (kmul : 'k -> 'k -> 'k) (coeffs : 'k list) (x : 'k) =
      FOLDR (\c acc. kadd c (kmul x acc)) kzero coeffs``);

val q1816952_algebraically_closed_def = new_definition (
  "q1816952_algebraically_closed_def",
  ``q1816952_algebraically_closed
      (kzero : 'k) (kadd : 'k -> 'k -> 'k)
      (kmul : 'k -> 'k -> 'k) <=>
      !coeffs : 'k list.
        1 < LENGTH coeffs /\ LAST coeffs <> kzero ==>
        ?x : 'k. q1816952_poly_eval kzero kadd kmul coeffs x = kzero``);

val q1816952_category_def = new_definition (
  "q1816952_category_def",
  ``q1816952_category
      (dom : 'mor -> 'obj) (cod : 'mor -> 'obj)
      (id : 'obj -> 'mor) (comp : 'mor -> 'mor -> 'mor) <=>
      (!X. q1816952_hom dom cod (id X) X X) /\
      (!X Y Z f g.
        q1816952_hom dom cod f X Y /\
        q1816952_hom dom cod g Y Z ==>
        q1816952_hom dom cod (comp g f) X Z) /\
      (!X Y f.
        q1816952_hom dom cod f X Y ==>
        comp (id Y) f = f /\ comp f (id X) = f) /\
      (!W X Y Z f g h.
        q1816952_hom dom cod f W X /\
        q1816952_hom dom cod g X Y /\
        q1816952_hom dom cod h Y Z ==>
        comp h (comp g f) = comp (comp h g) f)``);

val q1816952_preadditive_def = new_definition (
  "q1816952_preadditive_def",
  ``q1816952_preadditive
      (dom : 'mor -> 'obj) (cod : 'mor -> 'obj)
      (comp : 'mor -> 'mor -> 'mor)
      (mzero : 'obj -> 'obj -> 'mor)
      (madd : 'mor -> 'mor -> 'mor) (mneg : 'mor -> 'mor) <=>
      (!X Y. q1816952_hom dom cod (mzero X Y) X Y) /\
      (!X Y f g.
        q1816952_hom dom cod f X Y /\
        q1816952_hom dom cod g X Y ==>
        q1816952_hom dom cod (madd f g) X Y) /\
      (!X Y f.
        q1816952_hom dom cod f X Y ==>
        q1816952_hom dom cod (mneg f) X Y) /\
      (!X Y f g.
        q1816952_hom dom cod f X Y /\
        q1816952_hom dom cod g X Y ==>
        madd f g = madd g f) /\
      (!X Y f g h.
        q1816952_hom dom cod f X Y /\
        q1816952_hom dom cod g X Y /\
        q1816952_hom dom cod h X Y ==>
        madd (madd f g) h = madd f (madd g h)) /\
      (!X Y f.
        q1816952_hom dom cod f X Y ==>
        madd (mzero X Y) f = f /\
        madd (mneg f) f = mzero X Y) /\
      (!X Y Z f g h.
        q1816952_hom dom cod f X Y /\
        q1816952_hom dom cod g X Y /\
        q1816952_hom dom cod h Y Z ==>
        comp h (madd f g) = madd (comp h f) (comp h g)) /\
      (!X Y Z f g h.
        q1816952_hom dom cod f Y Z /\
        q1816952_hom dom cod g Y Z /\
        q1816952_hom dom cod h X Y ==>
        comp (madd f g) h = madd (comp f h) (comp g h)) /\
      (!X Y Z f.
        q1816952_hom dom cod f X Y ==>
        comp (mzero Y Z) f = mzero X Z) /\
      (!X Y Z f.
        q1816952_hom dom cod f Y Z ==>
        comp f (mzero X Y) = mzero X Z)``);

val q1816952_linear_category_def = new_definition (
  "q1816952_linear_category_def",
  ``q1816952_linear_category
      (dom : 'mor -> 'obj) (cod : 'mor -> 'obj)
      (comp : 'mor -> 'mor -> 'mor)
      (kzero : 'k) (kone : 'k)
      (kadd : 'k -> 'k -> 'k) (kmul : 'k -> 'k -> 'k)
      (mzero : 'obj -> 'obj -> 'mor)
      (madd : 'mor -> 'mor -> 'mor)
      (smul : 'k -> 'mor -> 'mor) <=>
      (!X Y a f.
        q1816952_hom dom cod f X Y ==>
        q1816952_hom dom cod (smul a f) X Y) /\
      (!X Y f.
        q1816952_hom dom cod f X Y ==>
        smul kone f = f /\ smul kzero f = mzero X Y) /\
      (!X Y a b f.
        q1816952_hom dom cod f X Y ==>
        smul (kadd a b) f = madd (smul a f) (smul b f)) /\
      (!X Y a b f.
        q1816952_hom dom cod f X Y ==>
        smul (kmul a b) f = smul a (smul b f)) /\
      (!X Y a f g.
        q1816952_hom dom cod f X Y /\
        q1816952_hom dom cod g X Y ==>
        smul a (madd f g) = madd (smul a f) (smul a g)) /\
      (!X Y Z a f g.
        q1816952_hom dom cod f X Y /\
        q1816952_hom dom cod g Y Z ==>
        comp g (smul a f) = smul a (comp g f) /\
        comp (smul a g) f = smul a (comp g f))``);

val q1816952_has_kernels_def = new_definition (
  "q1816952_has_kernels_def",
  ``q1816952_has_kernels
      (dom : 'mor -> 'obj) (cod : 'mor -> 'obj)
      (comp : 'mor -> 'mor -> 'mor)
      (mzero : 'obj -> 'obj -> 'mor) <=>
      !X Y f.
        q1816952_hom dom cod f X Y ==>
        ?K k.
          q1816952_hom dom cod k K X /\
          comp f k = mzero K Y /\
          !Z g.
            q1816952_hom dom cod g Z X /\
            comp f g = mzero Z Y ==>
            ?!l.
              q1816952_hom dom cod l Z K /\
              comp k l = g``);

val q1816952_mono_def = new_definition (
  "q1816952_mono_def",
  ``q1816952_mono
      (dom : 'mor -> 'obj) (cod : 'mor -> 'obj)
      (comp : 'mor -> 'mor -> 'mor)
      (f : 'mor) (X : 'obj) (Y : 'obj) <=>
      q1816952_hom dom cod f X Y /\
      !Z g h.
        q1816952_hom dom cod g Z X /\
        q1816952_hom dom cod h Z X /\
        comp f g = comp f h ==>
        g = h``);

val q1816952_iso_def = new_definition (
  "q1816952_iso_def",
  ``q1816952_iso
      (dom : 'mor -> 'obj) (cod : 'mor -> 'obj)
      (id : 'obj -> 'mor) (comp : 'mor -> 'mor -> 'mor)
      (f : 'mor) (X : 'obj) (Y : 'obj) <=>
      q1816952_hom dom cod f X Y /\
      ?g.
        q1816952_hom dom cod g Y X /\
        comp g f = id X /\
        comp f g = id Y``);

val q1816952_simple_def = new_definition (
  "q1816952_simple_def",
  ``q1816952_simple
      (dom : 'mor -> 'obj) (cod : 'mor -> 'obj)
      (id : 'obj -> 'mor) (comp : 'mor -> 'mor -> 'mor)
      (mzero : 'obj -> 'obj -> 'mor) (X : 'obj) <=>
      id X <> mzero X X /\
      !Y f.
        q1816952_mono dom cod comp f Y X ==>
        f = mzero Y X \/ q1816952_iso dom cod id comp f Y X``);

val q1816952_lincomb_def = new_definition (
  "q1816952_lincomb_def",
  ``q1816952_lincomb
      (kzero : 'k)
      (mzero : 'obj -> 'obj -> 'mor)
      (madd : 'mor -> 'mor -> 'mor)
      (smul : 'k -> 'mor -> 'mor)
      (X : 'obj) (basis : 'mor list) (coeff : num -> 'k) =
      FOLDL
        (\acc i. madd acc (smul (coeff i) (EL i basis)))
        (mzero X X)
        (GENLIST (\i. i) (LENGTH basis))``);

val q1816952_basis_def = new_definition (
  "q1816952_basis_def",
  ``q1816952_basis
      (dom : 'mor -> 'obj) (cod : 'mor -> 'obj)
      (kzero : 'k)
      (mzero : 'obj -> 'obj -> 'mor)
      (madd : 'mor -> 'mor -> 'mor)
      (smul : 'k -> 'mor -> 'mor)
      (X : 'obj) (basis : 'mor list) <=>
      EVERY (\b. q1816952_hom dom cod b X X) basis /\
      ALL_DISTINCT basis /\
      (!coeff : num -> 'k.
        q1816952_lincomb kzero mzero madd smul X basis coeff =
          mzero X X ==>
        !i. i < LENGTH basis ==> coeff i = kzero) /\
      (!f.
        q1816952_hom dom cod f X X ==>
        ?coeff : num -> 'k.
          q1816952_lincomb kzero mzero madd smul X basis coeff = f)``);

val q1816952_finite_dimensional_def = new_definition (
  "q1816952_finite_dimensional_def",
  ``q1816952_finite_dimensional
      (dom : 'mor -> 'obj) (cod : 'mor -> 'obj)
      (kzero : 'k)
      (mzero : 'obj -> 'obj -> 'mor)
      (madd : 'mor -> 'mor -> 'mor)
      (smul : 'k -> 'mor -> 'mor) (X : 'obj) <=>
      ?basis : 'mor list.
        q1816952_basis dom cod kzero mzero madd smul X basis``);

val q1816952_one_dimensional_def = new_definition (
  "q1816952_one_dimensional_def",
  ``q1816952_one_dimensional
      (dom : 'mor -> 'obj) (cod : 'mor -> 'obj)
      (kzero : 'k)
      (mzero : 'obj -> 'obj -> 'mor)
      (madd : 'mor -> 'mor -> 'mor)
      (smul : 'k -> 'mor -> 'mor) (X : 'obj) <=>
      ?b : 'mor.
        q1816952_basis dom cod kzero mzero madd smul X [b]``);

val finrank_endomorphism_simple_eq_one =
  ``!(kzero : 'k) (kone : 'k)
      (kadd : 'k -> 'k -> 'k) (kmul : 'k -> 'k -> 'k)
      (kneg : 'k -> 'k) (kinv : 'k -> 'k)
      (dom : 'mor -> 'obj) (cod : 'mor -> 'obj)
      (id : 'obj -> 'mor) (comp : 'mor -> 'mor -> 'mor)
      (mzero : 'obj -> 'obj -> 'mor)
      (madd : 'mor -> 'mor -> 'mor) (mneg : 'mor -> 'mor)
      (smul : 'k -> 'mor -> 'mor) (X : 'obj).
      q1816952_field kzero kone kadd kmul kneg kinv /\
      q1816952_algebraically_closed kzero kadd kmul /\
      q1816952_category dom cod id comp /\
      q1816952_preadditive dom cod comp mzero madd mneg /\
      q1816952_linear_category
        dom cod comp kzero kone kadd kmul mzero madd smul /\
      q1816952_has_kernels dom cod comp mzero /\
      q1816952_simple dom cod id comp mzero X /\
      q1816952_finite_dimensional
        dom cod kzero mzero madd smul X
      ==>
      q1816952_one_dimensional
        dom cod kzero mzero madd smul X``;
