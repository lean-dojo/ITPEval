(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q2631152 (thousand-theorems__hol4__Q2631152), "Carathéodory's extension
  theorem": a nonnegative sigma-subadditive additive content on a set
  semiring induces a measure on the generated sigma-algebra that agrees with
  the content on every set of the semiring. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory iterateTheory extrealTheory;
open sigma_algebraTheory measureTheory;

val q2631152_add_content_def = new_definition (
  "q2631152_add_content_def",
  ``q2631152_add_content
      (C : 'a set set) (mu : 'a set -> extreal) <=>
      (!u. 0 <= mu u) /\
      mu {} = 0 /\
      !I : 'a set set.
        I SUBSET C /\
        FINITE I /\
        disjoint I /\
        BIGUNION I IN C
        ==>
        mu (BIGUNION I) = SIGMA mu I``);

val q2631152_sigma_subadditive_def = new_definition (
  "q2631152_sigma_subadditive_def",
  ``q2631152_sigma_subadditive
      (C : 'a set set) (mu : 'a set -> extreal) <=>
      !f : num -> 'a set.
        (!i. f i IN C) /\
        BIGUNION (IMAGE f UNIV) IN C
        ==>
        mu (BIGUNION (IMAGE f UNIV)) <= suminf (mu o f)``);

val q2631152_generated_measure_def = new_definition (
  "q2631152_generated_measure_def",
  ``q2631152_generated_measure
      (a : 'a algebra) (C : 'a set set) (mu : 'a set -> extreal) =
      (space a,
       subsets a,
       outer_measure mu (countable_covers C))``);

val caratheodory_extension_measure_eq =
  ``!(a : 'a algebra) (C : 'a set set)
      (mu : 'a set -> extreal) (s : 'a set).
      a = sigma UNIV C /\
      semiring (UNIV,C) /\
      q2631152_add_content C mu /\
      q2631152_sigma_subadditive C mu /\
      s IN C
      ==>
      measure (q2631152_generated_measure a C mu) s = mu s``;
