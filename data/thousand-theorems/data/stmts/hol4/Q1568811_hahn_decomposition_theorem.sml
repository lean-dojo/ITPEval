(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1568811 (thousand-theorems__hol4__Q1568811), "Hahn decomposition
  theorem": every real-valued signed measure on a measurable space has
  complementary measurable positive and negative sets. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;
open sigma_algebraTheory;

val q1568811_has_sum_def = new_definition (
  "q1568811_has_sum_def",
  ``q1568811_has_sum (f : num -> real) (a : real) <=>
      !e : real.
        0 < e ==>
        ?base : num set.
          FINITE base /\
          !u : num set.
            FINITE u /\ base SUBSET u ==>
            abs (SIGMA f u - a) < e``);

val q1568811_signed_measure_def = new_definition (
  "q1568811_signed_measure_def",
  ``q1568811_signed_measure
      (msets : 'a set set) (s : 'a set -> real) <=>
      sigma_algebra ((UNIV : 'a set), msets) /\
      s {} = 0 /\
      (!u : 'a set. u NOTIN msets ==> s u = 0) /\
      !sets : num -> 'a set.
        (!n. sets n IN msets) /\
        (!m n. m <> n ==> DISJOINT (sets m) (sets n))
        ==>
        q1568811_has_sum
          (\n. s (sets n))
          (s (BIGUNION (IMAGE sets UNIV)))``);

val q1568811_positive_set_def = new_definition (
  "q1568811_positive_set_def",
  ``q1568811_positive_set
      (msets : 'a set set) (s : 'a set -> real)
      (i : 'a set) <=>
      !u : 'a set.
        u IN msets /\ u SUBSET i ==> 0 <= s u``);

val q1568811_negative_set_def = new_definition (
  "q1568811_negative_set_def",
  ``q1568811_negative_set
      (msets : 'a set set) (s : 'a set -> real)
      (j : 'a set) <=>
      !u : 'a set.
        u IN msets /\ u SUBSET j ==> s u <= 0``);

val hahn_decomposition_theorem =
  ``!(msets : 'a set set) (s : 'a set -> real).
      q1568811_signed_measure msets s
      ==>
      ?i j : 'a set.
        i IN msets /\
        q1568811_positive_set msets s i /\
        j IN msets /\
        q1568811_negative_set msets s j /\
        DISJOINT i j /\
        i UNION j = UNIV``;
