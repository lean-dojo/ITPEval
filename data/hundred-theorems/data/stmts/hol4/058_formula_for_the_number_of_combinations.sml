(*
  Statement-only formalization of "Formula for the Number of Combinations"
  from Hundred Theorems item 058. For a finite set, the family of its subsets
  of a prescribed size has cardinality equal to the corresponding binomial
  coefficient. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory combinatoricsTheory pred_setTheory;

val formula_for_the_number_of_combinations =
  ``!n m (s : 'a set).
      s HAS_SIZE n ==>
      {t : 'a set | t SUBSET s /\ t HAS_SIZE m} HAS_SIZE binomial n m``;
