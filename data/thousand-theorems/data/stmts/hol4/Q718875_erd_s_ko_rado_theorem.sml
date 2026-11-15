(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q718875, "Erdős–Ko–Rado theorem": an intersecting family of r-element
  subsets of Fin n has size at most (n - 1) choose (r - 1) when r <= n / 2.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val q718875_binomial_def = new_definition (
  "q718875_binomial_def",
  ``q718875_binomial (n : num) (k : num) =
      CARD {s : num set | s SUBSET count n /\ CARD s = k}``);

val erdos_ko_rado =
  ``!n r : num. !family : (num set) set.
      FINITE family /\
      (!s. s IN family ==>
          FINITE s /\ s SUBSET count n /\ CARD s = r) /\
      (!s t. s IN family /\ t IN family ==> ~(DISJOINT s t)) /\
      r <= n DIV 2
      ==>
      CARD family <= q718875_binomial (n - 1) (r - 1)``;
