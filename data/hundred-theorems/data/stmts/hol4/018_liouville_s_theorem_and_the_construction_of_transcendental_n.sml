(*
  Statement-only formalization of "Liouville's Theorem and the Construction of Transcendental
  Numbers" from Hundred Theorems item 018. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pred_setTheory realTheory intrealTheory
     real_sigmaTheory;

val liouville_numbers_are_transcendental =
  ``!x : real.
      (!n : num.
         ?a b : int.
           1 < b /\
           x <> real_of_int a / real_of_int b /\
           abs (x - real_of_int a / real_of_int b) <
             1 / (real_of_int b pow n))
      ==>
      !p : num -> int.
        FINITE {k | p k <> 0} /\
        (?k. p k <> 0)
        ==>
        SIGMA
          (\k. real_of_int (p k) * x pow k)
          {k | p k <> 0} <> 0``;
