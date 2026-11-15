(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1981_b5:
  the rationality of the exponential of the infinite series formed from the
  number of ones in each positive integer's binary expansion. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory ratTheory realTheory real_of_ratTheory
     seqTheory transcTheory;

val putnam_1981_b5 =
  ``let B =
      \n : num.
        CARD {k : num | ODD (n DIV (2 EXP k))}
    in
      ((?q : rat.
          exp
            (suminf
               (\n : num.
                  (&(B (n + 1)) : real) /
                  (&(n + 1) * &(n + 2)))) =
          real_of_rat q)
       <=> T)``;
