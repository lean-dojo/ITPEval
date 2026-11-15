(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2011_b6:
  for an odd prime p, at least (p + 1) / 2 residues below p make the
  factorial polynomial sum from k = 0 to p - 1 nondivisible by p. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory pred_setTheory primeTheory;

val putnam_2011_b6 =
  ``!p : num.
      ODD p /\ prime p
      ==>
      (p + 1) DIV 2 <=
        CARD
          {n : num |
             n < p /\
             ~(p divides
                 SIGMA
                   (\k : num. FACT k * n EXP k)
                   (count p))}``;
