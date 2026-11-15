(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1983_a4:
  for m = 6*k - 1 with positive k, the alternating sum of the binomial
  coefficients indexed by 3*j - 1 for j from 1 through 2*k - 1 is nonzero.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory combinatoricsTheory integerTheory listTheory;

val putnam_1983_a4 =
  ``!k m : num. !S : int.
      0 < k /\
      m = 6 * k - 1 /\
      S =
        FOLDL
          (\acc : int. \j : num.
             acc +
             (~1 : int) ** (j + 1) *
             int_of_num (binomial m (3 * j - 1)))
          0
          (GENLIST SUC (2 * k - 1))
      ==>
      S <> 0``;
