(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2003_b3:
  the factorial of a natural number is the product, over its positive indices,
  of the least common multiples of the corresponding initial quotient ranges.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory combinatoricsTheory listTheory;

val putnam_2003_b3 =
  ``!n : num.
      FACT n =
        PROD
          (GENLIST
             (\j : num.
                list_lcm (GENLIST SUC (n DIV SUC j)))
             n)``;
