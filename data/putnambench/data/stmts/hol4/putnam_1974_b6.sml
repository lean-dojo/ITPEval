(*
  Statement-only formalization of PutnamBench artifact putnam_1974_b6:
  the numbers of subsets of {1,...,1000} whose cardinalities are congruent
  to 0, 1, and 2 modulo 3. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val putnam_1974_b6 =
  ``let base = IMAGE SUC (count 1000) in
    let subset_count =
      \r : num.
        CARD
          {s : num set |
             s SUBSET base /\ CARD s MOD 3 = r}
    in
    let q = (2 EXP 1000 - 1) DIV 3 in
      (subset_count 0, subset_count 1, subset_count 2) =
      (q, q, q + 1)``;
