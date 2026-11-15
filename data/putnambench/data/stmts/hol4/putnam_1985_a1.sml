(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1985_a1:
  the number of ordered triples of sets with union {1,...,10} and empty
  triple intersection, expressed by its prime exponents. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val putnam_1985_a1 =
  ``let putnam_1985_a1_solution =
      ((10, 10), (0, 0)) : (num # num) # (num # num)
    in
    let base = IMAGE SUC (count 10)
    in
      CARD
        {A : (num set # num set) # num set |
           FST (FST A) UNION SND (FST A) UNION SND A = base /\
           FST (FST A) INTER SND (FST A) INTER SND A = EMPTY} =
      2 EXP FST (FST putnam_1985_a1_solution) *
      3 EXP SND (FST putnam_1985_a1_solution) *
      5 EXP FST (SND putnam_1985_a1_solution) *
      7 EXP SND (SND putnam_1985_a1_solution)``;
