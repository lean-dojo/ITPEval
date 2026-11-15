(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1996_b1:
  the number of minimal selfish subsets of {1,...,n}, where a set is selfish
  when it contains its own cardinality, is the nth Fibonacci number. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val putnam_1996_b1 =
  ``let is_fibonacci =
      \f : num -> num.
        f 0 = 0 /\
        f 1 = 1 /\
        (!k : num. f (k + 2) = f k + f (k + 1))
    in
    let solution =
      @f : num -> num. is_fibonacci f
    in
      !n : num.
        1 <= n
        ==>
        CARD
          {s : num set |
             s SUBSET IMAGE SUC (count n) /\
             CARD s IN s /\
             (!ss : num set.
                ss PSUBSET s
                ==>
                ~(CARD ss IN ss))} =
        solution n``;
