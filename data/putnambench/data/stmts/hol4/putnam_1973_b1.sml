(*
  Statement-only formalization of PutnamBench artifact putnam_1973_b1:
  deleting any one of 2n+1 indexed integers leaves two n-element parts with
  equal sums only if all the integers are equal. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pred_setTheory;

val putnam_1973_b1 =
  ``!n : num. !a : num -> int.
      let indices = IMAGE SUC (count (2 * n + 1))
      in
        (!S : num set.
           S SUBSET indices /\ CARD S = 2 * n
           ==>
           ?T : num set.
             T SUBSET S /\
             CARD T = n /\
             ITSET (\i acc. a i + acc) T 0 =
             ITSET (\i acc. a i + acc) (S DIFF T) 0)
        ==>
        !i j : num.
          i IN indices /\ j IN indices
          ==>
          a i = a j``;
