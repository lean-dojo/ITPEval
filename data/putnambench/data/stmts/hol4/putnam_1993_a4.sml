(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1993_a4:
  two bounded families of positive integers have equal subset sums, with the
  subset chosen from the first family nonempty. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val putnam_1993_a4 =
  ``!x : num -> num. !y : num -> num.
      (!i : num. i < 19 ==> 0 < x i /\ x i <= 93) /\
      (!j : num. j < 93 ==> 0 < y j /\ y j <= 19)
      ==>
      ?is js : num set.
        is SUBSET count 19 /\
        js SUBSET count 93 /\
        is <> {} /\
        SIGMA x is = SIGMA y js``;
