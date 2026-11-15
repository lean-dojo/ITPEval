(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1993_b6:
  three positive natural numbers can be transformed to include zero by
  finitely many applications of the stated doubling-and-subtraction rule.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val putnam_1993_b6 =
  ``!S : num -> num.
    !f : num -> num -> (num -> num) -> (num -> num).
      (!i : num. i < 3 ==> 0 < S i) /\
      (!i j k : num.
         i < 3 /\ j < 3 /\ k < 3 /\
         i <> j /\ i <> k /\ j <> k
         ==>
         !S' : num -> num.
           if S' i <= S' j then
             f i j S' i = 2 * S' i /\
             f i j S' j = S' j - S' i /\
             f i j S' k = S' k
           else
             f i j S' = S')
      ==>
      ?Ss : num -> num -> num.
        ?N : num.
          Ss 0 = S /\
          (?i : num. i < 3 /\ Ss N i = 0) /\
          (!n : num.
             n < N
             ==>
             ?i j : num.
               i < 3 /\ j < 3 /\ i <> j /\
               f i j (Ss n) = Ss (n + 1))``;
