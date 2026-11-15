(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2019_b6:
  independent perfect dominating sets in the integer lattice exist in every
  positive dimension. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pred_setTheory;

val putnam_2019_b6 =
  ``let lattice_point =
      \n : num. \p : num -> int.
        !i : num. n <= i ==> p i = 0
    in
    let neighbors =
      \n : num. \p q : num -> int.
        lattice_point n p /\
        lattice_point n q /\
        ?i : num.
          i < n /\
          ABS (p i - q i) = 1 /\
          !j : num.
            j < n /\ j <> i
            ==>
            p j = q j
    in
    let solution = {n : num | 1 <= n}
    in
      !n : num.
        ((1 <= n /\
          ?S : (num -> int) set.
            (!p : num -> int.
               p IN S
               ==>
               lattice_point n p) /\
            (!p : num -> int.
               p IN S
               ==>
               !q : num -> int.
                 neighbors n p q
                 ==>
                 q NOTIN S) /\
            (!p : num -> int.
               lattice_point n p /\ p NOTIN S
               ==>
               {q : num -> int |
                  q IN S /\ neighbors n p q}
                 HAS_SIZE 1))
         <=>
         n IN solution)``;
