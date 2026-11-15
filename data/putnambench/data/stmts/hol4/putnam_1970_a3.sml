(*
  Statement-only formalization of PutnamBench artifact putnam_1970_a3:
  the longest nonzero repeated decimal digit ending a perfect square has
  length 3, first attained by the square 1444. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory listTheory numposrepTheory;

val putnam_1970_a3 =
  ``!L : num -> num.
      (!n : num.
         L n <= LENGTH (n2l 10 n) /\
         (!k : num.
            k < L n
            ==>
            EL k (n2l 10 n) = EL 0 (n2l 10 n)) /\
         (L n <> LENGTH (n2l 10 n)
          ==>
          EL (L n) (n2l 10 n) <> EL 0 (n2l 10 n)))
      ==>
      (?n : num.
         EL 0 (n2l 10 (n ** 2)) <> 0 /\
         L (n ** 2) = 3) /\
      (!n : num.
         EL 0 (n2l 10 (n ** 2)) <> 0
         ==>
         L (n ** 2) <= 3) /\
      (?m : num. m ** 2 = 1444) /\
      L 1444 = 3 /\
      EL 0 (n2l 10 1444) <> 0 /\
      !n : num.
        EL 0 (n2l 10 (n ** 2)) <> 0 /\
        L (n ** 2) = 3
        ==>
        1444 <= n ** 2``;
