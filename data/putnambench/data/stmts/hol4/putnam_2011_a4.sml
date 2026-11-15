(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2011_a4:
  positive sizes admitting an integer square matrix whose row self-dot-products
  are even and whose distinct-row dot-products are odd are exactly the odd
  sizes. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pred_setTheory;

val putnam_2011_a4 =
  ``!n : num.
      0 < n
      ==>
      ((?A : num -> num -> int.
          (!r : num.
             r < n
             ==>
             ?k : int.
               ITSET
                 (\j : num. \acc : int. A r j * A r j + acc)
                 (count n)
                 0 =
               2 * k) /\
          (!r1 r2 : num.
             r1 < n /\ r2 < n /\ r1 <> r2
             ==>
             ?k : int.
               ITSET
                 (\j : num. \acc : int. A r1 j * A r2 j + acc)
                 (count n)
                 0 =
               2 * k + 1))
       <=> ODD n)``;
