(*
  Statement-only formalization of PutnamBench artifact putnam_1980_b6:
  a recursively defined rational sum has reduced denominator not divisible
  by the prime endpoint. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory pred_setTheory ratTheory;

val putnam_1980_b6 =
  ``!G : num # num -> rat.
      (!d n : num.
         d <= n
         ==>
         (d = 1 ==> G (d, n) = 1q / rat_of_num n) /\
         (1 < d ==>
          G (d, n) =
            (rat_of_num d / rat_of_num n) *
            ITSET
              (\i : num. \acc : rat. rat_add (G (d - 1, i - 1)) acc)
              {i : num | d <= i /\ i <= n}
              0q))
      ==>
      !d p : num.
        1 < d /\ d <= p /\ prime p
        ==>
        ~divides p (RATD (G (d, p)))``;
