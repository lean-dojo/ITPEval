(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1985_a5:
  classification of the integers from 1 through 10 for which the integral
  from 0 to 2 pi of the product cos(x) cos(2x) ... cos(mx) is nonzero. This
  file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory transcTheory
     integrationTheory;

val putnam_1985_a5 =
  ``let I =
      \m : num.
        integration$integral (interval [0, 2 * pi])
          (\x : real.
             real_sigma$product
               (count m)
               (\i : num. cos (&(i + 1) * x)))
    in
      !m : num.
        1 <= m /\ m <= 10
        ==>
        (I m <> 0 <=>
         m = 3 \/ m = 4 \/ m = 7 \/ m = 8)``;
