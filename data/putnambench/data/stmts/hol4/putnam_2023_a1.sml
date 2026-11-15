(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2023_a1:
  the least positive index whose cosine-product function has second derivative
  at zero of absolute value greater than 2023 is 18. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory limTheory
     transcTheory;

val putnam_2023_a1 =
  ``let f =
      \n : num.
        \x : real.
          REAL_PROD_IMAGE
            (\i : num. cos (&i * x))
            (IMAGE SUC (count n))
    in
      0 < 18 /\
      2023 < abs (diffn 2 (f 18) 0) /\
      (!n : num.
         0 < n /\ 2023 < abs (diffn 2 (f n) 0)
         ==>
         18 <= n)``;
