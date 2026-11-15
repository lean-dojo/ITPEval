(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2006_a5:
  the quotient of the sum and product of tangent values at n equally spaced
  angles, for odd n and an irrational theta/pi, is n or -n according to n
  modulo four. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_of_ratTheory
     real_sigmaTheory transcTheory;

val putnam_2006_a5 =
  ``!n : num. !theta : real. !a : num -> real.
      ODD n /\
      theta / pi NOTIN q_set /\
      (!k : num.
         k IN (count (SUC n) DIFF count 1)
         ==>
         a k = tan (theta + (&k * pi) / &n))
      ==>
      REAL_SUM_IMAGE a (count (SUC n) DIFF count 1) /
        REAL_PROD_IMAGE a (count (SUC n) DIFF count 1) =
      (if n MOD 4 = 1 then (&n : real) else ~(&n : real))``;
