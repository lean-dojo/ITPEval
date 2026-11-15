(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1989_b3:
  the moments of a rapidly decaying differentiable function satisfying the
  stated dilation differential equation have an explicit product formula,
  and their factorial scaling has the specified convergence behavior.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_topologyTheory limTheory
     transcTheory derivativeTheory real_sigmaTheory;
open extrealTheory measureTheory lebesgueTheory lebesgue_measureTheory;

val putnam_1989_b3 =
  ``!f : real -> real.
      let nonnegative_reals = {x : real | 0 <= x}
      in
      let positive_reals = {x : real | 0 < x}
      in
      let moment =
        \n : num.
          let halfline = restrict_space lebesgue positive_reals
          in
          let integrand =
            \x : real. Normal (x pow n * f x)
          in
            if lebesgue$integrable halfline integrand then
              real (lebesgue$integral halfline integrand)
            else
              0
      in
      let solution =
        \n : num. \c : real.
          c * &(FACT n) /
          ((3 : real) pow n *
           REAL_PROD_IMAGE
             (\m : num. 1 - inv ((2 : real) pow m))
             (IMAGE SUC (count n)))
      in
      let scaled =
        \n : num. moment n * (3 : real) pow n / &(FACT n)
      in
        f differentiable_on nonnegative_reals /\
        (!x : real.
           0 < x
           ==>
           (f diffl (-3 * f x + 6 * f (2 * x))) x) /\
        (!x : real.
           0 <= x
           ==>
           abs (f x) <= exp (-sqrt x))
        ==>
        (!n : num. moment n = solution n (moment 0)) /\
        (?L : real. (scaled --> L) sequentially) /\
        ((scaled --> 0) sequentially ==> moment 0 = 0)``;
