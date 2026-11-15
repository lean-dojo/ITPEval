(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1990_b1:
  classification of the continuously differentiable real functions satisfying
  the stated integral identity as two signed exponential functions. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory real_topologyTheory limTheory transcTheory;
open integrationTheory;

val putnam_1990_b1 =
  ``let oriented_integral =
      \g : real -> real.
      \a b : real.
        if a <= b then
          integration$integral (interval [a, b]) g
        else
          ~(integration$integral (interval [b, a]) g)
    in
      !f : real -> real.
        ((!x : real. higher_differentiable 1 f x) /\
         (\x : real. diffn 1 f x) continuous_on UNIV /\
         (!x : real.
            f x pow 2 =
              oriented_integral
                (\t : real. f t pow 2 + diffn 1 f t pow 2)
                0 x +
              (1990 : real)))
        <=>
        (f = (\x : real. sqrt 1990 * exp x) \/
         f = (\x : real. ~(sqrt 1990 * exp x)))``;
