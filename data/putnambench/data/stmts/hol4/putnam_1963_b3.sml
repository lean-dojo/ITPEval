(*
  Statement-only formalization of PutnamBench artifact putnam_1963_b3:
  the classification of twice-differentiable real functions satisfying a
  quadratic addition-subtraction functional equation as scalar multiples of
  hyperbolic sine, the identity function, or sine. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory limTheory transcTheory;

val putnam_1963_b3 =
  ``!f : real -> real.
      (!x : real. higher_differentiable 2 f x)
      ==>
      ((!x y : real.
          (f x) pow 2 - (f y) pow 2 =
            f (x + y) * f (x - y))
       <=>
       ?A k : real.
         f = (\x : real. A * sinh (k * x)) \/
         f = (\x : real. A * x) \/
         f = (\x : real. A * sin (k * x)))``;
