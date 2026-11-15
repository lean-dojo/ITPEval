(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1997_b2:
  every twice-differentiable real function satisfying
  f(x) + f''(x) = -x g(x) f'(x) for a nonnegative real function g has
  globally bounded absolute value. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory limTheory;

val putnam_1997_b2 =
  ``!f g : real -> real.
      (!x : real. 0 <= g x) /\
      (!x : real. higher_differentiable 2 f x) /\
      (!x : real.
         f x + diffn 2 f x =
           ~x * g x * diffn 1 f x)
      ==>
      ?B : real.
        !x : real. abs (f x) <= B``;
