(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1991_b2:
  nonconstant differentiable real functions satisfying the complex addition
  laws have unit squared norm everywhere when the derivative of the first
  function vanishes at zero. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory limTheory;

val putnam_1991_b2 =
  ``!f g : real -> real.
      ~(?c : real.
          f = (\x : real. c) \/
          g = (\x : real. c)) /\
      (!x : real.
         f differentiable x /\
         g differentiable x) /\
      (!x y : real.
         f (x + y) = f x * f y - g x * g y) /\
      (!x y : real.
         g (x + y) = f x * g y + g x * f y)
      ==>
      (diffn 1 f 0 = 0
       ==>
       !x : real. f x pow 2 + g x pow 2 = 1)``;
