(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2022_b6:
  continuous positive-real-valued functions on the positive reals satisfying
  the given functional equation are exactly f(x) = 1 / (1 + c*x) for
  nonnegative real c. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory real_topologyTheory;

val putnam_2022_b6 =
  ``!f : real -> real.
      (f continuous_on {x : real | 0 < x} /\
       (!x : real. 0 < x ==> 0 < f x) /\
       (!x y : real.
          0 < x /\ 0 < y
          ==>
          f (x * f y) + f (y * f x) = 1 + f (x + y)))
      <=>
      ?c : real.
        0 <= c /\
        !x : real.
          0 < x ==> f x = 1 / (1 + c * x)``;
