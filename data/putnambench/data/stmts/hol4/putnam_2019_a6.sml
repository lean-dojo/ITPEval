(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2019_a6:
  a continuous real function that is twice differentiable on the open unit
  interval and vanishes faster than x^r at zero has either derivative tending
  to zero or unbounded scaled second derivative near zero. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory real_topologyTheory limTheory transcTheory;

val putnam_2019_a6 =
  ``let right_limit =
      \f : real -> real.
      \l : real.
        !epsilon : real.
          0 < epsilon
          ==>
          ?delta : real.
            0 < delta /\
            !x : real.
              0 < x /\ x < delta
              ==>
              abs (f x - l) < epsilon
    in
      !g : real -> real. !r : real.
        g continuous_on interval [0, 1] /\
        (!x : real.
           0 < x /\ x < 1
           ==>
           higher_differentiable 2 g x) /\
        1 < r /\
        right_limit (\x : real. g x / (x powr r)) 0
        ==>
        right_limit (diffn 1 g) 0 \/
        (!M : real.
           ?delta : real.
             0 < delta /\
             !x : real.
               0 < x /\ x < delta
               ==>
               ?x' : real.
                 0 < x' /\ x' <= x /\
                 M < x' powr r * abs (diffn 2 g x'))``;
