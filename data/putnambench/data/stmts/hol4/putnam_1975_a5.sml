(*
  Statement-only formalization of PutnamBench artifact putnam_1975_a5:
  for two positive linearly independent solutions on a closed real interval
  of a second-order linear differential equation, a positive
  square-root-product scaling satisfies the associated nonlinear equation.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory real_topologyTheory limTheory transcTheory;

val putnam_1975_a5 =
  ``!a b : real. !f y1 y2 : real -> real.
      f continuous_on UNIV /\
      (!x : real. higher_differentiable 2 y1 x) /\
      (diffn 2 y1) continuous_on UNIV /\
      (!x : real. higher_differentiable 2 y2 x) /\
      (diffn 2 y2) continuous_on UNIV /\
      (!x : real. diffn 2 y1 x = f x * y1 x) /\
      (!x : real. diffn 2 y2 x = f x * y2 x) /\
      (!c1 c2 : real.
         (!x : real. c1 * y1 x + c2 * y2 x = 0)
         ==>
         c1 = 0 /\ c2 = 0) /\
      (!x : real.
         x IN interval [a, b] ==> 0 < y1 x /\ 0 < y2 x)
      ==>
      ?c : real.
        0 < c /\
        (let z = \x : real. c * sqrt (y1 x * y2 x)
         in
           !x : real.
             x IN interval [a, b]
             ==>
             diffn 2 z x + 1 / (z x pow 3) = f x * z x)``;
