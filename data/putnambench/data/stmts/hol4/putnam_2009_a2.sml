(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2009_a2:
  the explicit local solution for one component of a differentiable
  three-function nonlinear ODE system with prescribed initial values. This
  file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory real_topologyTheory transcTheory derivativeTheory;

val putnam_2009_a2 =
  ``let solution =
      \x : real.
        (2 : real) powr (-1 / 12) *
        (sin (6 * x + pi / 4) /
           (cos (6 * x + pi / 4) pow 2)) powr (1 / 6)
    in
      !f g h : real -> real. !a b : real.
        a < 0 /\ 0 < b /\
        (!x : real.
           a < x /\ x < b
           ==>
           f differentiable (at x) /\
           g differentiable (at x) /\
           h differentiable (at x)) /\
        (!x : real.
           a < x /\ x < b
           ==>
           vector_derivative f (at x) =
             2 * f x pow 2 * g x * h x + 1 / (g x * h x)) /\
        f 0 = 1 /\
        (!x : real.
           a < x /\ x < b
           ==>
           vector_derivative g (at x) =
             f x * g x pow 2 * h x + 4 / (f x * h x)) /\
        g 0 = 1 /\
        (!x : real.
           a < x /\ x < b
           ==>
           vector_derivative h (at x) =
             3 * f x * g x * h x pow 2 + 1 / (f x * g x)) /\
        h 0 = 1
        ==>
        ?c d : real.
          c < 0 /\ 0 < d /\
          !x : real.
            c < x /\ x < d ==> f x = solution x``;
