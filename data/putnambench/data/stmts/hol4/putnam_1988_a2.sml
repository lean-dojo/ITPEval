(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1988_a2:
  existence on a nonempty open real interval of a nonzero differentiable
  function satisfying the erroneous product-derivative identity for
  f(x) = exp(x^2). This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory limTheory transcTheory;

val putnam_1988_a2 =
  ``let f = \x : real. exp (x pow 2)
    in
      ((?a b : real.
          a < b /\
          ?g : real -> real.
            (?x : real. a < x /\ x < b /\ g x <> 0) /\
            (!x : real.
               a < x /\ x < b
               ==>
               g differentiable x) /\
            (!x : real.
               a < x /\ x < b
               ==>
               diffn 1 (\y : real. f y * g y) x =
                 diffn 1 f x * diffn 1 g x))
       <=> T)``;
