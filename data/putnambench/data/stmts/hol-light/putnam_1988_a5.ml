(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1988_a5:
  existence and uniqueness on the positive reals of a positive-valued
  function satisfying f(f(x)) = 6*x - f(x). This file contains no proof.
*)

let statement =
  `?f:real->real.
     (!x:real.
        &0 < x
        ==> f (f x) = &6 * x - f x /\ &0 < f x) /\
     (!g:real->real.
        (!x:real.
           &0 < x
           ==> g (g x) = &6 * x - g x /\ &0 < g x)
        ==> !x:real. &0 < x ==> f x = g x)`;;
