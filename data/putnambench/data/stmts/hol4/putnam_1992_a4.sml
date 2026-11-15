(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1992_a4:
  the values at zero of every positive-order derivative of a smooth real
  function prescribed on the reciprocal positive integers. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory limTheory;

val putnam_1992_a4 =
  ``let solution =
      \k : num.
        if EVEN k
        then (-1 : real) pow (k DIV 2) * &(FACT k)
        else 0
    in
      !f : real -> real.
        (!k : num. !x : real. higher_differentiable k f x) /\
        (!n : num.
           0 < n
           ==>
           f (1 / &n) = (&n pow 2) / (&n pow 2 + 1))
        ==>
        !k : num.
          0 < k
          ==>
          diffn k f 0 = solution k``;
