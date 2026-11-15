(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2003_b1:
  nonexistence of four real polynomials whose two separated products sum
  identically to 1 + xy + x^2 y^2. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory polyTheory;

val putnam_2003_b1 =
  ``let putnam_2003_b1_solution = F
    in
      ((?a b c d : real list.
          !x y : real.
            1 + x * y + (x pow 2) * (y pow 2) =
              poly a x * poly c y + poly b x * poly d y)
       <=>
       putnam_2003_b1_solution)``;
