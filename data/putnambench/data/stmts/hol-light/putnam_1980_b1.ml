(*
  Statement-only formalization of PutnamBench artifact putnam_1980_b1:
  characterization of the real constants for which the symmetric exponential
  average is bounded by exp(c * x^2) for every real x. This file contains no
  proof.
*)

let statement =
  `let putnam_1980_b1_solution = {c:real | &1 / &2 <= c} in
   !c:real.
     ((!x:real.
         (exp x + exp (--x)) / &2 <= exp (c * x pow 2)) <=>
      c IN putnam_1980_b1_solution)`;;
