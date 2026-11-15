(*
  Statement-only formalization of PutnamBench artifact putnam_1980_b3:
  characterization of the real initial values for which the recursively
  defined sequence remains positive. This file contains no proof.
*)

let statement =
  `let putnam_1980_b3_solution = {x:real | &3 <= x} in
   !a:real. !u:num->real.
     u 0 = a /\
     (!n:num. u (n + 1) = &2 * u n - (&n) pow 2)
     ==>
     ((!n:num. u n > &0) <=>
      a IN putnam_1980_b3_solution)`;;
