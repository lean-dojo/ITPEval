(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1993_a2:
  a recurrence with a constant real coefficient for every nonzero real
  sequence satisfying a quadratic determinant identity. This file contains no proof.
*)

let statement =
  `!x:num->real.
     ((!n:num. ~(x n = &0)) /\
      (!n:num.
         1 <= n
         ==> x n pow 2 - x (n - 1) * x (n + 1) = &1))
     ==>
     ?a:real.
       !n:num.
         1 <= n
         ==> x (n + 1) = a * x n - x (n - 1)`;;
