(*
  Statement-only formalization of PutnamBench artifact putnam_1972_a5:
  no natural number n greater than 1 divides the integer 2^n - 1.
  This file contains no proof.
*)

let statement =
  `!n:num.
     n > 1
     ==> ~((&n:int) divides ((&2:int) pow n - &1))`;;
