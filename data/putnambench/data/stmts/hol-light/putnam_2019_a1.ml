(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2019_a1
  (putnambench__hol-light__putnam_2019_a1): the nonnegative integer values of
  A^3 + B^3 + C^3 - 3ABC, characterized by their residues modulo 9. This file
  contains no proof.
*)

let statement =
  `{n:int |
      ?A B C:int.
        &0 <= A /\
        &0 <= B /\
        &0 <= C /\
        A pow 3 + B pow 3 + C pow 3 - &3 * A * B * C = n} =
   {n:int |
      &0 <= n /\
      ~(n rem &9 = &3) /\
      ~(n rem &9 = &6)}`;;
