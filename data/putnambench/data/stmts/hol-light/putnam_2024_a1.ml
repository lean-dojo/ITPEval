(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2024_a1
  (putnambench__hol-light__putnam_2024_a1): classification of the positive
  integer exponents admitting positive integers a, b, and c such that
  2*a^n + 3*b^n = 4*c^n. This file contains no proof.
*)

let statement =
  `!n:num.
     (0 < n /\
      ?a b c:num.
        0 < a /\
        0 < b /\
        0 < c /\
        2 * a EXP n + 3 * b EXP n = 4 * c EXP n)
     <=>
     n = 1`;;
