(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2025_b3
  (putnambench__hol-light__putnam_2025_b3): a nonempty set of positive
  integers closed under the positive divisors of 2025^n - 15^n contains every
  positive integer. This file contains no proof.
*)

let statement =
  `!S:num->bool.
     (?m:num. m IN S) /\
     (!n:num. n IN S ==> 0 < n) /\
     (!n d:num.
        n IN S /\
        0 < d /\
        d divides (2025 EXP n - 15 EXP n)
        ==> d IN S)
     ==>
     S = {n:num | 0 < n}`;;
