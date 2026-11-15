(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2018_b3
  (putnambench__hol-light__putnam_2018_b3): classification of the positive
  integers below 10^100 satisfying three divisibility conditions involving
  2^n. This file contains no proof.
*)

let statement =
  `{n:num |
      0 < n /\
      n < 10 EXP 100 /\
      (&n:int) divides ((&2:int) pow n) /\
      ((&n:int) - &1) divides (((&2:int) pow n) - &1) /\
      ((&n:int) - &2) divides (((&2:int) pow n) - &2)} =
   {n:num |
      n = 2 EXP 2 \/
      n = 2 EXP 4 \/
      n = 2 EXP 16 \/
      n = 2 EXP 256}`;;
