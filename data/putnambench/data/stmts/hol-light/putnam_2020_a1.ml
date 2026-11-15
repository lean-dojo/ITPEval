(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2020_a1
  (putnambench__hol-light__putnam_2020_a1): counting positive integers
  divisible by 2020, with at most 2020 decimal digits, whose digits are a
  nonempty block of ones followed by zeros. This file contains no proof.
*)

let statement =
  `{n:num |
      2020 divides n /\
      n < 10 EXP 2020 /\
      (?k l:num.
         l <= k /\
         n = nsum (0..(k - l)) (\i. 10 EXP (i + l)))}
   HAS_SIZE 508536`;;
