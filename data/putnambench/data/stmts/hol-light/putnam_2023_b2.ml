(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2023_b2
  (putnambench__hol-light__putnam_2023_b2): the minimum number of ones in the
  binary representation of a positive multiple of 2023 is 3. This file
  contains no proof.
*)

let statement =
  `let binary_ones =
     \m:num.
       CARD {j:num | ODD (m DIV (2 EXP j))} in
   (!n:num.
      0 < n
      ==> 3 <= binary_ones (2023 * n)) /\
   (?n:num.
      0 < n /\
      binary_ones (2023 * n) = 3)`;;
