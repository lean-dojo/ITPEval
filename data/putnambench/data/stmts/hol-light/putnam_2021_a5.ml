(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2021_a5
  (putnambench__hol-light__putnam_2021_a5): the nonnegative exponents for
  which the sum of the corresponding powers of the residues coprime to 2021
  is divisible by 2021. This file contains no proof.
*)

let statement =
  `let A =
     {n:num | 1 <= n /\ n <= 2021 /\ gcd(n,2021) = 1} in
   let S =
     \j:num. nsum A (\n:num. n EXP j) in
   !j:num.
     (2021 divides S j <=>
      ~(42 divides j) /\ ~(46 divides j))`;;
