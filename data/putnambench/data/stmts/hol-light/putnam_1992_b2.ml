(*
  Statement-only formalization of PutnamBench artifact putnam_1992_b2:
  the coefficient formula for powers of the polynomial 1 + x + x^2 + x^3
  as a finite binomial convolution. This file contains no proof.
*)

let statement =
  `let choose =
     \n r:num.
       if r <= n then FACT n DIV (FACT r * FACT (n - r)) else 0 in
   let pmul =
     \p q:num->num. \k:num.
       nsum (0..k) (\i:num. p i * q (k - i)) in
   let ppow =
     \p:num->num. \n:num.
       ITER n (pmul p) (\k:num. if k = 0 then 1 else 0) in
   let base =
     \k:num. if k <= 3 then 1 else 0 in
   let Q =
     \n k:num. ppow base n k in
   !n k:num.
     Q n k =
     nsum (0..k)
       (\j. choose n j *
            (if 2 * j <= k then choose n (k - 2 * j) else 0))`;;
