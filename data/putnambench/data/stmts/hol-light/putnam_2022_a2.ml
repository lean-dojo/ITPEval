(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2022_a2:
  the largest possible number of negative coefficients in the square of a
  degree-n real polynomial is 2*n - 2 for n at least 2. This file contains
  no proof.
*)

let statement =
  `let degree_is =
     \n:num. \p:num->real.
       ~(p n = &0) /\ (!k:num. n < k ==> p k = &0) in
   let square_coeff =
     \p:num->real. \k:num.
       sum (0..k) (\i:num. p i * p (k - i)) in
   let negative_coefficients =
     \p:num->real. \m:num.
       CARD {k:num | k <= m /\ square_coeff p k < &0} in
   !n:num.
     2 <= n
     ==>
     ((!p:num->real.
         degree_is n p
         ==> negative_coefficients p (2 * n) <= 2 * n - 2) /\
      (?p:num->real.
         degree_is n p /\
         negative_coefficients p (2 * n) = 2 * n - 2))`;;
