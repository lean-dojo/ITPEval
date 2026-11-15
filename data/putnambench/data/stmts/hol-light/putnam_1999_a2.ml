(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1999_a2:
  every real polynomial that is nonnegative on the real line is a finite sum
  of squares of real polynomials. This file contains no proof.
*)

let statement =
  `!p:real->real.
     polynomial_function p /\
     (!x:real. &0 <= p x)
     ==> ?k:num. ?f:num->real->real.
           0 < k /\
           (!i:num. i < k ==> polynomial_function (f i)) /\
           (!x:real.
              p x = sum (0..k - 1) (\i:num. (f i x) pow 2))`;;
