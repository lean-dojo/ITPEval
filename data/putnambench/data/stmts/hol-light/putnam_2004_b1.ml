(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2004_b1:
  partial sums formed from the leading coefficients of an integer polynomial
  at a rational root are integers. This file contains no proof.
*)

let statement =
  `let is_rational =
     \x:real.
       ?p q:int.
         ~(q = (&0:int)) /\
         x = real_of_int p / real_of_int q in
   !c:int list n:num r:real.
     LENGTH c = n + 1 /\
     ~(LAST c = (&0:int)) /\
     is_rational r /\
     sum (0..n)
       (\k:num. real_of_int (EL k c) * r pow k) = &0
     ==>
     !i:num.
       i < n
       ==> ?m:int.
             sum (0..i)
               (\j:num.
                  real_of_int (EL (n - j) c) *
                  r pow (i + 1 - j)) =
             real_of_int m`;;
