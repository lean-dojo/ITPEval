(*
  Statement-only formalization of PutnamBench artifact putnam_1979_a3:
  a nonzero real sequence satisfying the given recurrence has infinitely many
  integer-valued terms exactly when its first two terms are the same integer.
  This file contains no proof.
*)

let statement =
  `!x:num->real.
     (!n:num.
        ~(x n = &0) /\
        (3 <= n
         ==> x n =
             x (n - 2) * x (n - 1) /
             (&2 * x (n - 2) - x (n - 1))))
     ==>
     ((!m:num.
         ?n:num.
           n > m /\ ?a:int. x n = real_of_int a)
      <=>
      (?a:int.
         x 1 = real_of_int a /\
         x 2 = real_of_int a))`;;
