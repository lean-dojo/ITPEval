(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1994_a1:
  divergence to positive infinity of the partial sums of a positive real
  sequence satisfying a binary branching inequality. This file contains no
  proof.
*)

let statement =
  `!a:num->real.
     (!n:num.
        1 <= n
        ==> &0 < a n /\
            a n <= a (2 * n) + a (2 * n + 1))
     ==>
     !B:real.
       ?N:num.
         !n:num.
           N <= n
           ==> B <= sum (1..n) a`;;
