(*
  Statement-only formalization of PutnamBench artifact putnam_1966_a3:
  convergence to 1 of n * x_n for a real sequence starting between 0 and 1
  and satisfying x_(n+1) = x_n * (1 - x_n). This file contains no proof.
*)

let statement =
  `!x:num->real.
     &0 < x 1 /\ x 1 < &1 /\
     (!n:num. 1 <= n ==> x (n + 1) = x n * (&1 - x n))
     ==> !e:real.
           &0 < e
           ==> ?N:num. !n:num. N <= n ==> abs (&n * x n - &1) < e`;;
