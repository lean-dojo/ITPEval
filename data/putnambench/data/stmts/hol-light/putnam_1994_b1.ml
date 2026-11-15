(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1994_b1:
  classification of the positive integers that lie within 250 of exactly
  fifteen perfect squares. This file contains no proof.
*)

let statement =
  `let putnam_1994_b1_solution =
     {n:int |
        ((&315:int) <= n /\ n <= &325) \/
        ((&332:int) <= n /\ n <= &350)} in
   !n:int.
     n IN putnam_1994_b1_solution <=>
     (&0:int) < n /\
     CARD {m:num | abs (n - &(m EXP 2)) <= (&250:int)} = 15`;;
