(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1984_b1:
  the degree-one polynomial recurrence satisfied by the partial sums of
  positive factorials. This file contains no proof.
*)

let statement =
  `let putnam_1984_b1_solution =
     ((\x:num. (&x:int) + &3),
      (\x:num. --(&x:int) - &2)) in
   !f:num->int.
     (!n:num.
        0 < n
        ==> f n = isum (1..n) (\i. &(FACT i)))
     ==>
     !n:num.
       1 <= n
       ==> f (n + 2) =
           FST putnam_1984_b1_solution n * f (n + 1) +
           SND putnam_1984_b1_solution n * f n`;;
