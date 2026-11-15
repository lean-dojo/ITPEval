(*
  Statement-only formalization of PutnamBench artifact putnam_1979_a6:
  a reciprocal-distance bound for finitely many points in the real unit
  interval. This file contains no proof.
*)

let statement =
  `!n:num. !p:num->real.
     (!i:num. i IN 1..n ==> &0 <= p i /\ p i <= &1)
     ==>
     ?x:real.
       &0 <= x /\ x <= &1 /\
       (!i:num. i IN 1..n ==> ~(x = p i)) /\
       sum (1..n) (\i. &1 / abs (x - p i))
       <= &8 * &n *
          sum (1..n) (\i. &1 / (&2 * &i - &1))`;;
