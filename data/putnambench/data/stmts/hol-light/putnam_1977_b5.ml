(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1977_b5:
  a strict quadratic-sum bound for n real numbers implies that A is less
  than twice every pairwise product. This file contains no proof.
*)

let statement =
  `!n:num. !a:num->real. !A:real.
     n > 1 /\
     A + sum (1..n) (\i:num. (a i) pow 2) <
         (&1 / (&n - &1)) * (sum (1..n) a) pow 2
     ==> !i j:num.
           1 <= i /\ i < j /\ j <= n
           ==> A < &2 * a i * a j`;;
