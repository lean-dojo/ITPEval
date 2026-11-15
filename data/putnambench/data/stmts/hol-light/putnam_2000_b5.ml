(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2000_b5:
  finite positive-integer sets evolving by exclusive membership of adjacent
  integers recur as the union of the initial set and one of its translates.
  This file contains no proof.
*)

let statement =
  `!S:num->int->bool.
     (!n:num. FINITE (S n)) /\
     (!n:num. !s:int. s IN S n ==> &0 < s) /\
     (!n:num. !a:int.
        a IN S (n + 1) <=>
        ((a - &1 IN S n /\ ~(a IN S n)) \/
         (a IN S n /\ ~(a - &1 IN S n))))
     ==> !n:num.
           ?N:num.
             n <= N /\
             S N = S 0 UNION {M:int | M - &N IN S 0}`;;
