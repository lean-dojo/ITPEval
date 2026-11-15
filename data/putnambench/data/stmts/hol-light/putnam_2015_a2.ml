(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2015_a2:
  the integer sequence with the given second-order recurrence has 181 as an
  odd prime factor of its 2015th term. This file contains no proof.
*)

let statement =
  `!a:num->int.
     a 0 = &1 /\
     a 1 = &2 /\
     (!n:num.
        2 <= n
        ==> a n = &4 * a (n - 1) - a (n - 2))
     ==> ODD 181 /\
         prime 181 /\
         (&181:int) divides a 2015`;;
