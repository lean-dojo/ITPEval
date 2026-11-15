(*
  Statement-only formalization of PutnamBench problem putnam_1983_a1:
  exactly 2301 positive integers divide at least one of 10^40 and 20^30.
  This file contains no proof.
*)

let statement =
  `{n:num |
      0 < n /\
      (n divides (10 EXP 40) \/ n divides (20 EXP 30))}
   HAS_SIZE 2301`;;
