(*
  Statement-only formalization of PutnamBench artifact putnam_1983_a3:
  injectivity modulo an odd prime of the polynomial whose coefficient of
  n^i is i + 1. This file contains no proof.
*)

let statement =
  `!p:num.
     ODD p /\ prime p
     ==>
     (let F =
        \n:num. nsum (0..p - 2) (\i. (i + 1) * n EXP i) in
      !a b:num.
        a < p /\ b < p /\ ~(a = b)
        ==> ~(F a MOD p = F b MOD p))`;;
