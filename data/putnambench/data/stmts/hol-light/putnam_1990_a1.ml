(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1990_a1:
  the integer sequence determined by the given third-order recurrence equals
  n! plus 2^n. This file contains no proof.
*)

let statement =
  `!a:num->int.
     a 0 = &2 /\
     a 1 = &3 /\
     a 2 = &6 /\
     (!n:num.
        3 <= n
        ==> a n =
            (&n + &4) * a (n - 1) -
            &4 * &n * a (n - 2) +
            (&4 * &n - &8) * a (n - 3))
     ==> a = (\n:num. &(FACT n) + &(2 EXP n))`;;
