(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1997_b5:
  congruence modulo n of consecutive-height base-2 tetration values for every
  natural number n at least 2. This file contains no proof.
*)

let statement =
  `!n:num. !tetration:num->num->num.
     2 <= n /\
     (!a:num. tetration a 0 = 1) /\
     (!a m:num.
        tetration a (m + 1) = a EXP (tetration a m))
     ==>
     (tetration 2 n) MOD n =
     (tetration 2 (n - 1)) MOD n`;;
