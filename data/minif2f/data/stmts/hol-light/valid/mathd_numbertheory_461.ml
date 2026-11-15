(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_461:
  if n counts the natural numbers from 1 through 7 that are coprime to 8, then
  3 raised to n is congruent to 1 modulo 8. This file contains no proof.
*)

let statement =
  `!n:num.
     n = CARD {k:num | 1 <= k /\ k < 8 /\ gcd(k,8) = 1}
     ==> (3 EXP n) MOD 8 = 1`;;
