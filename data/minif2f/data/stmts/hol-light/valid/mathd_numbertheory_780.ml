(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_780:
  a two-digit modulus for which 6x is congruent to 1 and x is congruent to 36
  must equal 43. This file contains no proof.
*)

let statement =
  `!m x:int.
     &0 <= x /\
     &10 <= m /\ m <= &99 /\
     (&6 * x == &1) (mod m) /\
     (x - &36 == &0) (mod m)
     ==> m = &43`;;
