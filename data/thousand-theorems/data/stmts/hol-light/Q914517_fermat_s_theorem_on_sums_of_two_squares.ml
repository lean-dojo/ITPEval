(*
  Statement-only formalization of Thousand Theorems corpus artifact Q914517,
  "Fermat's theorem on sums of two squares": every natural prime not
  congruent to 3 modulo 4 is a sum of two squares of natural numbers.
  This file contains no proof.
*)

let Q914517_FERMATS_THEOREM_ON_SUMS_OF_TWO_SQUARES =
  `!p:num.
     prime p /\ ~(p MOD 4 = 3)
     ==> ?a b:num. a EXP 2 + b EXP 2 = p`;;
