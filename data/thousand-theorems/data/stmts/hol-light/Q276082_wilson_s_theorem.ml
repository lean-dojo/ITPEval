(*
  Statement-only formalization of Thousand Theorems corpus artifact Q276082,
  "Wilson's theorem": for every natural prime p, the factorial of p - 1 is
  congruent to -1 modulo p. This file contains no proof.
*)

let Q276082_WILSONS_THEOREM =
  `!p:num.
     prime p
     ==> (FACT (p - 1) == p - 1) (mod p)`;;
