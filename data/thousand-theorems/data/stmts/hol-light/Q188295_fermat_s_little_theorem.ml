(*
  Statement-only formalization of Thousand Theorems corpus artifact Q188295,
  "Fermat's little theorem": for a prime p, every nonzero residue modulo p
  raised to the power p - 1 is congruent to one modulo p. This file contains
  no proof.
*)

let Q188295_FERMATS_LITTLE_THEOREM =
  `!p a:num.
     prime p /\
     ~((a == 0) (mod p))
     ==> (a EXP (p - 1) == 1) (mod p)`;;
