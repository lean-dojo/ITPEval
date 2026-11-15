(*
  Statement-only formalization of Logipedia corpus artifact
  nat.eq_match_nat_type_O, catalog title "nat.eq_match_nat_type_O": for every
  result type, zero case, and successor case, Leibniz equality transports
  every predicate from the natural-number eliminator at zero to its zero
  case. This file contains no proof.
*)

new_constant
  ("logipedia_nat_match_nat_type", `:'a -> (num -> 'a) -> num -> 'a`);;

let statement =
  `!case_O:'a.
   !case_S:num->'a.
   !P:'a->bool.
     P (logipedia_nat_match_nat_type case_O case_S 0)
     ==> P case_O`;;
