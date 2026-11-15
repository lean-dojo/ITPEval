(*
  Statement-only formalization of Logipedia corpus artifact
  nat.sym_eq_match_nat_type_O, catalog title "nat.sym_eq_match_nat_type_O":
  for every result type, zero case, and successor case, Leibniz equality
  transports every predicate from the zero case to the natural-number
  eliminator at zero. This file contains no proof.
*)

new_constant
  ("logipedia_nat_match_nat_type", `:'a -> (num -> 'a) -> num -> 'a`);;

let statement =
  `!case_O:'a.
   !case_S:num->'a.
   !P:'a->bool.
     P case_O
     ==> P (logipedia_nat_match_nat_type case_O case_S 0)`;;
