(*
  Statement-only formalization of Logipedia corpus artifact
  nat.axiom_match_nat_type_O, catalog title
  "nat.axiom_match_nat_type_O": for every result type, zero case, and
  successor case, the source equality relation identifies the natural-number
  eliminator at zero with its zero case. This file contains no proof.
*)

new_constant
  ("logipedia_connectives_equal", `:'a -> 'a -> bool`);;

new_constant
  ("logipedia_nat_match_nat_type", `:'a -> (num -> 'a) -> num -> 'a`);;

let statement =
  `!case_O:'a.
   !case_S:num->'a.
     logipedia_connectives_equal
       (logipedia_nat_match_nat_type case_O case_S 0)
       case_O`;;
