(*
  Statement-only formalization of Logipedia corpus artifact
  nat.axiom_match_nat_type_S, catalog title
  "nat.axiom_match_nat_type_S": for every result type, zero case, successor
  case, and natural number n, the source equality relation identifies the
  natural-number eliminator at the successor of n with the successor case
  applied to n. This file contains no proof.
*)

new_constant
  ("logipedia_connectives_equal", `:'a -> 'a -> bool`);;

new_constant
  ("logipedia_nat_match_nat_type", `:'a -> (num -> 'a) -> num -> 'a`);;

let statement =
  `!case_O:'a.
   !case_S:num->'a.
   !n:num.
     logipedia_connectives_equal
       (logipedia_nat_match_nat_type case_O case_S (SUC n))
       (case_S n)`;;
