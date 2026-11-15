(*
  Statement-only formalization of Logipedia corpus artifact
  nat.eq_match_nat_type_S, catalog title "nat.eq_match_nat_type_S": for every
  result type, zero case, successor case, and natural number n, Leibniz
  equality transports every predicate from the natural-number eliminator at
  the successor of n to the successor case applied to n. This file contains
  no proof.
*)

new_constant
  ("logipedia_nat_match_nat_type", `:'a -> (num -> 'a) -> num -> 'a`);;

let statement =
  `!case_O:'a.
   !case_S:num->'a.
   !n:num.
   !P:'a->bool.
     P (logipedia_nat_match_nat_type case_O case_S (SUC n))
     ==> P (case_S n)`;;
