(*
  Statement-only formalization of Logipedia corpus artifact nat.sym_eq_minus,
  catalog title "nat.sym_eq_minus": for every natural number n, Leibniz
  equality transports every predicate holding of the natural-type filter
  applied to minus_body at n to minus n. This file contains no proof.
*)

new_constant
  ("logipedia_nat_filter_nat_type", `:(num -> 'a) -> num -> 'a`);;

new_constant
  ("logipedia_nat_minus", `:num -> num -> num`);;

new_constant
  ("logipedia_nat_minus_body", `:num -> num -> num`);;

let statement =
  `!n:num.
   !P:((num -> num) -> bool).
     P (logipedia_nat_filter_nat_type logipedia_nat_minus_body n)
     ==>
     P (logipedia_nat_minus n)`;;
