(*
  Statement-only formalization of Logipedia corpus artifact nat.axiom_eqb,
  catalog title "nat.axiom_eqb": for every natural number n, the source
  equality relation identifies eqb n with the natural-type filter applied to
  eqb_body at n. This file contains no proof.
*)

new_constant
  ("logipedia_connectives_equal", `:'a -> 'a -> bool`);;

new_constant
  ("logipedia_nat_filter_nat_type", `:(num -> 'a) -> num -> 'a`);;

new_constant
  ("logipedia_nat_eqb", `:num -> num -> bool`);;

new_constant
  ("logipedia_nat_eqb_body", `:num -> num -> bool`);;

let statement =
  `!n:num.
     logipedia_connectives_equal
       (logipedia_nat_eqb n)
       (logipedia_nat_filter_nat_type logipedia_nat_eqb_body n)`;;
