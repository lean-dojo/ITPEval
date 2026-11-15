(*
  Statement-only formalization of Logipedia corpus artifact nat.axiom_leb,
  catalog title "nat.axiom_leb": for every natural number n, the source
  equality relation identifies leb n with the natural-type filter applied to
  leb_body at n. This file contains no proof.
*)

new_constant
  ("logipedia_connectives_equal", `:'a -> 'a -> bool`);;

new_constant
  ("logipedia_nat_filter_nat_type", `:(num -> 'a) -> num -> 'a`);;

new_constant
  ("logipedia_nat_leb", `:num -> num -> bool`);;

new_constant
  ("logipedia_nat_leb_body", `:num -> num -> bool`);;

let statement =
  `!n:num.
     logipedia_connectives_equal
       (logipedia_nat_leb n)
       (logipedia_nat_filter_nat_type logipedia_nat_leb_body n)`;;
