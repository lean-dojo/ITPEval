(*
  Statement-only formalization of Logipedia corpus artifact nat.eq_plus,
  catalog title "nat.eq_plus": for every natural number n, Leibniz equality
  relates plus n to the natural-type filter applied to plus_body at n. This
  file contains no proof.
*)

new_constant
  ("logipedia_nat_filter_nat_type", `:(num -> 'a) -> num -> 'a`);;

new_constant
  ("logipedia_nat_plus", `:num -> num -> num`);;

new_constant
  ("logipedia_nat_plus_body", `:num -> num -> num`);;

let statement =
  `!n:num.
   !P:(num->num)->bool.
     P (logipedia_nat_plus n)
     ==>
     P (logipedia_nat_filter_nat_type logipedia_nat_plus_body n)`;;
