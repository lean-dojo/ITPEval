(*
  Statement-only formalization of Logipedia corpus artifact nat.eq_minus,
  catalog title "nat.eq_minus": for every natural number n, Leibniz equality
  relates minus n to the natural-type filter applied to minus_body at n. This
  file contains no proof.
*)

new_constant
  ("logipedia_nat_filter_nat_type", `:(num -> 'a) -> num -> 'a`);;

new_constant
  ("logipedia_nat_minus", `:num -> num -> num`);;

new_constant
  ("logipedia_nat_minus_body", `:num -> num -> num`);;

let statement =
  `!n:num.
   !P:(num->num)->bool.
     P (logipedia_nat_minus n)
     ==>
     P (logipedia_nat_filter_nat_type logipedia_nat_minus_body n)`;;
