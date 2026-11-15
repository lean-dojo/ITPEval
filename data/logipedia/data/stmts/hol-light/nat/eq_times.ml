(*
  Statement-only formalization of Logipedia corpus artifact nat.eq_times,
  catalog title "nat.eq_times": for every natural number n, Leibniz equality
  relates times n to the natural-type filter applied to times_body at n. This
  file contains no proof.
*)

new_constant
  ("logipedia_nat_filter_nat_type", `:(num -> 'a) -> num -> 'a`);;

new_constant
  ("logipedia_nat_times", `:num -> num -> num`);;

new_constant
  ("logipedia_nat_times_body", `:num -> num -> num`);;

let statement =
  `!n:num.
   !P:(num->num)->bool.
     P (logipedia_nat_times n)
     ==>
     P (logipedia_nat_filter_nat_type logipedia_nat_times_body n)`;;
