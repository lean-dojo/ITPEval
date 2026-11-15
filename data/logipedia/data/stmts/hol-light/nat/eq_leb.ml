(*
  Statement-only formalization of Logipedia corpus artifact nat.eq_leb,
  catalog title "nat.eq_leb": for every natural number n, Leibniz equality
  relates leb n to the natural-type filter applied to leb_body at n. This
  file contains no proof.
*)

new_constant
  ("logipedia_nat_filter_nat_type", `:(num -> 'a) -> num -> 'a`);;

new_constant
  ("logipedia_nat_leb", `:num -> num -> bool`);;

new_constant
  ("logipedia_nat_leb_body", `:num -> num -> bool`);;

let statement =
  `!n:num.
   !P:(num->bool)->bool.
     P (logipedia_nat_leb n)
     ==>
     P (logipedia_nat_filter_nat_type logipedia_nat_leb_body n)`;;
