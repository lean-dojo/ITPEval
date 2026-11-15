(*
  Statement-only formalization of Logipedia corpus artifact nat.eq_eqb,
  catalog title "nat.eq_eqb": for every natural number n, Leibniz equality
  relates eqb n to the natural-type filter applied to eqb_body at n. This
  file contains no proof.
*)

new_constant
  ("logipedia_nat_filter_nat_type", `:(num -> 'a) -> num -> 'a`);;

new_constant
  ("logipedia_nat_eqb", `:num -> num -> bool`);;

new_constant
  ("logipedia_nat_eqb_body", `:num -> num -> bool`);;

let statement =
  `!n:num.
   !P:(num->bool)->bool.
     P (logipedia_nat_eqb n)
     ==>
     P (logipedia_nat_filter_nat_type logipedia_nat_eqb_body n)`;;
