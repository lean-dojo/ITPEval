(*
  Statement-only formalization of Logipedia corpus artifact
  nat.leb_true_to_le, catalog title "nat.leb_true_to_le": if the recursive
  Boolean less-than-or-equal test on two natural numbers is true, then the
  first number is at most the second. This file contains no proof.
*)

let logipedia_nat_leb = new_recursive_definition num_RECURSION
  `(logipedia_nat_leb 0 m = T) /\
   (!n m.
      logipedia_nat_leb (SUC n) m =
      if m = 0 then F else logipedia_nat_leb n (PRE m))`;;

let statement =
  `!n m:num.
     logipedia_nat_leb n m = T
     ==>
     n <= m`;;
