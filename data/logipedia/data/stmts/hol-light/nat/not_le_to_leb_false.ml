(*
  Statement-only formalization of Logipedia corpus artifact
  nat.not_le_to_leb_false, catalog title "nat.not_le_to_leb_false": for all
  natural numbers n and m, if n is not at most m, then the recursive Boolean
  less-than-or-equal test on n and m is false. This file contains no proof.
*)

let logipedia_nat_leb = new_recursive_definition num_RECURSION
  `(logipedia_nat_leb 0 m = T) /\
   (!n m.
      logipedia_nat_leb (SUC n) m =
      if m = 0 then F else logipedia_nat_leb n (PRE m))`;;

let statement =
  `!n m:num.
     ~(n <= m)
     ==>
     logipedia_nat_leb n m = F`;;
