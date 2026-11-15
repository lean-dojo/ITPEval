(*
  Statement-only formalization of Logipedia corpus artifact nat.leb_elim,
  catalog title "nat.leb_elim": the Boolean less-than-or-equal test on two
  natural numbers satisfies elimination into an arbitrary predicate on
  Booleans, using the ordered and not-ordered cases. This file contains no
  proof.
*)

let logipedia_nat_leb = new_recursive_definition num_RECURSION
  `(logipedia_nat_leb 0 m = T) /\
   (!n m.
      logipedia_nat_leb (SUC n) m =
      if m = 0 then F else logipedia_nat_leb n (PRE m))`;;

let statement =
  `!n m:num.
   !P:bool->bool.
     (n <= m ==> P T) ==>
     (~(n <= m) ==> P F) ==>
     P (logipedia_nat_leb n m)`;;
