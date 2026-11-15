(*
  Statement-only formalization of Logipedia corpus artifact nat.match_nat_prop,
  catalog title "nat.match_nat_prop": a predicate holding at zero and at every
  successor holds for every natural number. This file contains no proof.
*)

let statement =
  `!return_:num->bool.
     return_ 0
     ==> (!n:num. return_ (SUC n))
     ==> !z:num. return_ z`;;
