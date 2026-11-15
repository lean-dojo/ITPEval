(*
  Statement-only formalization of Logipedia corpus artifact
  nat.sym_eq_filter_nat_type_S, catalog title
  "nat.sym_eq_filter_nat_type_S": for every result type, function from natural
  numbers to that type, and natural number n, Leibniz equality transports
  every predicate from the function's value at the successor of n to the
  natural-type filter at that successor. This file contains no proof.
*)

new_constant
  ("logipedia_nat_filter_nat_type", `:(num -> 'a) -> num -> 'a`);;

let statement =
  `!return_fn:num->'a.
   !n:num.
   !P:'a->bool.
     P (return_fn (SUC n))
     ==> P (logipedia_nat_filter_nat_type return_fn (SUC n))`;;
