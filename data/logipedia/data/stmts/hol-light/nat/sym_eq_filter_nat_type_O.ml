(*
  Statement-only formalization of Logipedia corpus artifact
  nat.sym_eq_filter_nat_type_O, catalog title
  "nat.sym_eq_filter_nat_type_O": for every result type and function from
  natural numbers to that type, Leibniz equality transports every predicate
  from the function's value at zero to the natural-type filter at zero. This
  file contains no proof.
*)

new_constant
  ("logipedia_nat_filter_nat_type", `:(num -> 'a) -> num -> 'a`);;

let statement =
  `!return_fn:num->'a.
   !P:'a->bool.
     P (return_fn 0)
     ==> P (logipedia_nat_filter_nat_type return_fn 0)`;;
