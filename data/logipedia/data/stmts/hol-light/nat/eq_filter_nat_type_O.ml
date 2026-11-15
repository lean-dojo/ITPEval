(*
  Statement-only formalization of Logipedia corpus artifact
  nat.eq_filter_nat_type_O, catalog title "nat.eq_filter_nat_type_O": for
  every result type and function from natural numbers to that type, Leibniz
  equality transports predicates from the natural-type filter at zero to the
  function's value at zero. This file contains no proof.
*)

new_constant
  ("logipedia_nat_filter_nat_type", `:(num -> 'a) -> num -> 'a`);;

let statement =
  `!return_fn:num->'a.
   !P:'a->bool.
     P (logipedia_nat_filter_nat_type return_fn 0)
     ==> P (return_fn 0)`;;
