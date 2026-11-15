(*
  Statement-only formalization of Logipedia corpus artifact
  nat.axiom_filter_nat_type_O, catalog title
  "nat.axiom_filter_nat_type_O": for every result type and every function
  from natural numbers to that type, the source equality relation identifies
  the natural-type filter at zero with the function's value at zero. This
  file contains no proof.
*)

new_constant
  ("logipedia_connectives_equal", `:'a -> 'a -> bool`);;

new_constant
  ("logipedia_nat_filter_nat_type", `:(num -> 'a) -> num -> 'a`);;

let statement =
  `!return_fn:num->'a.
     logipedia_connectives_equal
       (logipedia_nat_filter_nat_type return_fn 0)
       (return_fn 0)`;;
