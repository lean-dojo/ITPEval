(*
  Statement-only formalization of Logipedia corpus artifact
  nat.axiom_filter_nat_type_S, catalog title
  "nat.axiom_filter_nat_type_S": for every result type, function from natural
  numbers to that type, and natural number n, the source equality relation
  identifies the natural-type filter at the successor of n with the
  function's value at that successor. This file contains no proof.
*)

new_constant
  ("logipedia_connectives_equal", `:'a -> 'a -> bool`);;

new_constant
  ("logipedia_nat_filter_nat_type", `:(num -> 'a) -> num -> 'a`);;

let statement =
  `!return_fn:num->'a.
   !n:num.
     logipedia_connectives_equal
       (logipedia_nat_filter_nat_type return_fn (SUC n))
       (return_fn (SUC n))`;;
