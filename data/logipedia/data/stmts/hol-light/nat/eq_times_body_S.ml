(*
  Statement-only formalization of Logipedia corpus artifact
  nat.eq_times_body_S, catalog title "nat.eq_times_body_S": for every natural
  number n, Leibniz equality transports every predicate holding of times_body
  at the successor of n to the function mapping m to plus m (times n m). This
  file contains no proof.
*)

new_constant
  ("logipedia_nat_plus", `:num -> num -> num`);;

new_constant
  ("logipedia_nat_times", `:num -> num -> num`);;

new_constant
  ("logipedia_nat_times_body", `:num -> num -> num`);;

let statement =
  `!n:num.
   !P:((num -> num) -> bool).
     P (logipedia_nat_times_body (SUC n)) ==>
     P (\m:num. logipedia_nat_plus m (logipedia_nat_times n m))`;;
