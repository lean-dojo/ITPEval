(*
  Statement-only formalization of Logipedia corpus artifact
  exp.axiom_exp_body_S, catalog title "exp.axiom_exp_body_S": for all natural
  numbers n and m, the source equality relation identifies exp_body n at the
  successor of m with exp n m multiplied by n. This file contains no proof.
*)

new_constant
  ("logipedia_connectives_equal", `:'a -> 'a -> bool`);;

new_constant
  ("logipedia_exp_exp", `:num -> num -> num`);;

new_constant
  ("logipedia_exp_exp_body", `:num -> num -> num`);;

let statement =
  `!n m:num.
     logipedia_connectives_equal
       (logipedia_exp_exp_body n (SUC m))
       (logipedia_exp_exp n m * n)`;;
