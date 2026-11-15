(*
  Statement-only formalization of Logipedia corpus artifact
  bool.sym_eq_match_bool_type_true, catalog title
  "bool.sym_eq_match_bool_type_true": under Leibniz equality, the true branch
  equals the result of the polymorphic Boolean eliminator at true. This file
  contains no proof.
*)

new_constant
  ("logipedia_bool_match_bool_type", `:'a -> 'a -> bool -> 'a`);;

let statement =
  `!case_true case_false:'a.
     case_true =
     logipedia_bool_match_bool_type case_true case_false T`;;
