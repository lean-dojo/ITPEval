(*
  Statement-only formalization of Logipedia corpus artifact
  bool.eq_match_bool_type_false, catalog title
  "bool.eq_match_bool_type_false": the polymorphic Boolean eliminator returns
  its false branch at false under Leibniz equality. This file contains no proof.
*)

new_constant
  ("logipedia_bool_match_bool_type", `:'a -> 'a -> bool -> 'a`);;

let statement =
  `!case_true case_false:'a.
     logipedia_bool_match_bool_type case_true case_false F = case_false`;;
