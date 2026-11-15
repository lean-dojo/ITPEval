(*
  Statement-only formalization of Logipedia corpus artifact
  bool.eq_match_bool_type_true, catalog title
  "bool.eq_match_bool_type_true": the polymorphic Boolean eliminator returns
  its true branch at true under Leibniz equality. This file contains no proof.
*)

new_constant
  ("logipedia_bool_match_bool_type", `:'a -> 'a -> bool -> 'a`);;

let statement =
  `!case_true case_false:'a.
     logipedia_bool_match_bool_type case_true case_false T = case_true`;;
