(*
  Statement-only formalization of Logipedia corpus artifact
  bool.axiom_match_bool_type_false, catalog title
  "bool.axiom_match_bool_type_false": the polymorphic Boolean eliminator
  selects its false branch under the source equality relation. This file
  contains no proof.
*)

new_constant
  ("logipedia_connectives_equal", `:'a -> 'a -> bool`);;

new_constant
  ("logipedia_bool_match_bool_type", `:'a -> 'a -> bool -> 'a`);;

let statement =
  `!case_true case_false:'a.
     logipedia_connectives_equal
       (logipedia_bool_match_bool_type case_true case_false F)
       case_false`;;
