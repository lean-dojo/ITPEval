(*
  Statement-only formalization of Logipedia corpus artifact
  bool.axiom_match_bool_type_true, catalog title
  "bool.axiom_match_bool_type_true": the polymorphic Boolean eliminator
  selects its true branch under the source equality relation. This file
  contains no proof.
*)

new_constant
  ("logipedia_connectives_equal", `:'a -> 'a -> bool`);;

new_constant
  ("logipedia_bool_match_bool_type", `:'a -> 'a -> bool -> 'a`);;

let statement =
  `!case_true case_false:'a.
     logipedia_connectives_equal
       (logipedia_bool_match_bool_type case_true case_false T)
       case_true`;;
