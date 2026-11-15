(*
  Statement-only formalization of Logipedia corpus artifact
  connectives.refl_equal, catalog title "connectives.refl_equal": for any type
  and element x, the distinguished equality relation connectives.equal holds
  from x to itself. This file contains no proof.
*)

new_constant
  ("logipedia_connectives_equal", `:'a -> 'a -> bool`);;

let statement =
  `!x:'a.
     (logipedia_connectives_equal:'a->'a->bool) x x`;;
