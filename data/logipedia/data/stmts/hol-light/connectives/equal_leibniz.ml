(*
  Statement-only formalization of Logipedia corpus artifact
  connectives.equal_leibniz, catalog title "connectives.equal_leibniz": for
  any type and elements x and y, the distinguished equality relation
  connectives.equal x y entails transport of every predicate from x to y.
  This file contains no proof.
*)

new_constant
  ("logipedia_connectives_equal", `:'a -> 'a -> bool`);;

let statement =
  `!x y:'a.
     (logipedia_connectives_equal:'a->'a->bool) x y
     ==> !P:'a->bool. P x ==> P y`;;
