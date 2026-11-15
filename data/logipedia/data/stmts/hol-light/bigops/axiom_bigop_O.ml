(*
  Statement-only formalization of Logipedia corpus artifact
  bigops.axiom_bigop_O, catalog title "bigops.axiom_bigop_O": the source
  polymorphic equality relation holds between bigop and bigop_body at zero.
  This file contains no proof.
*)

new_constant
  ("logipedia_connectives_equal", `:'a -> 'a -> bool`);;

new_constant
  ("logipedia_bigops_bigop",
   `:num -> (num -> bool) -> 'a -> ('a -> 'a -> 'a) ->
     (num -> 'a) -> 'a`);;

new_constant
  ("logipedia_bigops_bigop_body",
   `:num -> (num -> bool) -> 'a -> ('a -> 'a -> 'a) ->
     (num -> 'a) -> 'a`);;

let statement =
  `logipedia_connectives_equal
     (logipedia_bigops_bigop 0 :
        (num -> bool) -> 'a -> ('a -> 'a -> 'a) -> (num -> 'a) -> 'a)
     (logipedia_bigops_bigop_body 0)`;;
