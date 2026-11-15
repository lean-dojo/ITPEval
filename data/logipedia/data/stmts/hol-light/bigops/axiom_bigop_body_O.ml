(*
  Statement-only formalization of Logipedia corpus artifact
  bigops.axiom_bigop_body_O, catalog title "bigops.axiom_bigop_body_O": the
  source polymorphic equality relation identifies bigop_body at zero with the
  function that returns its nil argument. This file contains no proof.
*)

new_constant
  ("logipedia_connectives_equal", `:'a -> 'a -> bool`);;

new_constant
  ("logipedia_bigops_bigop_body",
   `:num -> (num -> bool) -> 'a -> ('a -> 'a -> 'a) ->
     (num -> 'a) -> 'a`);;

let statement =
  `logipedia_connectives_equal
     (logipedia_bigops_bigop_body 0 :
        (num -> bool) -> 'a -> ('a -> 'a -> 'a) -> (num -> 'a) -> 'a)
     (\p nil op f. nil)`;;
