(*
  Statement-only formalization of Logipedia corpus artifact
  bigops.sym_eq_bigop_body_O, catalog title "bigops.sym_eq_bigop_body_O":
  Leibniz equality transports every predicate holding of the polymorphic
  function that returns its nil argument to bigop_body at zero. This file
  contains no proof.
*)

new_constant
  ("logipedia_bigops_bigop_body",
   `:num -> (num -> bool) -> 'a -> ('a -> 'a -> 'a) ->
     (num -> 'a) -> 'a`);;

let statement =
  `!P:(((num -> bool) -> 'a -> ('a -> 'a -> 'a) ->
        (num -> 'a) -> 'a) -> bool).
     P (\p nil op f. nil) ==>
     P (logipedia_bigops_bigop_body 0)`;;
