(*
  Statement-only formalization of Logipedia corpus artifact
  bigops.eq_bigop_body_O, catalog title "bigops.eq_bigop_body_O": Leibniz
  equality identifies bigop_body at zero with the polymorphic function that
  returns its nil argument. This file contains no proof.
*)

new_constant
  ("logipedia_bigops_bigop_body",
   `:num -> (num -> bool) -> 'a -> ('a -> 'a -> 'a) ->
     (num -> 'a) -> 'a`);;

let statement =
  `!P:(((num -> bool) -> 'a -> ('a -> 'a -> 'a) ->
        (num -> 'a) -> 'a) -> bool).
     P (logipedia_bigops_bigop_body 0) ==>
     P (\p nil op f. nil)`;;
