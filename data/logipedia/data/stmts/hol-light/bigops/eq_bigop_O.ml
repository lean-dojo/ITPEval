(*
  Statement-only formalization of Logipedia corpus artifact
  bigops.eq_bigop_O, catalog title "bigops.eq_bigop_O": Leibniz equality
  between the polymorphic higher-order operators bigop and bigop_body at
  zero. This file contains no proof.
*)

new_constant
  ("logipedia_bigops_bigop",
   `:num -> (num -> bool) -> 'a -> ('a -> 'a -> 'a) ->
     (num -> 'a) -> 'a`);;

new_constant
  ("logipedia_bigops_bigop_body",
   `:num -> (num -> bool) -> 'a -> ('a -> 'a -> 'a) ->
     (num -> 'a) -> 'a`);;

let statement =
  `!P:(((num -> bool) -> 'a -> ('a -> 'a -> 'a) ->
        (num -> 'a) -> 'a) -> bool).
     P (logipedia_bigops_bigop 0) ==>
     P (logipedia_bigops_bigop_body 0)`;;
