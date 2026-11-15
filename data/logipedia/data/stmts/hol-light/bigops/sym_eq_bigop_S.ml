(*
  Statement-only formalization of Logipedia corpus artifact
  bigops.sym_eq_bigop_S, catalog title "bigops.sym_eq_bigop_S": Leibniz
  equality transports every predicate holding of the polymorphic higher-order
  operator bigop_body at every successor natural-number index to bigop at the
  same index. This file contains no proof.
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
  `!n:num.
   !P:(((num -> bool) -> 'a -> ('a -> 'a -> 'a) ->
        (num -> 'a) -> 'a) -> bool).
     P (logipedia_bigops_bigop_body (SUC n)) ==>
     P (logipedia_bigops_bigop (SUC n))`;;
