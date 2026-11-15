(*
  Statement-only formalization of Logipedia corpus artifact
  bigops.eq_bigop_S, catalog title "bigops.eq_bigop_S": Leibniz equality
  between the polymorphic higher-order operators bigop and bigop_body at
  every successor natural-number index. This file contains no proof.
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
     P (logipedia_bigops_bigop (SUC n)) ==>
     P (logipedia_bigops_bigop_body (SUC n))`;;
