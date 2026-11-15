(*
  Statement-only formalization of Logipedia corpus artifact
  bigops.eq_bigop_body_S, catalog title "bigops.eq_bigop_body_S": Leibniz
  equality identifies bigop_body at each successor index with the function
  that conditionally combines the current value with the preceding bigop.
  This file contains no proof.
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
     P (\p nil op f.
          if p n then
            op (f n) (logipedia_bigops_bigop n p nil op f)
          else
            logipedia_bigops_bigop n p nil op f)`;;
