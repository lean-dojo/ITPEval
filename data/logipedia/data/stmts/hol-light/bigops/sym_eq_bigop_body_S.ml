(*
  Statement-only formalization of Logipedia corpus artifact
  bigops.sym_eq_bigop_body_S, catalog title "bigops.sym_eq_bigop_body_S":
  Leibniz equality transports every predicate holding of the conditional
  successor-step function to bigop_body at the corresponding successor index.
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
     P (\p nil op f.
          if p n then
            op (f n) (logipedia_bigops_bigop n p nil op f)
          else
            logipedia_bigops_bigop n p nil op f)
     ==>
     P (logipedia_bigops_bigop_body (SUC n))`;;
