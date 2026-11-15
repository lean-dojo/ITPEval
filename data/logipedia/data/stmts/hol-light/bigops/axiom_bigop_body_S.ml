(*
  Statement-only formalization of Logipedia corpus artifact
  bigops.axiom_bigop_body_S, catalog title "bigops.axiom_bigop_body_S": the
  source polymorphic equality relation identifies bigop_body at a successor
  index with the conditional extension of the preceding bigop. This file
  contains no proof.
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
  `!n:num.
     logipedia_connectives_equal
       (logipedia_bigops_bigop_body (SUC n) :
          (num -> bool) -> 'a -> ('a -> 'a -> 'a) -> (num -> 'a) -> 'a)
       (\p nil op f.
          if p n then
            op (f n) (logipedia_bigops_bigop n p nil op f)
          else
            logipedia_bigops_bigop n p nil op f)`;;
