(*
  Statement-only formalization of Logipedia corpus artifact bigops.bigop_diff,
  catalog title "bigops.bigop_diff": removing a selected true index from a
  predicate-filtered finite product over natural numbers factors out its
  value. This file contains no proof.
*)

let logipedia_bigops_bigop = new_recursive_definition num_RECURSION
  `(logipedia_bigops_bigop
       0 (p:num->bool) (nil:A) (op:A->A->A) (f:num->A) = nil) /\
   (logipedia_bigops_bigop
       (SUC n) (p:num->bool) (nil:A) (op:A->A->A) (f:num->A) =
      if p n then
        op (f n) (logipedia_bigops_bigop n p nil op f)
      else
        logipedia_bigops_bigop n p nil op f)`;;

let statement =
  `!p:num->bool. !f:num->num. !i n:num.
     i < n
     ==>
     p i = T
     ==>
     logipedia_bigops_bigop n p 1 (\x y:num. x * y) f =
     f i *
     logipedia_bigops_bigop
       n (\x. ~(i = x) /\ p x) 1 (\x y:num. x * y) f`;;
