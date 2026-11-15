(*
  Statement-only formalization of Logipedia corpus artifact bigops.bigop_I_gen,
  catalog title "bigops.bigop_I_gen": reindexing a predicate-filtered finite
  product over a natural-number interval. This file contains no proof.
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
  `!a b:num. !p:num->bool. !f:num->num.
     a <= b
     ==>
     logipedia_bigops_bigop
       (b - a) (\i. p (i + a)) 1 (\x y:num. x * y) (\i. f (i + a)) =
     logipedia_bigops_bigop
       b (\i. a <= i /\ p i) 1 (\x y:num. x * y) (\i. f i)`;;
