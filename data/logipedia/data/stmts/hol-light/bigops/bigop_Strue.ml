(*
  Statement-only formalization of Logipedia corpus artifact
  bigops.bigop_Strue, catalog title "bigops.bigop_Strue": extending a
  predicate-filtered finite big operation by one index applies the operation
  to that index's value when the predicate is true there. This file contains
  no proof.
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
  `!k:num. !p:num->bool. !nil:A. !op:A->A->A. !f:num->A.
     p k = T
     ==>
     logipedia_bigops_bigop (SUC k) p nil op f =
     op (f k) (logipedia_bigops_bigop k p nil op f)`;;
