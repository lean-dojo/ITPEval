(*
  Statement-only formalization of Logipedia corpus artifact
  bigops.bigop_Sfalse, catalog title "bigops.bigop_Sfalse": extending a
  predicate-filtered finite big operation by one index leaves its value
  unchanged when the predicate is false at that index. This file contains no
  proof.
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
     p k = F
     ==>
     logipedia_bigops_bigop (SUC k) p nil op f =
     logipedia_bigops_bigop k p nil op f`;;
