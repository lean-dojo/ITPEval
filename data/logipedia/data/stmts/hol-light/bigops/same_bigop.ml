(*
  Statement-only formalization of Logipedia corpus artifact bigops.same_bigop,
  catalog title "bigops.same_bigop": predicate-filtered finite big operations
  are equal when their selectors agree below the bound and their selected
  function values agree there. This file contains no proof.
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
  `!k:num. !p1 p2:num->bool. !nil:A. !op:A->A->A. !f g:num->A.
     (!i:num. i < k ==> p1 i = p2 i)
     ==>
     (!i:num. i < k ==> p1 i = T ==> f i = g i)
     ==>
     logipedia_bigops_bigop k p1 nil op f =
     logipedia_bigops_bigop k p2 nil op g`;;
