(*
  Statement-only formalization of Logipedia artifact "bigops.bigop_false":
  a Boolean-selected finite big operation with the constantly false selector
  returns its initial value. This file contains no proof.
*)

let bigop = new_recursive_definition num_RECURSION
  `(bigop 0 (p:num->bool) (nil:A) (op:A->A->A) (f:num->A) = nil) /\
   (bigop (SUC n) p nil op f =
      if p n
      then op (f n) (bigop n p nil op f)
      else bigop n p nil op f)`;;

let BIGOPS_BIGOP_FALSE_STATEMENT =
  `!n (nil:A) (op:A->A->A) (f:num->A).
      bigop n (\i:num. F) nil op f = nil`;;
