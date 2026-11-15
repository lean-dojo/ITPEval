(*
  Statement-only formalization of Logipedia corpus artifact
  fermat.eq_fact_pi_p, catalog title "fermat.eq_fact_pi_p": every natural
  factorial equals the finite product of the successive naturals from one.
  This file contains no proof.
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
  `!n:num.
     FACT n =
     logipedia_bigops_bigop
       (SUC n - SUC 0)
       (\i. T)
       (SUC 0)
       (\x y:num. x * y)
       (\i. i + SUC 0)`;;
