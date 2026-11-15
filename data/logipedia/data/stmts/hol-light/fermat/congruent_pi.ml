(*
  Statement-only formalization of Logipedia corpus artifact
  fermat.congruent_pi, catalog title "fermat.congruent_pi": the finite product
  of natural-number values is congruent modulo a positive natural modulus to
  the finite product of their residues. This file contains no proof.
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
  `!f:num->num. !n p:num.
     0 < p
     ==>
     (logipedia_bigops_bigop n (\i. T) 1 (\x y:num. x * y) f) MOD p =
     (logipedia_bigops_bigop
        n (\i. T) 1 (\x y:num. x * y) (\i. (f i) MOD p)) MOD p`;;
