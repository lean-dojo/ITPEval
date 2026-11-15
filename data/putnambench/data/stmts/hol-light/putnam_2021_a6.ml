(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2021_a6:
  a polynomial with coefficients in {0,1} that factors into two nonconstant
  integer polynomials has a composite value at 2. This file contains no proof.
*)

let statement =
  `let eval =
     \p:int list. \x:int.
       ITLIST (\c acc. c + x * acc) p (&0) in
   let zero_one_coefficients =
     \p:int list.
       !i:num.
         i < LENGTH p
         ==> EL i p = (&0:int) \/ EL i p = &1 in
   let nonconstant =
     \p:int list.
       ?i:num. 0 < i /\ i < LENGTH p /\ ~(EL i p = (&0:int)) in
   let integer_prime =
     \z:int. prime (num_of_int (abs z)) in
   !p:int list.
     zero_one_coefficients p /\
     (?q r:int list.
        nonconstant q /\
        nonconstant r /\
        !x:int. eval p x = eval q x * eval r x)
     ==>
     ~(eval p (&2) = (&0:int)) /\
     ~(eval p (&2) = &1) /\
     ~(integer_prime (eval p (&2)))`;;
