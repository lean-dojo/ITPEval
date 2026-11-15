(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2001_a3:
  classification of the integers for which a specified quartic factors into
  two nonconstant polynomials with integer coefficients. This file contains
  no proof.
*)

let statement =
  `let eval =
     \p:int list. \x:int.
       ITLIST (\c acc. c + x * acc) p (&0) in
   let nonconstant =
     \p:int list.
       ?i:num. 0 < i /\ i < LENGTH p /\ ~(EL i p = &0) in
   !m:int.
     ((?a b:int list.
         nonconstant a /\
         nonconstant b /\
         (!x:int.
            eval a x * eval b x =
            x pow 4 - ((&2:int) * m + &4) * x pow 2 +
            (m - &2) pow 2))
      <=>
      (?k:int. m = k pow 2 \/ m = &2 * k pow 2))`;;
