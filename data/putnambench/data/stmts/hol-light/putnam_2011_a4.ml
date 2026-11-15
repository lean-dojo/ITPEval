(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2011_a4:
  positive matrix orders admitting an integer matrix whose row self-dot
  products are even and whose distinct-row dot products are odd are exactly
  the odd orders. This file contains no proof.
*)

let statement =
  `let even_integer =
     \x:int. ?k:int. x = &2 * k in
   let odd_integer =
     \x:int. ?k:int. x = &2 * k + &1 in
   let row_dot =
     \n:num. \A:num->num->int. \r s:num.
       isum (0..n - 1) (\j:num. A r j * A s j) in
   !n:num.
     0 < n
     ==>
     ((?A:num->num->int.
         (!r:num.
            r < n
            ==> even_integer (row_dot n A r r)) /\
         (!r s:num.
            r < n /\ s < n /\ ~(r = s)
            ==> odd_integer (row_dot n A r s))) <=>
      ODD n)`;;
