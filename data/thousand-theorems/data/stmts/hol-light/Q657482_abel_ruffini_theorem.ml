(*
  Statement-only formalization of Thousand Theorems corpus artifact Q657482,
  (thousand-theorems__hol-light__Q657482), "Abel–Ruffini theorem": there
  exists a complex number algebraic over the rationals that is not solvable
  by radicals over the rationals. This file contains no proof.
*)

needs "Library/floor.ml";;
needs "Complex/cpoly.ml";;

let Q657482_ABEL_RUFFINI_THEOREM =
  `let is_rational_complex =
     \c:complex. ?q:real. rational q /\ c = Cx q in
   let is_algebraic_over_rationals =
     \z:complex.
       ?p:complex list.
         ALL is_rational_complex p /\
         ~(poly p = poly []) /\
         poly p z = Cx(&0) in
   let is_radically_solvable_over_rationals =
     \z:complex.
       !R:complex->bool.
         ((!q:real. rational q ==> R (Cx q)) /\
          (!x:complex. R x ==> R (--x)) /\
          (!x:complex. R x /\ ~(x = Cx(&0)) ==> R (inv x)) /\
          (!x y:complex. R x /\ R y ==> R (x + y)) /\
          (!x y:complex. R x /\ R y ==> R (x * y)) /\
          (!n:num. ~(n = 0) ==>
             !x y:complex. R x /\ y pow n = x ==> R y))
         ==> R z in
   ?z:complex.
     is_algebraic_over_rationals z /\
     ~(is_radically_solvable_over_rationals z)`;;
