(*
  Statement-only formalization of "Insolvability of General Higher Degree Equations
  (Abel-Ruffini)" from Hundred Theorems item 016. This file contains no proof.
*)

needs "Complex/complexnumbers.ml";;

let ABEL_RUFFINI =
 `?z:complex.
      z pow 5 - Cx(&4) * z + Cx(&2) = Cx(&0) /\
      ~(!R:complex->bool.
          ((!n:num. R (Cx(&n))) /\
           (!x:complex. R x ==> R (--x)) /\
           (!x:complex. R x /\ ~(x = Cx(&0)) ==> R (inv x)) /\
           (!x y:complex. R x /\ R y ==> R (x + y)) /\
           (!x y:complex. R x /\ R y ==> R (x * y)) /\
           (!n:num. ~(n = 0) ==>
                    !x y:complex. R x /\ y pow n = x ==> R y))
          ==> R z)`;;
