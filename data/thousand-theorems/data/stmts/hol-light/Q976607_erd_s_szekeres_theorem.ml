(*
  Statement-only formalization of Thousand Theorems corpus artifact Q976607
  (thousand-theorems__hol-light__Q976607), "Erdős–Szekeres theorem": an
  injective sequence indexed by a finite linear order with more than r * s
  entries has an increasing subsequence longer than r or a decreasing
  subsequence longer than s. This file contains no proof.
*)

let Q976607_ERDOS_SZEKERES_THEOREM =
  `let strict_linear_order_A =
     \(lt:A->A->bool).
       (!x:A. ~(lt x x)) /\
       (!x y z:A. lt x y /\ lt y z ==> lt x z) /\
       (!x y:A. lt x y \/ x = y \/ lt y x) in
   let strict_linear_order_B =
     \(lt:B->B->bool).
       (!x:B. ~(lt x x)) /\
       (!x y z:B. lt x y /\ lt y z ==> lt x z) /\
       (!x y:B. lt x y \/ x = y \/ lt y x) in
   !r s:num.
   !ltA:A->A->bool.
   !ltB:B->B->bool.
   !f:A->B.
     FINITE (UNIV:A->bool) /\
     strict_linear_order_A ltA /\
     strict_linear_order_B ltB /\
     (!x y:A. f x = f y ==> x = y) /\
     r * s < CARD (UNIV:A->bool)
     ==>
     ((?t:A->bool.
         FINITE t /\
         r < CARD t /\
         (!x y:A.
            x IN t /\ y IN t /\ ltA x y
            ==> ltB (f x) (f y))) \/
      (?t:A->bool.
         FINITE t /\
         s < CARD t /\
         (!x y:A.
            x IN t /\ y IN t /\ ltA x y
            ==> ltB (f y) (f x))))`;;
