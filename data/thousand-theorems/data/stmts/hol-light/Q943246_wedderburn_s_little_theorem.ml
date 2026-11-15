(*
  Statement-only formalization of Thousand Theorems corpus artifact Q943246
  (thousand-theorems__hol-light__Q943246), "Wedderburn's little theorem":
  every finite division ring has commutative multiplication and hence is a
  field. This file contains no proof.
*)

let Q943246_WEDDERBURN_LITTLE_THEOREM =
  `let is_division_ring =
     \(zeroD:D) (oneD:D) (addD:D->D->D) (mulD:D->D->D)
      (negD:D->D) (invD:D->D).
       ~(zeroD = oneD) /\
       (!x:D. addD zeroD x = x /\ addD x zeroD = x) /\
       (!x y:D. addD x y = addD y x) /\
       (!x y z:D. addD (addD x y) z = addD x (addD y z)) /\
       (!x:D.
          addD (negD x) x = zeroD /\ addD x (negD x) = zeroD) /\
       (!x:D. mulD oneD x = x /\ mulD x oneD = x) /\
       (!x y z:D. mulD (mulD x y) z = mulD x (mulD y z)) /\
       (!x y z:D.
          mulD x (addD y z) = addD (mulD x y) (mulD x z)) /\
       (!x y z:D.
          mulD (addD x y) z = addD (mulD x z) (mulD y z)) /\
       (!x:D. mulD zeroD x = zeroD /\ mulD x zeroD = zeroD) /\
       invD zeroD = zeroD /\
       (!x:D.
          ~(x = zeroD)
          ==> mulD x (invD x) = oneD /\ mulD (invD x) x = oneD) in
   !zeroD oneD:D.
   !addD mulD:D->D->D.
   !negD invD:D->D.
     is_division_ring zeroD oneD addD mulD negD invD /\
     FINITE (UNIV:D->bool)
     ==> !x y:D. mulD x y = mulD y x`;;
