(*
  Statement-only formalization of Thousand Theorems corpus artifact Q107710112,
  "Cantor's isomorphism theorem": any two countable, dense, nonempty linear
  orders without endpoints are order isomorphic. This file contains no proof.
*)

let Q107710112_CANTOR_ISOMORPHISM_THEOREM =
  `!ltA:A->A->bool. !ltB:B->B->bool.
     (!x:A. ~(ltA x x)) /\
     (!x y z:A. ltA x y /\ ltA y z ==> ltA x z) /\
     (!x y:A. ltA x y \/ x = y \/ ltA y x) /\
     (!x y:A. ltA x y ==> ?z:A. ltA x z /\ ltA z y) /\
     (!x:A. ?y:A. ltA y x) /\
     (!x:A. ?y:A. ltA x y) /\
     COUNTABLE (:A) /\
     (!x:B. ~(ltB x x)) /\
     (!x y z:B. ltB x y /\ ltB y z ==> ltB x z) /\
     (!x y:B. ltB x y \/ x = y \/ ltB y x) /\
     (!x y:B. ltB x y ==> ?z:B. ltB x z /\ ltB z y) /\
     (!x:B. ?y:B. ltB y x) /\
     (!x:B. ?y:B. ltB x y) /\
     COUNTABLE (:B)
     ==> ?f:A->B.
           BIJ f (:A) (:B) /\
           !x y:A. (ltB (f x) (f y) <=> ltA x y)`;;
