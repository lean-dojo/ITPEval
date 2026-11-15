(*
  Statement-only formalization of Thousand Theorems corpus artifact Q536640,
  "Hall's marriage theorem": an indexed family of finite sets has an injective
  system of representatives exactly when every finite subfamily has a union at
  least as large as its index set. This file contains no proof.
*)

let Q536640_HALL_S_MARRIAGE_THEOREM =
  `!indices:A->bool.
   !t:A->B->bool.
     (!i:A. i IN indices ==> FINITE (t i))
     ==> ((!s:A->bool.
            FINITE s /\ s SUBSET indices
            ==> CARD s <= CARD (UNIONS (IMAGE t s))) <=>
          ?f:A->B.
            (!x y:A.
               x IN indices /\ y IN indices /\ f x = f y
               ==> x = y) /\
            (!x:A. x IN indices ==> f x IN t x))`;;
