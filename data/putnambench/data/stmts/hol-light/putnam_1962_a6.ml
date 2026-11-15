(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1962_a6:
  an addition- and multiplication-closed rational set satisfying exact sign
  trichotomy is the set of positive rationals. This file contains no proof.
*)

let statement =
  `let is_rational =
     \x:real.
       ?p q:int.
         ~(q = &0) /\
         x = real_of_int p / real_of_int q in
   !S:real->bool.
     S SUBSET {x:real | is_rational x} /\
     (!a b:real. a IN S /\ b IN S ==> a + b IN S) /\
     (!a b:real. a IN S /\ b IN S ==> a * b IN S) /\
     (!r:real.
        is_rational r
        ==>
        (r IN S \/ --r IN S \/ r = &0) /\
        ~(r IN S /\ --r IN S) /\
        ~(r IN S /\ r = &0) /\
        ~(--r IN S /\ r = &0))
     ==>
     S = {r:real | is_rational r /\ &0 < r}`;;
