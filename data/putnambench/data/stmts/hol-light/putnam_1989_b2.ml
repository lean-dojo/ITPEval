(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1989_b2:
  every nonempty cancellative semigroup in which each element has only
  finitely many positive powers is a group. This file contains no proof.
*)

let statement =
  `!carrier:A->bool mul:A->A->A.
     (?w:A. w IN carrier) /\
     (!x y:A.
        x IN carrier /\ y IN carrier
        ==> mul x y IN carrier) /\
     (!x y z:A.
        x IN carrier /\ y IN carrier /\ z IN carrier
        ==> mul (mul x y) z = mul x (mul y z)) /\
     (!x y z:A.
        x IN carrier /\ y IN carrier /\ z IN carrier
        ==>
        (mul x y = mul x z ==> y = z) /\
        (mul y x = mul z x ==> y = z)) /\
     (!a:A.
        a IN carrier
        ==>
        FINITE
          {x:A |
             ?n:num powers:num->A.
               powers 0 = a /\
               (!k:num. powers (SUC k) = mul a (powers k)) /\
               powers n = x})
     ==>
     ?e:A.
       e IN carrier /\
       !x:A.
         x IN carrier
         ==>
         mul e x = x /\
         mul x e = x /\
         ?y:A.
           y IN carrier /\
           mul x y = e /\
           mul y x = e`;;
