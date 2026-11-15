(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1989_b2:
  every nonempty cancellative semigroup in which each element has only
  finitely many positive powers is a group. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val putnam_1989_b2 =
  ``let putnam_1989_b2_solution = T
    in
      ((!carrier : 'a set. !mul : 'a -> 'a -> 'a.
          carrier <> {} /\
          (!x y : 'a.
             x IN carrier /\ y IN carrier
             ==>
             mul x y IN carrier) /\
          (!x y z : 'a.
             x IN carrier /\ y IN carrier /\ z IN carrier
             ==>
             mul (mul x y) z = mul x (mul y z)) /\
          (!x y z : 'a.
             x IN carrier /\ y IN carrier /\ z IN carrier
             ==>
             (mul x y = mul x z ==> y = z) /\
             (mul y x = mul z x ==> y = z)) /\
          (!a : 'a.
             a IN carrier
             ==>
             FINITE
               (IMAGE
                  (\n : num. FUNPOW (mul a) n a)
                  (UNIV : num set)))
          ==>
          ?e : 'a.
            e IN carrier /\
            !x : 'a.
              x IN carrier
              ==>
              mul e x = x /\
              mul x e = x /\
              ?y : 'a.
                y IN carrier /\
                mul x y = e /\
                mul y x = e)
       <=>
       putnam_1989_b2_solution)``;
