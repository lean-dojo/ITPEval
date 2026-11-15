(*
  Statement-only formalization of PutnamBench artifact putnam_1972_a2:
  two involutive laws force a binary operation to be commutative, but do not
  force it to be associative. This file contains no proof.
*)

let statement =
  `(!op:'a->'a->'a.
      (!x y:'a.
         op x (op x y) = y /\
         op (op y x) x = y)
      ==>
      (!x y:'a. op x y = op y x)) /\
   (?S:real->bool.
      ?op:real->real->real.
        (!x y:real.
           x IN S /\ y IN S
           ==>
           op x y IN S /\
           op x (op x y) = y /\
           op (op y x) x = y) /\
        ~(!x y z:real.
            x IN S /\ y IN S /\ z IN S
            ==>
            op x (op y z) = op (op x y) z))`;;
