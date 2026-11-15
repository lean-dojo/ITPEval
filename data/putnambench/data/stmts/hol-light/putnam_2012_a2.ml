(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2012_a2:
  cancellation in a commutative semigroup whose left translations are
  surjective. This file contains no proof.
*)

let statement =
  `!op:'a->'a->'a. !a b c:'a.
     ((!x y:'a. op x y = op y x) /\
      (!x y z:'a. op (op x y) z = op x (op y z)) /\
      (!x y:'a. ?z:'a. op x z = y) /\
      op a c = op b c)
     ==>
     a = b`;;
