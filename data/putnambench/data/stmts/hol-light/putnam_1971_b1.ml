(*
  Statement-only formalization of PutnamBench artifact putnam_1971_b1:
  an idempotent binary operation satisfying the cyclic law is associative and
  commutative. This file contains no proof.
*)

let statement =
  `!op:'a->'a->'a.
     (!x:'a. op x x = x) /\
     (!x y z:'a. op (op x y) z = op (op y z) x)
     ==>
     ((!x y z:'a. op (op x y) z = op x (op y z)) /\
      (!x y:'a. op x y = op y x))`;;
