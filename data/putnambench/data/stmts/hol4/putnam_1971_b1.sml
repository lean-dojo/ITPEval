(*
  Statement-only formalization of PutnamBench artifact putnam_1971_b1:
  an idempotent binary operation satisfying the cyclic law
  (x op y) op z = (y op z) op x is associative and commutative.
  This file contains no proof.
*)

open HolKernel Parse boolLib;

val putnam_1971_b1 =
  ``!(op : 'a -> 'a -> 'a).
      ((!x. op x x = x) /\
       (!x y z. op (op x y) z = op (op y z) x))
      ==>
      ((!x y z. op (op x y) z = op x (op y z)) /\
       (!x y. op x y = op y x))``;
