(*
  Statement-only formalization of the Babel-formal artifact ideals: arbitrary
  intersections and binary sums of ideals in a commutative ring are ideals.
  This file contains no proof.
*)

open HolKernel Parse boolLib;

val _ = new_theory "hello";

val babel_cring_def = new_definition (
  "babel_cring_def",
  ``babel_cring (zeroR : 'r) (oneR : 'r)
      (add : 'r -> 'r -> 'r) (mul : 'r -> 'r -> 'r)
      (opp : 'r -> 'r) <=>
      (!x y. add x y = add y x) /\
      (!x y z. add (add x y) z = add x (add y z)) /\
      (!x. add x zeroR = x) /\
      (!x. add x (opp x) = zeroR) /\
      (!x y. mul x y = mul y x) /\
      (!x y z. mul (mul x y) z = mul x (mul y z)) /\
      (!x. mul x oneR = x) /\
      (!a x y. mul a (add x y) = add (mul a x) (mul a y)) /\
      (!x y. opp (add x y) = add (opp x) (opp y))``);

val babel_is_ideal_def = new_definition (
  "babel_is_ideal_def",
  ``babel_is_ideal (zeroR : 'r) (add : 'r -> 'r -> 'r)
      (mul : 'r -> 'r -> 'r) (opp : 'r -> 'r)
      (ideal : 'r -> bool) <=>
      ideal zeroR /\
      (!x y. ideal x /\ ideal y ==> ideal (add x y)) /\
      (!x. ideal x ==> ideal (opp x)) /\
      (!a x. ideal x ==> ideal (mul a x))``);

val babel_ideal_inter_def = new_definition (
  "babel_ideal_inter_def",
  ``babel_ideal_inter (index : 'i -> bool)
      (fam : 'i -> 'r -> bool) =
      (\x. !i. index i ==> fam i x)``);

val inter_isIdeal =
  ``!(zeroR : 'r) (oneR : 'r)
      (add : 'r -> 'r -> 'r) (mul : 'r -> 'r -> 'r)
      (opp : 'r -> 'r) (index : 'i -> bool)
      (fam : 'i -> 'r -> bool).
      babel_cring zeroR oneR add mul opp ==>
      (!i. index i ==>
           babel_is_ideal zeroR add mul opp (fam i)) ==>
      babel_is_ideal zeroR add mul opp
        (babel_ideal_inter index fam)``;

val babel_ideal_sum_def = new_definition (
  "babel_ideal_sum_def",
  ``babel_ideal_sum (add : 'r -> 'r -> 'r)
      (ideal1 : 'r -> bool) (ideal2 : 'r -> bool) =
      (\x. ?a b. ideal1 a /\ ideal2 b /\ x = add a b)``);

val sum_isIdeal =
  ``!(zeroR : 'r) (oneR : 'r)
      (add : 'r -> 'r -> 'r) (mul : 'r -> 'r -> 'r)
      (opp : 'r -> 'r) (ideal1 : 'r -> bool) (ideal2 : 'r -> bool).
      babel_cring zeroR oneR add mul opp ==>
      babel_is_ideal zeroR add mul opp ideal1 ==>
      babel_is_ideal zeroR add mul opp ideal2 ==>
      babel_is_ideal zeroR add mul opp
        (babel_ideal_sum add ideal1 ideal2)``;

val _ = export_theory();
