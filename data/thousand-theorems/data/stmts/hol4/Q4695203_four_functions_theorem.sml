(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q4695203, "Four functions theorem": the Ahlswede-Daykin inequality for
  nonnegative functions on a distributive lattice and finite families.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory;

val q4695203_distributive_lattice_def = new_definition (
  "q4695203_distributive_lattice_def",
  ``q4695203_distributive_lattice
      (leq : 'a -> 'a -> bool)
      (meet : 'a -> 'a -> 'a)
      (join : 'a -> 'a -> 'a) <=>
      (!x. leq x x) /\
      (!x y z. leq x y /\ leq y z ==> leq x z) /\
      (!x y. leq x y /\ leq y x ==> x = y) /\
      (!x y. leq (meet x y) x /\ leq (meet x y) y) /\
      (!x y z. leq z x /\ leq z y ==> leq z (meet x y)) /\
      (!x y. leq x (join x y) /\ leq y (join x y)) /\
      (!x y z. leq x z /\ leq y z ==> leq (join x y) z) /\
      (!x y z.
        leq
          (meet (join x y) (join x z))
          (join x (meet y z)))``);

val q4695203_strict_less_def = new_definition (
  "q4695203_strict_less_def",
  ``q4695203_strict_less
      (leq : 'r -> 'r -> bool) (x : 'r) (y : 'r) <=>
      leq x y /\ ~leq y x``);

val q4695203_ordered_comm_semiring_def = new_definition (
  "q4695203_ordered_comm_semiring_def",
  ``q4695203_ordered_comm_semiring
      (zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r)
      (mulR : 'r -> 'r -> 'r)
      (leq : 'r -> 'r -> bool) <=>
      (!x y. addR x y = addR y x) /\
      (!x y z. addR (addR x y) z = addR x (addR y z)) /\
      (!x. addR zeroR x = x) /\
      (!x y. mulR x y = mulR y x) /\
      (!x y z. mulR (mulR x y) z = mulR x (mulR y z)) /\
      (!x. mulR oneR x = x) /\
      (!x y z.
        mulR x (addR y z) = addR (mulR x y) (mulR x z)) /\
      (!x. mulR zeroR x = zeroR) /\
      (!x. leq x x) /\
      (!x y z. leq x y /\ leq y z ==> leq x z) /\
      (!x y. leq x y /\ leq y x ==> x = y) /\
      (!x y. leq x y \/ leq y x) /\
      (!x y z. leq x y ==> leq (addR x z) (addR y z)) /\
      (!x y z. leq (addR x z) (addR y z) ==> leq x y) /\
      leq zeroR oneR /\
      zeroR <> oneR /\
      (!a b c.
        q4695203_strict_less leq zeroR a /\
        q4695203_strict_less leq b c
        ==>
        q4695203_strict_less leq (mulR a b) (mulR a c)) /\
      (!a b c.
        q4695203_strict_less leq zeroR c /\
        q4695203_strict_less leq a b
        ==>
        q4695203_strict_less leq (mulR a c) (mulR b c)) /\
      (!a b. leq a b ==> ?c. b = addR a c)``);

val q4695203_sum_def = new_definition (
  "q4695203_sum_def",
  ``q4695203_sum
      (zeroR : 'r) (addR : 'r -> 'r -> 'r)
      (f : 'a -> 'r) (s : 'a set) =
      ITSET (\x acc. addR (f x) acc) s zeroR``);

val q4695203_pair_image_def = new_definition (
  "q4695203_pair_image_def",
  ``q4695203_pair_image
      (opn : 'a -> 'a -> 'a) (s : 'a set) (t : 'a set) =
      {z : 'a | ?x y. x IN s /\ y IN t /\ z = opn x y}``);

val four_functions_theorem =
  ``!(leA : 'a -> 'a -> bool)
      (meet : 'a -> 'a -> 'a) (join : 'a -> 'a -> 'a)
      (zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (leR : 'r -> 'r -> bool)
      (f1 : 'a -> 'r) (f2 : 'a -> 'r)
      (f3 : 'a -> 'r) (f4 : 'a -> 'r)
      (s : 'a set) (t : 'a set).
      q4695203_distributive_lattice leA meet join /\
      q4695203_ordered_comm_semiring zeroR oneR addR mulR leR /\
      FINITE s /\ FINITE t /\
      (!a. leR zeroR (f1 a)) /\
      (!a. leR zeroR (f2 a)) /\
      (!a. leR zeroR (f3 a)) /\
      (!a. leR zeroR (f4 a)) /\
      (!a b.
        leR
          (mulR (f1 a) (f2 b))
          (mulR (f3 (meet a b)) (f4 (join a b))))
      ==>
      leR
        (mulR
          (q4695203_sum zeroR addR f1 s)
          (q4695203_sum zeroR addR f2 t))
        (mulR
          (q4695203_sum zeroR addR f3
            (q4695203_pair_image meet s t))
          (q4695203_sum zeroR addR f4
            (q4695203_pair_image join s t)))``;
