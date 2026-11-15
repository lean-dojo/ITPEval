(* Statement-only formalization of PutnamBench artifact putnam_1984_b3:
   every finite type with at least two elements admits a right-cancellative
   binary operation with no associative triple. This file contains no proof. *)

From Stdlib Require Import Lists.List Arith.PeanoNat.

Definition putnam_1984_b3_finite_card_at_least_two (F : Type) : Prop :=
  exists enumeration : list F,
    NoDup enumeration /\
    (forall x : F, List.In x enumeration) /\
    (2 <= length enumeration)%nat.

Definition putnam_1984_b3_solution : Prop := True.

Theorem putnam_1984_b3 :
  (forall F : Type,
    putnam_1984_b3_finite_card_at_least_two F ->
    exists mul : F -> F -> F,
      forall x y z : F,
        (mul x z = mul y z -> x = y) /\
        mul x (mul y z) <> mul (mul x y) z) <->
  putnam_1984_b3_solution.
Admitted.
