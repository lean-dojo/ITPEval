(* Statement-only formalization of PutnamBench corpus artifact putnam_2025_a6
   (putnambench__rocq__putnam_2025_a6): exact 2-adic divisibility of a
   difference formed from a recursively defined integer sequence. This file
   contains no proof. *)

From Stdlib Require Import Arith.PeanoNat ZArith.

Fixpoint putnam_2025_a6_zpow_nat (base : Z) (exponent : nat) : Z :=
  match exponent with
  | O => 1%Z
  | S n => (base * putnam_2025_a6_zpow_nat base n)%Z
  end.

Fixpoint putnam_2025_a6_b (n : nat) : Z :=
  match n with
  | O => 0%Z
  | S m =>
      (2 * putnam_2025_a6_zpow_nat (putnam_2025_a6_b m) 2 +
       putnam_2025_a6_b m + 1)%Z
  end.

Theorem putnam_2025_a6 :
  forall k : nat,
    (1 <= k)%nat ->
    Z.divide
      (putnam_2025_a6_zpow_nat 2 (2 * k + 2))
      (putnam_2025_a6_b (Nat.pow 2 (k + 1)) -
       2 * putnam_2025_a6_b (Nat.pow 2 k))%Z /\
    ~ Z.divide
        (putnam_2025_a6_zpow_nat 2 (2 * k + 3))
        (putnam_2025_a6_b (Nat.pow 2 (k + 1)) -
         2 * putnam_2025_a6_b (Nat.pow 2 k))%Z.
Admitted.
