(* Statement-only formalization of PutnamBench corpus artifact putnam_1997_b4:
   an alternating sum of coefficients of powers of 1 + x + x^2 lies between
   zero and one. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat ZArith.

Open Scope Z_scope.

Fixpoint putnam_1997_b4_coefficient (m n : nat) : Z :=
  match m with
  | O =>
      match n with
      | O => 1
      | S _ => 0
      end
  | S m' =>
      putnam_1997_b4_coefficient m' n +
      match n with
      | O => 0
      | S n' => putnam_1997_b4_coefficient m' n'
      end +
      match n with
      | O => 0
      | S O => 0
      | S (S n') => putnam_1997_b4_coefficient m' n'
      end
  end.

Fixpoint putnam_1997_b4_sign (i : nat) : Z :=
  match i with
  | O => 1
  | S i' => - putnam_1997_b4_sign i'
  end.

Fixpoint putnam_1997_b4_sum
    (a : nat -> nat -> Z) (k count : nat) : Z :=
  match count with
  | O => 0
  | S i =>
      putnam_1997_b4_sum a k i +
      putnam_1997_b4_sign i * a (k - i)%nat i
  end.

Theorem putnam_1997_b4 :
  forall a : nat -> nat -> Z,
    (forall m n : nat,
      a m n = putnam_1997_b4_coefficient m n) ->
    forall k : nat,
      let total :=
        putnam_1997_b4_sum a k (S (Nat.div (2 * k) 3)) in
      (0 <= total <= 1)%Z.
Admitted.
