(* Statement-only formalization of PutnamBench artifact putnam_1987_a2:
   the decimal-length block containing the 10^1987-th digit in the
   concatenation of the positive integers. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Lists.List.

Fixpoint putnam_1987_a2_decimal_digits_fuel
    (fuel n : nat) : list nat :=
  match fuel with
  | O => nil
  | S fuel' =>
      if Nat.ltb n 10
      then n :: nil
      else
        Nat.modulo n 10
          :: putnam_1987_a2_decimal_digits_fuel fuel' (Nat.div n 10)
  end.

Definition putnam_1987_a2_num_digits (n : nat) : nat :=
  length (putnam_1987_a2_decimal_digits_fuel (S n) n).

Definition putnam_1987_a2_solution : nat := 1984.

Theorem putnam_1987_a2
    (seqind seqsize f : nat -> nat)
    (hseqind :
      seqind 1 = 1 /\
      forall i : nat,
        (2 <= i)%nat ->
        seqind i =
          seqind (i - 1) + putnam_1987_a2_num_digits (i - 1))
    (hseqsize :
      forall i : nat,
        (1 <= i)%nat ->
        forall j : nat,
          (j < putnam_1987_a2_num_digits i)%nat ->
          seqsize (seqind i + j) = putnam_1987_a2_num_digits i)
    (hf :
      forall n : nat,
        f n = seqsize (10 ^ n)) :
  f 1987 = putnam_1987_a2_solution.
Admitted.
