(* Statement-only formalization of PutnamBench artifact putnam_1970_a3:
   the longest run of equal nonzero terminal decimal digits of a perfect
   square, and the least square attaining it. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Lists.List.

Fixpoint decimal_digits_fuel (fuel n : nat) : list nat :=
  match fuel with
  | O => nil
  | S fuel' =>
      if Nat.ltb n 10
      then n :: nil
      else Nat.modulo n 10 :: decimal_digits_fuel fuel' (Nat.div n 10)
  end.

Definition decimal_digits (n : nat) : list nat :=
  decimal_digits_fuel (S n) n.

Definition decimal_digit (n k : nat) : nat :=
  nth k (decimal_digits n) 0.

Definition terminal_run_length (L : nat -> nat) : Prop :=
  forall n : nat,
    (0 < n)%nat ->
    (L n <= length (decimal_digits n))%nat /\
    (forall k : nat,
      (k < L n)%nat ->
      decimal_digit n k = decimal_digit n 0) /\
    (L n <> length (decimal_digits n) ->
      decimal_digit n (L n) <> decimal_digit n 0).

Definition putnam_1970_a3_solution : nat * nat := (3, 1444).

Theorem putnam_1970_a3
    (L : nat -> nat)
    (hL : terminal_run_length L) :
  (exists n : nat,
    decimal_digit (n * n) 0 <> 0 /\
    L (n * n) = fst putnam_1970_a3_solution) /\
  (forall n : nat,
    decimal_digit (n * n) 0 <> 0 ->
    (L (n * n) <= fst putnam_1970_a3_solution)%nat) /\
  (exists m : nat, m * m = snd putnam_1970_a3_solution) /\
  L (snd putnam_1970_a3_solution) = fst putnam_1970_a3_solution /\
  decimal_digit (snd putnam_1970_a3_solution) 0 <> 0 /\
  forall n : nat,
    decimal_digit (n * n) 0 <> 0 /\
    L (n * n) = fst putnam_1970_a3_solution ->
    (snd putnam_1970_a3_solution <= n * n)%nat.
Admitted.
