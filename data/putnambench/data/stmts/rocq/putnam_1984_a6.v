(* Statement-only formalization of PutnamBench corpus artifact putnam_1984_a6:
   the last nonzero decimal digit of a factorial at sums of distinct powers
   of five depends only on the exponent sum, and the induced function has
   least positive period four from index one. This file contains no proof. *)

From Stdlib Require Import Arith.

Fixpoint putnam_1984_a6_factorial (n : nat) : nat :=
  match n with
  | O => 1
  | S k => S k * putnam_1984_a6_factorial k
  end.

Fixpoint putnam_1984_a6_power (base exponent : nat) : nat :=
  match exponent with
  | O => 1
  | S k => base * putnam_1984_a6_power base k
  end.

Fixpoint putnam_1984_a6_sum_first
    (terms : nat -> nat) (count : nat) : nat :=
  match count with
  | O => 0
  | S k => putnam_1984_a6_sum_first terms k + terms k
  end.

Definition putnam_1984_a6_injective_below
    (values : nat -> nat) (count : nat) : Prop :=
  forall i j : nat,
    i < count ->
    j < count ->
    values i = values j ->
    i = j.

Definition putnam_1984_a6_last_nonzero_factorial_digit
    (n digit : nat) : Prop :=
  exists trailing_zeros core : nat,
    putnam_1984_a6_factorial n =
      putnam_1984_a6_power 10 trailing_zeros * core /\
    core mod 10 <> 0 /\
    digit = core mod 10.

Definition putnam_1984_a6_periodic_from
    (start : nat) (values : nat -> nat) (period : nat) : Prop :=
  forall index : nat,
    start <= index ->
    values index = values (index + period).

Definition putnam_1984_a6_least_positive_period_from
    (start : nat) (values : nat -> nat) (period : nat) : Prop :=
  0 < period /\
  putnam_1984_a6_periodic_from start values period /\
  forall other_period : nat,
    0 < other_period ->
    putnam_1984_a6_periodic_from start values other_period ->
    period <= other_period.

Definition putnam_1984_a6_depends_only_on_exponent_sum
    (factorial_digit values : nat -> nat) : Prop :=
  forall (count : nat) (exponents : nat -> nat),
    0 < count ->
    putnam_1984_a6_injective_below exponents count ->
    factorial_digit
      (putnam_1984_a6_sum_first
        (fun i : nat => putnam_1984_a6_power 5 (exponents i))
        count) =
    values (putnam_1984_a6_sum_first exponents count).

Definition putnam_1984_a6_solution : nat := 4.

Theorem putnam_1984_a6 :
  forall factorial_digit : nat -> nat,
    (forall n : nat,
      putnam_1984_a6_last_nonzero_factorial_digit
        n (factorial_digit n)) ->
    exists values : nat -> nat,
      putnam_1984_a6_depends_only_on_exponent_sum
        factorial_digit values /\
      putnam_1984_a6_least_positive_period_from
        1 values putnam_1984_a6_solution.
Admitted.
