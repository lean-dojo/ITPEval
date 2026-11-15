(* Statement-only formalization of VERINA corpus artifact verina_advanced_74,
   catalog title "solution": executable summation over all contiguous
   subarrays of the squared number of distinct natural values, together with
   the bounded-input precondition and exact result contract. This file
   contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List.

Import ListNotations.

Definition solution_precond (nums : list nat) : Prop :=
  1 <= length nums /\
  length nums <= 100 /\
  forallb
    (fun x => andb (Nat.leb 1 x) (Nat.leb x 100))
    nums = true.

Definition solution_subarray
    (nums : list nat)
    (i j : nat) : list nat :=
  firstn (j - i + 1) (skipn i nums).

Definition solution_insert_distinct
    (seen : list nat)
    (x : nat) : list nat :=
  if existsb (Nat.eqb x) seen
  then seen
  else x :: seen.

Definition solution_distinct_count (values : list nat) : nat :=
  length (fold_left solution_insert_distinct values []).

Definition solution (nums : list nat) : nat :=
  let n := length nums in
  fold_left
    (fun outer_sum i =>
      outer_sum +
      fold_left
        (fun inner_sum d =>
          let subarr := solution_subarray nums i (i + d) in
          let count := solution_distinct_count subarr in
          inner_sum + count * count)
        (seq 0 (n - i))
        0)
    (seq 0 n)
    0.

Definition solution_postcond
    (nums : list nat)
    (result : nat) : Prop :=
  let n := length nums in
  let expected_sum :=
    fold_left
      (fun outer_sum i =>
        let inner_sum :=
          fold_left
            (fun current_inner_sum d =>
              let j := i + d in
              let subarr := solution_subarray nums i j in
              let count := solution_distinct_count subarr in
              current_inner_sum + count * count)
            (seq 0 (n - i))
            0 in
        outer_sum + inner_sum)
      (seq 0 n)
      0 in
  solution_precond nums ->
  0 <= result /\ result = expected_sum.

Theorem solution_spec_satisfied (nums : list nat) :
  solution_postcond nums (solution nums).
Admitted.
