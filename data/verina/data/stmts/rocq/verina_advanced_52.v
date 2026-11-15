(* Statement-only formalization of VERINA corpus artifact verina_advanced_52,
   catalog title "minOperations": an executable reverse-list scan computing
   the minimum number of removals needed to collect every natural number from
   1 through k, together with its correctness contract. This file contains no
   proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List.

Import ListNotations.

Definition minOperations_targets (k : nat) : list nat :=
  map S (seq 0 k).

Definition minOperations_contains
    (n : nat)
    (xs : list nat) : bool :=
  existsb (Nat.eqb n) xs.

Definition minOperations_precond
    (nums : list nat)
    (k : nat) : Prop :=
  forallb
    (fun n => minOperations_contains n nums)
    (minOperations_targets k) = true.

Fixpoint minOperations_loop
    (k : nat)
    (remaining collected : list nat)
    (collected_count ops : nat) : nat :=
  match remaining with
  | [] => ops
  | head :: tail =>
      let ops' := S ops in
      if andb
          (andb (Nat.ltb 0 head) (Nat.leb head k))
          (negb (minOperations_contains head collected))
      then
        let collected' := head :: collected in
        let collected_count' := S collected_count in
        if Nat.eqb collected_count' k
        then ops'
        else
          minOperations_loop
            k tail collected' collected_count' ops'
      else
        minOperations_loop
          k tail collected collected_count ops'
  end.

Definition minOperations
    (nums : list nat)
    (k : nat)
    (_h_precond : minOperations_precond nums k) : nat :=
  if Nat.eqb k 0
  then 0
  else minOperations_loop k (rev nums) [] 0 0.

Definition minOperations_postcond
    (nums : list nat)
    (k result : nat)
    (_h_precond : minOperations_precond nums k) : Prop :=
  let processed := firstn result (rev nums) in
  let target_nums := minOperations_targets k in
  let collected_all :=
    forallb
      (fun n => minOperations_contains n processed)
      target_nums = true in
  let is_minimal :=
    if Nat.ltb 0 result
    then
      let processed_minus_one :=
        firstn (Nat.sub result 1) (rev nums) in
      forallb
        (fun n => minOperations_contains n processed_minus_one)
        target_nums <> true
    else Nat.eqb k 0 = true in
  collected_all /\ is_minimal.

Theorem minOperations_spec_satisfied
    (nums : list nat)
    (k : nat)
    (h_precond : minOperations_precond nums k) :
  minOperations_postcond
    nums k
    (minOperations nums k h_precond)
    h_precond.
Admitted.
