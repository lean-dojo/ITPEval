(* Statement-only formalization of VERINA corpus artifact verina_advanced_46,
   catalog title "maxSubarraySum": an executable Kadane-style scan over
   integer lists, including its all-negative and integer-to-natural conversion
   behavior, together with the exhaustive contiguous-subarray maximum
   correctness contract. This file contains no proof. *)

From Stdlib Require Import Bool.Bool Lists.List ZArith.

Import ListNotations.

Definition maxSubarraySum_precond
    (_numbers : list Z) : Prop :=
  True.

Fixpoint maxSubarraySum_isAllNegative
    (numbers : list Z) : bool :=
  match numbers with
  | [] => true
  | x :: xs =>
      if Z.geb x 0%Z
      then false
      else maxSubarraySum_isAllNegative xs
  end.

Fixpoint maxSubarraySum_findMaxProduct
    (numbers : list Z)
    (currMax currSum : Z) {struct numbers} : Z :=
  match numbers with
  | [] => currMax
  | [x] => Z.max currMax x
  | x :: (y :: rest as tail) =>
      let newSum := Z.max y (currSum + y)%Z in
      let newMax := Z.max currMax newSum in
      maxSubarraySum_findMaxProduct tail newMax newSum
  end.

Definition maxSubarraySum_handleList
    (numbers : list Z) : nat :=
  match maxSubarraySum_isAllNegative numbers with
  | true => 0
  | false =>
      match numbers with
      | [] => 0
      | x :: rest =>
          let initialMax := Z.max 0%Z x in
          let startSum := Z.max 0%Z x in
          let result :=
            maxSubarraySum_findMaxProduct
              (x :: rest) initialMax startSum in
          Z.to_nat result
      end
  end.

Definition maxSubarraySum
    (numbers : list Z)
    (_h_precond : maxSubarraySum_precond numbers) : Z :=
  Z.of_nat (maxSubarraySum_handleList numbers).

Fixpoint maxSubarraySum_sum
    (numbers : list Z) : Z :=
  match numbers with
  | [] => 0%Z
  | x :: xs => (x + maxSubarraySum_sum xs)%Z
  end.

Definition maxSubarraySum_subArraySums
    (numbers : list Z) : list Z :=
  flat_map
    (fun start =>
      map
        (fun len =>
          maxSubarraySum_sum
            (firstn len (skipn start numbers)))
        (seq 0 (Nat.add (Nat.sub (length numbers) start) 1)))
    (seq 0 (Nat.add (length numbers) 1)).

Definition maxSubarraySum_postcond
    (numbers : list Z)
    (result : Z)
    (_h_precond : maxSubarraySum_precond numbers) : Prop :=
  let subArraySums := maxSubarraySum_subArraySums numbers in
  existsb (fun sum => Z.eqb sum result) subArraySums = true /\
  forallb (fun sum => Z.leb sum result) subArraySums = true.

Theorem maxSubarraySum_spec_satisfied
    (numbers : list Z)
    (h_precond : maxSubarraySum_precond numbers) :
  maxSubarraySum_postcond
    numbers (maxSubarraySum numbers h_precond) h_precond.
Admitted.
