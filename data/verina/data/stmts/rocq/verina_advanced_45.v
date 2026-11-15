(* Statement-only formalization of VERINA corpus artifact verina_advanced_45,
   catalog title "maxSubarraySum": an executable Kadane scan computing the
   maximum sum of a nonempty contiguous integer subarray, with zero for the
   empty list, together with its exact subarray-enumeration correctness
   contract. This file contains no proof. *)

From Stdlib Require Import Bool.Bool Lists.List ZArith.

Import ListNotations.

Definition maxSubarraySum_precond (_xs : list Z) : Prop :=
  True.

Fixpoint maxSubarraySum_helper
    (lst : list Z)
    (curMax globalMax : Z) : Z :=
  match lst with
  | [] => globalMax
  | x :: rest =>
      let newCurMax := Z.max x (curMax + x)%Z in
      let newGlobal := Z.max globalMax newCurMax in
      maxSubarraySum_helper rest newCurMax newGlobal
  end.

Definition maxSubarraySum
    (xs : list Z)
    (_h_precond : maxSubarraySum_precond xs) : Z :=
  match xs with
  | [] => 0%Z
  | x :: rest => maxSubarraySum_helper rest x x
  end.

Fixpoint maxSubarraySum_sum (xs : list Z) : Z :=
  match xs with
  | [] => 0%Z
  | x :: rest => (x + maxSubarraySum_sum rest)%Z
  end.

Definition maxSubarraySum_subarraySums
    (xs : list Z) : list Z :=
  flat_map
    (fun start =>
      map
        (fun len =>
          maxSubarraySum_sum
            (firstn len (skipn start xs)))
        (seq 1 (length xs - start)))
    (seq 0 (S (length xs))).

Definition maxSubarraySum_postcond
    (xs : list Z)
    (result : Z)
    (_h_precond : maxSubarraySum_precond xs) : Prop :=
  let subarray_sums := maxSubarraySum_subarraySums xs in
  let has_result_subarray :=
    existsb (fun sum => Z.eqb sum result) subarray_sums in
  let is_maximum :=
    forallb (fun sum => Z.leb sum result) subarray_sums in
  match xs with
  | [] => Z.eqb result 0%Z = true
  | _ :: _ =>
      has_result_subarray = true /\
      is_maximum = true
  end.

Theorem maxSubarraySum_spec_satisfied
    (xs : list Z)
    (h_precond : maxSubarraySum_precond xs) :
  maxSubarraySum_postcond
    xs (maxSubarraySum xs h_precond) h_precond.
Admitted.
