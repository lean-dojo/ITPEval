(* Statement-only formalization of VERINA corpus artifact verina_advanced_44,
   catalog title "maxSubarraySumDivisibleByK": executable prefix-sum
   enumeration of contiguous integer subarrays whose lengths are divisible by
   an integer k, together with the declared positive-k precondition and the
   maximum-sum correctness contract. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List ZArith.

Import ListNotations.

Definition maxSubarraySumDivisibleByK_precond
    (_arr : list Z)
    (k : Z) : Prop :=
  (0 < k)%Z.

Fixpoint maxSubarraySumDivisibleByK_prefixSumsFrom
    (accumulator : Z)
    (arr : list Z) : list Z :=
  match arr with
  | [] => [accumulator]
  | x :: remaining =>
      accumulator ::
        maxSubarraySumDivisibleByK_prefixSumsFrom
          (accumulator + x)%Z remaining
  end.

Definition maxSubarraySumDivisibleByK_prefixSums
    (arr : list Z) : list Z :=
  maxSubarraySumDivisibleByK_prefixSumsFrom 0%Z arr.

Definition maxSubarraySumDivisibleByK_validLength
    (len : nat)
    (k : Z) : bool :=
  andb
    (Z.eqb (Z.rem (Z.of_nat len) k) 0%Z)
    (Nat.ltb 0 len).

Definition maxSubarraySumDivisibleByK_sumsForLength
    (prefixSums : list Z)
    (n len : nat) : list Z :=
  map
    (fun start =>
      (nth (Nat.add start len) prefixSums 0%Z -
       nth start prefixSums 0%Z)%Z)
    (seq 0 (Nat.add (Nat.sub n len) 1)).

Definition maxSubarraySumDivisibleByK_candidateSums
    (arr : list Z)
    (k : Z) : list Z :=
  let n := length arr in
  let prefixSums := maxSubarraySumDivisibleByK_prefixSums arr in
  flat_map
    (fun len =>
      if maxSubarraySumDivisibleByK_validLength len k
      then
        maxSubarraySumDivisibleByK_sumsForLength
          prefixSums n len
      else [])
    (seq 0 (S n)).

Fixpoint maxSubarraySumDivisibleByK_maxOption
    (values : list Z) : option Z :=
  match values with
  | [] => None
  | value :: remaining =>
      match maxSubarraySumDivisibleByK_maxOption remaining with
      | None => Some value
      | Some currentMaximum => Some (Z.max value currentMaximum)
      end
  end.

Definition maxSubarraySumDivisibleByK
    (arr : list Z)
    (k : Z) : Z :=
  let n := length arr in
  if orb (Nat.eqb n 0) (Z.eqb k 0%Z)
  then 0%Z
  else
    match
      maxSubarraySumDivisibleByK_maxOption
        (maxSubarraySumDivisibleByK_candidateSums arr k)
    with
    | None => 0%Z
    | Some maximum => maximum
    end.

Definition maxSubarraySumDivisibleByK_extract
    (arr : list Z)
    (start len : nat) : list Z :=
  firstn len (skipn start arr).

Definition maxSubarraySumDivisibleByK_subarrays
    (arr : list Z) : list (list Z) :=
  let n := length arr in
  flat_map
    (fun start =>
      map
        (fun len =>
          maxSubarraySumDivisibleByK_extract arr start len)
        (seq 0 (Nat.add (Nat.sub n start) 1)))
    (seq 0 n).

Definition maxSubarraySumDivisibleByK_divisibleNonempty
    (k : Z)
    (subarray : list Z) : bool :=
  andb
    (Nat.eqb
      (Nat.modulo (length subarray) (Z.to_nat k))
      0)
    (Nat.ltb 0 (length subarray)).

Fixpoint maxSubarraySumDivisibleByK_sum
    (subarray : list Z) : Z :=
  match subarray with
  | [] => 0%Z
  | x :: remaining =>
      (x + maxSubarraySumDivisibleByK_sum remaining)%Z
  end.

Definition maxSubarraySumDivisibleByK_postcond
    (arr : list Z)
    (k result : Z) : Prop :=
  let subarrays :=
    maxSubarraySumDivisibleByK_subarrays arr in
  let divisibleSubarrays :=
    filter
      (maxSubarraySumDivisibleByK_divisibleNonempty k)
      subarrays in
  let subarraySums :=
    map maxSubarraySumDivisibleByK_sum divisibleSubarrays in
  (length subarraySums = 0%nat -> result = 0%Z) /\
  ((0 < length subarraySums)%nat ->
    In result subarraySums /\
    forallb (fun sum => Z.leb sum result) subarraySums = true).

Theorem maxSubarraySumDivisibleByK_spec_satisfied
    (arr : list Z)
    (k : Z) :
  maxSubarraySumDivisibleByK_postcond
    arr k (maxSubarraySumDivisibleByK arr k).
Admitted.
