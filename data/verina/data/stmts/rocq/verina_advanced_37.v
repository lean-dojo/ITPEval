(* Statement-only formalization of VERINA corpus artifact verina_advanced_37,
   catalog title "majorityElement": insertion-sort computation of the middle
   integer in a nonempty list guaranteed to have a strict majority element,
   together with its majority and uniqueness contract. This file contains no
   proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List ZArith.

Import ListNotations.

Definition majorityElement_count (x : Z) (nums : list Z) : nat :=
  count_occ Z.eq_dec nums x.

Definition majorityElement_precond (nums : list Z) : Prop :=
  Nat.lt 0 (length nums) /\
  existsb
    (fun x =>
      Nat.ltb
        (Nat.div (length nums) 2)
        (majorityElement_count x nums))
    nums = true.

Fixpoint majorityElement_insert
    (x : Z) (xs : list Z) : list Z :=
  match xs with
  | [] => [x]
  | h :: t =>
      if Z.leb x h
      then x :: h :: t
      else h :: majorityElement_insert x t
  end.

Fixpoint majorityElement_insertionSort
    (xs : list Z) : list Z :=
  match xs with
  | [] => []
  | h :: t =>
      let sortedTail := majorityElement_insertionSort t in
      let sorted := majorityElement_insert h sortedTail in
      sorted
  end.

Definition majorityElement_getAt
    (xs : list Z) (i : nat) : Z :=
  match skipn i xs with
  | [] => 0%Z
  | h :: _ => h
  end.

Definition majorityElement
    (nums : list Z)
    (_h_precond : majorityElement_precond nums) : Z :=
  let sorted := majorityElement_insertionSort nums in
  let len := length sorted in
  let mid := Nat.div len 2 in
  majorityElement_getAt sorted mid.

Definition majorityElement_postcond
    (nums : list Z)
    (result : Z)
    (_h_precond : majorityElement_precond nums) : Prop :=
  let n := length nums in
  Nat.lt
    (Nat.div n 2)
    (majorityElement_count result nums) /\
  forallb
    (fun x =>
      orb
        (Z.eqb x result)
        (Nat.leb
          (majorityElement_count x nums)
          (Nat.div n 2)))
    nums = true.

Theorem majorityElement_spec_satisfied
    (nums : list Z)
    (h_precond : majorityElement_precond nums) :
  majorityElement_postcond
    nums (majorityElement nums h_precond) h_precond.
Admitted.
