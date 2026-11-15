(* Statement-only formalization of VERINA corpus artifact verina_advanced_57,
   catalog title "nextGreaterElement": an executable monotonic-stack
   computation of the first greater integer to the right for each requested
   distinct value, together with its correctness contract. This file contains
   no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List ZArith.

Import ListNotations.

Definition nextGreaterElement_precond
    (nums1 nums2 : list Z) : Prop :=
  NoDup nums1 /\
  NoDup nums2 /\
  forallb
    (fun x => existsb (Z.eqb x) nums2)
    nums1 = true.

Definition nextGreaterElement_nth
    (xs : list Z)
    (index : nat) : Z :=
  nth index xs 0%Z.

Definition nextGreaterElement_map := list (Z * Z).

Fixpoint nextGreaterElement_processStack
    (nums2 : list Z)
    (currentValue : Z)
    (stack : list nat)
    (entries : nextGreaterElement_map)
    {struct stack}
    : list nat * nextGreaterElement_map :=
  match stack with
  | [] => ([], entries)
  | topIndex :: rest =>
      let topValue := nextGreaterElement_nth nums2 topIndex in
      if Z.gtb currentValue topValue
      then
        nextGreaterElement_processStack
          nums2 currentValue rest
          ((topValue, currentValue) :: entries)
      else (stack, entries)
  end.

Fixpoint nextGreaterElement_mapLoop
    (nums2 remaining : list Z)
    (index : nat)
    (stack : list nat)
    (entries : nextGreaterElement_map)
    {struct remaining}
    : nextGreaterElement_map :=
  match remaining with
  | [] =>
      fold_left
        (fun acc pos =>
          (nextGreaterElement_nth nums2 pos, (-1)%Z) :: acc)
        stack entries
  | currentValue :: rest =>
      let '(newStack, newEntries) :=
        nextGreaterElement_processStack
          nums2 currentValue stack entries in
      nextGreaterElement_mapLoop
        nums2 rest (S index) (index :: newStack) newEntries
  end.

Definition nextGreaterElement_buildNextGreaterMap
    (nums2 : list Z) : nextGreaterElement_map :=
  nextGreaterElement_mapLoop nums2 nums2 0%nat [] [].

Fixpoint nextGreaterElement_findInMap
    (value : Z)
    (entries : nextGreaterElement_map) : Z :=
  match entries with
  | [] => (-1)%Z
  | (num, nextGreater) :: rest =>
      if Z.eqb num value
      then nextGreater
      else nextGreaterElement_findInMap value rest
  end.

Fixpoint nextGreaterElement_resultLoop
    (remaining : list Z)
    (entries : nextGreaterElement_map)
    (result : list Z)
    {struct remaining}
    : list Z :=
  match remaining with
  | [] => rev result
  | value :: rest =>
      let nextGreater :=
        nextGreaterElement_findInMap value entries in
      nextGreaterElement_resultLoop
        rest entries (nextGreater :: result)
  end.

Definition nextGreaterElement
    (nums1 nums2 : list Z)
    (_h_precond : nextGreaterElement_precond nums1 nums2)
    : list Z :=
  let entries :=
    nextGreaterElement_buildNextGreaterMap nums2 in
  nextGreaterElement_resultLoop nums1 entries [].

Fixpoint nextGreaterElement_findIdxFrom
    (value : Z)
    (xs : list Z)
    (index : nat) : option nat :=
  match xs with
  | [] => None
  | x :: rest =>
      if Z.eqb x value
      then Some index
      else nextGreaterElement_findIdxFrom value rest (S index)
  end.

Definition nextGreaterElement_findIdx
    (value : Z)
    (xs : list Z) : option nat :=
  nextGreaterElement_findIdxFrom value xs 0%nat.

Fixpoint nextGreaterElement_findOffset
    (nums2 : list Z)
    (value : Z)
    (offsets : list nat) : option nat :=
  match offsets with
  | [] => None
  | offset :: rest =>
      match nextGreaterElement_findIdx value nums2 with
      | None => None
      | Some index =>
          let position := index + offset + 1 in
          if Z.gtb
               (nextGreaterElement_nth nums2 position)
               value
          then Some offset
          else
            nextGreaterElement_findOffset nums2 value rest
      end
  end.

Definition nextGreaterElement_indexCorrect
    (nums2 : list Z)
    (value resultValue : Z) : bool :=
  match nextGreaterElement_findIdx value nums2 with
  | None => false
  | Some index =>
      let offsets :=
        seq 0%nat (length nums2 - index - 1) in
      match
        nextGreaterElement_findOffset nums2 value offsets
      with
      | None => Z.eqb resultValue (-1)%Z
      | Some offset =>
          Z.eqb
            resultValue
            (nextGreaterElement_nth
              nums2 (index + offset + 1))
      end
  end.

Definition nextGreaterElement_postcond
    (nums1 nums2 result : list Z)
    (_h_precond : nextGreaterElement_precond nums1 nums2)
    : Prop :=
  length result = length nums1 /\
  forallb
    (fun index =>
      let value := nextGreaterElement_nth nums1 index in
      let resultValue :=
        nextGreaterElement_nth result index in
      nextGreaterElement_indexCorrect
        nums2 value resultValue)
    (seq 0%nat (length nums1)) = true /\
  forallb
    (fun value =>
      orb
        (Z.eqb value (-1)%Z)
        (existsb (Z.eqb value) nums2))
    result = true.

Theorem nextGreaterElement_spec_satisfied
    (nums1 nums2 : list Z)
    (h_precond : nextGreaterElement_precond nums1 nums2) :
  nextGreaterElement_postcond
    nums1 nums2
    (nextGreaterElement nums1 nums2 h_precond)
    h_precond.
Admitted.
