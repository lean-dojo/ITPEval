(* Statement-only formalization of VERINA corpus artifact verina_advanced_12,
   catalog title "firstDuplicate": an executable left-to-right list scan that
   returns the first integer encountered for a second time, together with its
   earliest-second-occurrence correctness contract. This file contains no
   proof. *)

From Stdlib Require Import Arith.PeanoNat List ZArith.

Import ListNotations.

Definition firstDuplicate_precond (lst : list Z) : Prop :=
  True.

Fixpoint firstDuplicate_helper
    (seen remaining : list Z) : option Z :=
  match remaining with
  | [] => None
  | x :: xs =>
      if existsb (fun y => Z.eqb y x) seen
      then Some x
      else firstDuplicate_helper (x :: seen) xs
  end.

Definition firstDuplicate
    (lst : list Z)
    (_h_precond : firstDuplicate_precond lst) : option Z :=
  firstDuplicate_helper [] lst.

Fixpoint firstDuplicate_idxOf
    (lst : list Z) (v : Z) : nat :=
  match lst with
  | [] => 0%nat
  | x :: xs =>
      if Z.eqb x v
      then 0%nat
      else S (firstDuplicate_idxOf xs v)
  end.

Definition secondOccIdx (lst : list Z) (v : Z) : nat :=
  let first := firstDuplicate_idxOf lst v in
  first + 1 + firstDuplicate_idxOf (skipn (first + 1) lst) v.

Definition firstDuplicate_postcond
    (lst : list Z)
    (result : option Z)
    (_h_precond : firstDuplicate_precond lst) : Prop :=
  match result with
  | None => NoDup lst
  | Some x =>
      (1 < count_occ Z.eq_dec lst x)%nat /\
      forallb
        (fun y =>
          orb
            (Nat.eqb (count_occ Z.eq_dec lst y) 1)
            (Nat.leb (secondOccIdx lst x) (secondOccIdx lst y)))
        lst = true
  end.

Theorem firstDuplicate_spec_satisfied
    (lst : list Z)
    (h_precond : firstDuplicate_precond lst) :
  firstDuplicate_postcond
    lst (firstDuplicate lst h_precond) h_precond.
Admitted.
