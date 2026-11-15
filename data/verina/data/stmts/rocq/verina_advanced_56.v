(* Statement-only formalization of VERINA corpus artifact verina_advanced_56,
   catalog title "moveZeroes": an executable stable partition of an integer
   list into its nonzero elements followed by its zero elements, together with
   its subsequence, trailing-zero, count, and length correctness contract.
   This file contains no proof. *)

From Stdlib Require Import Bool.Bool Lists.List ZArith.

Import ListNotations.

Definition moveZeroes_precond (_xs : list Z) : Prop :=
  True.

Definition moveZeroes
    (xs : list Z)
    (_h_precond : moveZeroes_precond xs) : list Z :=
  filter (fun x => negb (Z.eqb x 0%Z)) xs ++
  filter (fun x => Z.eqb x 0%Z) xs.

Fixpoint countVal
    (val : Z)
    (xs : list Z) : nat :=
  match xs with
  | [] => 0%nat
  | x :: rest =>
      let count_rest := countVal val rest in
      if Z.eqb x val then S count_rest else count_rest
  end.

Fixpoint isSubsequence
    (xs ys : list Z) {struct ys} : bool :=
  match xs, ys with
  | [], _ => true
  | _ :: _, [] => false
  | x :: xt, y :: yt =>
      if Z.eqb x y
      then isSubsequence xt yt
      else isSubsequence xs yt
  end.

Fixpoint dropWhileNonzero
    (xs : list Z) : list Z :=
  match xs with
  | [] => []
  | x :: rest =>
      if negb (Z.eqb x 0%Z)
      then dropWhileNonzero rest
      else x :: rest
  end.

Definition moveZeroes_postcond
    (xs result : list Z)
    (_h_precond : moveZeroes_precond xs) : Prop :=
  isSubsequence
    (filter (fun x => negb (Z.eqb x 0%Z)) xs)
    result = true /\
  forallb
    (fun x => Z.eqb x 0%Z)
    (dropWhileNonzero result) = true /\
  countVal 0%Z xs = countVal 0%Z result /\
  length xs = length result.

Theorem moveZeroes_spec_satisfied
    (xs : list Z)
    (h_precond : moveZeroes_precond xs) :
  moveZeroes_postcond
    xs (moveZeroes xs h_precond) h_precond.
Admitted.
