(* Statement-only formalization of VERINA corpus artifact verina_basic_35,
   catalog title "MoveZeroesToEnd": an executable stable partition of an
   integer array into its nonzero entries followed by its zero entries,
   together with the permutation and exact prefix/suffix correctness
   contract. This file contains no proof. *)

From Stdlib Require Import Bool.Bool Lists.List Sorting.Permutation ZArith.

Import ListNotations.

Definition MoveZeroesToEnd_precond (_arr : list Z) : Prop :=
  True.

Definition MoveZeroesToEnd_isNonzero (x : Z) : bool :=
  negb (Z.eqb x 0%Z).

Definition MoveZeroesToEnd_isZero (x : Z) : bool :=
  Z.eqb x 0%Z.

Definition MoveZeroesToEnd
    (arr : list Z)
    (_h_precond : MoveZeroesToEnd_precond arr) : list Z :=
  filter MoveZeroesToEnd_isNonzero arr ++
  filter MoveZeroesToEnd_isZero arr.

Fixpoint MoveZeroesToEnd_idxOfZero (xs : list Z) : nat :=
  match xs with
  | [] => 0%nat
  | x :: rest =>
      if Z.eqb x 0%Z
      then 0%nat
      else S (MoveZeroesToEnd_idxOfZero rest)
  end.

Definition MoveZeroesToEnd_postcond
    (arr result : list Z)
    (_h_precond : MoveZeroesToEnd_precond arr) : Prop :=
  let firstResZeroIdx := MoveZeroesToEnd_idxOfZero result in
  Permutation result arr /\
  firstn firstResZeroIdx result =
    filter MoveZeroesToEnd_isNonzero arr /\
  skipn firstResZeroIdx result =
    filter MoveZeroesToEnd_isZero arr.

Theorem MoveZeroesToEnd_spec_satisfied
    (arr : list Z)
    (h_precond : MoveZeroesToEnd_precond arr) :
  MoveZeroesToEnd_postcond
    arr (MoveZeroesToEnd arr h_precond) h_precond.
Admitted.
