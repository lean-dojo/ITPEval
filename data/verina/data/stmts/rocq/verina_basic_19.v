(* Statement-only formalization of VERINA corpus artifact verina_basic_19,
   catalog title "isSorted": an executable Boolean check that every adjacent
   pair in an integer array is nondecreasing, together with its trivial
   precondition, exact Boolean postcondition, and final correctness
   proposition. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List ZArith.

Import ListNotations.
Open Scope Z_scope.

Definition isSorted_precond (_a : list Z) : Prop :=
  True.

Fixpoint isSorted_scan
    (previous : Z)
    (rest : list Z) : bool :=
  match rest with
  | [] => true
  | current :: tail =>
      if Z.leb previous current
      then isSorted_scan current tail
      else false
  end.

Definition isSorted
    (a : list Z)
    (_h_precond : isSorted_precond a) : bool :=
  if Nat.leb (length a) 1%nat
  then true
  else
    match a with
    | [] => true
    | first :: rest => isSorted_scan first rest
    end.

Definition isSorted_postcond
    (a : list Z)
    (result : bool)
    (_h_precond : isSorted_precond a) : Prop :=
  (forall i : nat,
      (i < length a - 1)%nat ->
      nth i a 0%Z <= nth (S i) a 0%Z) <->
  result = true.

Theorem isSorted_spec_satisfied
    (a : list Z)
    (h_precond : isSorted_precond a) :
  isSorted_postcond a (isSorted a h_precond) h_precond.
Admitted.
