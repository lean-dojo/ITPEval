(* Statement-only formalization of VERINA corpus artifact verina_basic_23,
   catalog title "differenceMinMax": an executable scan of a nonempty integer
   array returns the difference between its maximum and minimum, together with
   its fold-based postcondition and final correctness proposition. This file
   contains no proof. *)

From Stdlib Require Import Lists.List ZArith.

Import ListNotations.
Open Scope Z_scope.

Definition differenceMinMax_precond (a : list Z) : Prop :=
  (0 < length a)%nat.

Definition differenceMinMax_min_step (acc x : Z) : Z :=
  if Z.ltb x acc then x else acc.

Definition differenceMinMax_max_step (acc x : Z) : Z :=
  if Z.ltb acc x then x else acc.

Fixpoint differenceMinMax_loop
    (remaining : list Z)
    (minVal maxVal : Z) : Z :=
  match remaining with
  | [] => maxVal - minVal
  | x :: xs =>
      let newMin := differenceMinMax_min_step minVal x in
      let newMax := differenceMinMax_max_step maxVal x in
      differenceMinMax_loop xs newMin newMax
  end.

Definition differenceMinMax
    (a : list Z)
    (_h_precond : differenceMinMax_precond a) : Z :=
  match a with
  | [] => 0%Z
  | x :: xs => differenceMinMax_loop xs x x
  end.

Definition differenceMinMax_postcond
    (a : list Z)
    (result : Z)
    (_h_precond : differenceMinMax_precond a) : Prop :=
  result +
    fold_left differenceMinMax_min_step a (hd 0%Z a) =
  fold_left differenceMinMax_max_step a (hd 0%Z a).

Theorem differenceMinMax_spec_satisfied
    (a : list Z)
    (h_precond : differenceMinMax_precond a) :
  differenceMinMax_postcond
    a (differenceMinMax a h_precond) h_precond.
Admitted.
