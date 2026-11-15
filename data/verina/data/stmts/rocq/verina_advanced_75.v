(* Statement-only formalization of VERINA corpus artifact verina_advanced_75,
   catalog title "task_code": Kadane's executable maximum contiguous-subarray
   sum for a nonempty integer sequence, with the exhaustive subarray
   postcondition and final correctness proposition. This file contains no
   proof. *)

From Stdlib Require Import Bool.Bool Lists.List ZArith.

Import ListNotations.

Definition task_code_precond (sequence : list Z) : Prop :=
  (0 < length sequence)%nat.

Definition task_code_step
    (acc : Z * Z)
    (x : Z) : Z * Z :=
  let '(cur, maxSoFar) := acc in
  let curPlusX := (cur + x)%Z in
  let newCur :=
    if Z.geb curPlusX x then curPlusX else x in
  let newMax :=
    if Z.geb maxSoFar newCur then maxSoFar else newCur in
  (newCur, newMax).

Definition task_code
    (sequence : list Z)
    (_h_precond : task_code_precond sequence) : Z :=
  match sequence with
  | [] => 0%Z
  | x :: xs =>
      snd (fold_left task_code_step xs (x, x))
  end.

Definition task_code_subarrays
    (sequence : list Z) : list (list Z) :=
  flat_map
    (fun start =>
      map
        (fun len => firstn len (skipn start sequence))
        (seq 0%nat (length sequence - start + 1)))
    (seq 0%nat (length sequence + 1)).

Definition task_code_nonempty (values : list Z) : bool :=
  match values with
  | [] => false
  | _ :: _ => true
  end.

Definition task_code_sum (values : list Z) : Z :=
  fold_right Z.add 0%Z values.

Definition task_code_subarray_sums
    (sequence : list Z) : list Z :=
  map task_code_sum
    (filter task_code_nonempty
      (task_code_subarrays sequence)).

Definition task_code_postcond
    (sequence : list Z)
    (result : Z)
    (_h_precond : task_code_precond sequence) : Prop :=
  let subArraySums := task_code_subarray_sums sequence in
  existsb (Z.eqb result) subArraySums = true /\
  forallb (fun total => Z.leb total result) subArraySums = true.

Theorem task_code_spec_satisfied
    (sequence : list Z)
    (h_precond : task_code_precond sequence) :
  task_code_postcond
    sequence (task_code sequence h_precond) h_precond.
Admitted.
