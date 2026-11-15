(* Statement-only formalization of VERINA corpus artifact verina_basic_58,
   catalog title "double_array_elements": executable in-place doubling of
   every element of an integer array, together with its trivial precondition,
   pointwise postcondition, and final correctness proposition. This file
   contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List ZArith.

Import ListNotations.

Definition double_array_elements_precond
    (_s : list Z) : Prop :=
  True.

Fixpoint double_array_elements_set_nth
    (index : nat)
    (value : Z)
    (xs : list Z) : list Z :=
  match xs with
  | [] => []
  | x :: rest =>
      match index with
      | O => value :: rest
      | S index' =>
          x :: double_array_elements_set_nth index' value rest
      end
  end.

Fixpoint double_array_elements_aux_fuel
    (fuel : nat)
    (s_old s : list Z)
    (i : nat) : list Z :=
  match fuel with
  | O => s
  | S fuel' =>
      if Nat.ltb i (length s) then
        let new_s :=
          double_array_elements_set_nth
            i (2 * nth i s_old 0)%Z s in
        double_array_elements_aux_fuel
          fuel' s_old new_s (S i)
      else s
  end.

Definition double_array_elements_aux
    (s_old s : list Z)
    (i : nat) : list Z :=
  double_array_elements_aux_fuel
    (Nat.sub (length s) i) s_old s i.

Definition double_array_elements
    (s : list Z)
    (_h_precond : double_array_elements_precond s) : list Z :=
  double_array_elements_aux s s O.

Definition double_array_elements_postcond
    (s result : list Z)
    (_h_precond : double_array_elements_precond s) : Prop :=
  length result = length s /\
  forall i : nat,
    (i < length s)%nat ->
    nth i result 0%Z = (2 * nth i s 0)%Z.

Theorem double_array_elements_spec_satisfied
    (s : list Z)
    (h_precond : double_array_elements_precond s) :
  double_array_elements_postcond
    s (double_array_elements s h_precond) h_precond.
Admitted.
