(* Statement-only formalization of VERINA corpus artifact verina_basic_94,
   catalog title "iter_copy": an executable left-to-right copy of an
   arbitrary integer array into a fresh array, together with its
   unconditional precondition, length-and-pointwise postcondition, and final
   correctness proposition. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List ZArith.

Import ListNotations.

Module VerinaBasic94.

Definition iter_copy_get_option
    (s : list Z)
    (i : nat) : option Z :=
  nth_error s i.

Definition iter_copy_get_bang
    (s : list Z)
    (i : nat) : Z :=
  nth i s 0%Z.

Definition iter_copy_precond
    (_s : list Z) : Prop :=
  True.

Fixpoint iter_copy_loop_fuel
    (fuel : nat)
    (s : list Z)
    (i : nat)
    (acc : list Z) : list Z :=
  match fuel with
  | O => acc
  | S fuel' =>
      if Nat.ltb i (length s)
      then
        match iter_copy_get_option s i with
        | Some value =>
            iter_copy_loop_fuel
              fuel' s (S i) (acc ++ [value])
        | None => acc
        end
      else acc
  end.

Definition iter_copy_loop
    (s : list Z)
    (i : nat)
    (acc : list Z) : list Z :=
  iter_copy_loop_fuel
    (S (length s - i)) s i acc.

Definition iter_copy
    (s : list Z)
    (_h_precond : iter_copy_precond s) : list Z :=
  iter_copy_loop s O [].

Definition iter_copy_postcond
    (s result : list Z)
    (_h_precond : iter_copy_precond s) : Prop :=
  length s = length result /\
  forall i : nat,
    (i < length s)%nat ->
    iter_copy_get_bang s i =
      iter_copy_get_bang result i.

Theorem iter_copy_spec_satisfied
    (s : list Z)
    (h_precond : iter_copy_precond s) :
  iter_copy_postcond
    s (iter_copy s h_precond) h_precond.
Admitted.

End VerinaBasic94.
