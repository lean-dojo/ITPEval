(* Statement-only formalization of VERINA corpus artifact verina_basic_72,
   catalog title "append": executable copying of an arbitrary integer array
   followed by appending one integer, together with its precondition,
   pointwise-and-size postcondition, and final correctness proposition. This
   file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Lists.List ZArith.

Import ListNotations.

Definition append_precond (_a : list Z) (_b : Z) : Prop :=
  True.

Fixpoint copy_loop
    (fuel : nat)
    (a : list Z)
    (i : nat)
    (acc : list Z) : list Z :=
  match fuel with
  | O => acc
  | S fuel' =>
      if Nat.ltb i (length a)
      then
        copy_loop
          fuel' a (S i) (acc ++ [nth i a 0%Z])
      else acc
  end.

Definition copy
    (a : list Z)
    (i : nat)
    (acc : list Z) : list Z :=
  copy_loop (length a) a i acc.

Definition append
    (a : list Z)
    (b : Z)
    (_h_precond : append_precond a b) : list Z :=
  let c_initial := copy a O [] in
  let c_full := c_initial ++ [b] in
  c_full.

Definition append_postcond
    (a : list Z)
    (b : Z)
    (result : list Z)
    (_h_precond : append_precond a b) : Prop :=
  (forall i : nat,
      (i < length a)%nat ->
      nth i result 0%Z = nth i a 0%Z) /\
  nth (length a) result 0%Z = b /\
  length result = (length a + 1)%nat.

Theorem append_spec_satisfied
    (a : list Z)
    (b : Z)
    (h_precond : append_precond a b) :
  append_postcond
    a b (append a b h_precond) h_precond.
Admitted.
