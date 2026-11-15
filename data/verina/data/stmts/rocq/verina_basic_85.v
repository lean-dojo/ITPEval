(* Statement-only formalization of VERINA corpus artifact verina_basic_85,
   catalog title "reverse": executable reversal of an arbitrary integer array
   by swapping symmetric entries up to half its length, together with its
   unconditional precondition, pointwise-and-size postcondition, and final
   correctness proposition. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List ZArith.

Import ListNotations.

Definition reverse_precond (_a : list Z) : Prop :=
  True.

Fixpoint reverse_set_nth
    (index : nat)
    (value : Z)
    (arr : list Z) : list Z :=
  match arr with
  | [] => []
  | x :: rest =>
      match index with
      | O => value :: rest
      | S index' => x :: reverse_set_nth index' value rest
      end
  end.

Fixpoint reverse_core_fuel
    (fuel : nat)
    (arr : list Z)
    (i : nat) : list Z :=
  match fuel with
  | O => arr
  | S fuel' =>
      if Nat.ltb i (length arr / 2)%nat then
        let j := (length arr - 1 - i)%nat in
        let temp := nth i arr 0%Z in
        let arr' :=
          reverse_set_nth i (nth j arr 0%Z) arr in
        let arr'' := reverse_set_nth j temp arr' in
        reverse_core_fuel fuel' arr'' (S i)
      else arr
  end.

Definition reverse_core
    (arr : list Z)
    (i : nat) : list Z :=
  reverse_core_fuel
    ((length arr / 2) - i)%nat arr i.

Definition reverse
    (a : list Z)
    (_h_precond : reverse_precond a) : list Z :=
  reverse_core a O.

Definition reverse_postcond
    (a result : list Z)
    (_h_precond : reverse_precond a) : Prop :=
  length result = length a /\
  forall i : nat,
    (i < length a)%nat ->
    nth i result 0%Z =
    nth (length a - 1 - i)%nat a 0%Z.

Theorem reverse_spec_satisfied
    (a : list Z)
    (h_precond : reverse_precond a) :
  reverse_postcond
    a (reverse a h_precond) h_precond.
Admitted.
