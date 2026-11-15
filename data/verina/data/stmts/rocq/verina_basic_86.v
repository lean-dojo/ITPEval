(* Statement-only formalization of VERINA corpus artifact verina_basic_86,
   catalog title "rotate": executable left rotation of an arbitrary integer
   array by a nonnegative offset, together with its precondition, size-and-
   index postcondition, and final correctness proposition. This file contains
   no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List ZArith.

Import ListNotations.

Module VerinaBasic86.

Definition rotate_precond
    (_a : list Z)
    (offset : Z) : Prop :=
  (offset >= 0)%Z.

Fixpoint rotate_set_nth
    (index : nat)
    (value : Z)
    (xs : list Z) : list Z :=
  match xs with
  | [] => []
  | x :: rest =>
      match index with
      | O => value :: rest
      | S index' => x :: rotate_set_nth index' value rest
      end
  end.

Fixpoint rotateAux_fuel
    (fuel : nat)
    (a : list Z)
    (offset : Z)
    (i len : nat)
    (b : list Z) : list Z :=
  match fuel with
  | O => b
  | S fuel' =>
      if Nat.ltb i len then
        let idx_int :=
          Z.modulo (Z.of_nat i + offset) (Z.of_nat len) in
        let idx_int_adjusted :=
          if Z.ltb idx_int 0
          then (idx_int + Z.of_nat len)%Z
          else idx_int in
        let idx_nat := Z.to_nat idx_int_adjusted in
        let new_b :=
          rotate_set_nth i (nth idx_nat a 0%Z) b in
        rotateAux_fuel
          fuel' a offset (S i) len new_b
      else b
  end.

Definition rotateAux
    (a : list Z)
    (offset : Z)
    (i len : nat)
    (b : list Z) : list Z :=
  rotateAux_fuel (len - i)%nat a offset i len b.

Definition rotate
    (a : list Z)
    (offset : Z)
    (_h_precond : rotate_precond a offset) : list Z :=
  let len := length a in
  let default_val :=
    if Nat.ltb 0 len then nth 0 a 0%Z else 0%Z in
  let b0 := repeat default_val len in
  rotateAux a offset 0%nat len b0.

Definition rotate_postcond
    (a : list Z)
    (offset : Z)
    (result : list Z)
    (_h_precond : rotate_precond a offset) : Prop :=
  length result = length a /\
  forall i : nat,
    (i < length a)%nat ->
    nth i result 0%Z =
      nth
        (Z.to_nat
          (Z.modulo
            (Z.of_nat i + offset)
            (Z.of_nat (length a))))
        a
        0%Z.

Theorem rotate_spec_satisfied
    (a : list Z)
    (offset : Z)
    (h_precond : rotate_precond a offset) :
  rotate_postcond
    a offset (rotate a offset h_precond) h_precond.
Admitted.

End VerinaBasic86.
