(* Statement-only formalization of VERINA corpus artifact verina_advanced_8,
   catalog title "canCompleteCircuit": an executable greedy scan selecting the
   least viable starting index for a circular gas-station journey, or -1 when
   total gas is insufficient, together with its exact correctness contract.
   This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List ZArith.

Import ListNotations.

Definition canCompleteCircuit_precond
    (gas cost : list Z) : Prop :=
  (0 < length gas)%nat /\
  length gas = length cost.

Fixpoint canCompleteCircuit_loop
    (g c : list Z)
    (idx : nat)
    (tank : Z)
    (start : nat) : Z :=
  match g, c with
  | [], [] => Z.of_nat start
  | gi :: gs, ci :: cs =>
      let tank' := (tank + gi - ci)%Z in
      if Z.ltb tank' 0%Z
      then canCompleteCircuit_loop gs cs (S idx) 0%Z (S idx)
      else canCompleteCircuit_loop gs cs (S idx) tank' start
  | _, _ => (-1)%Z
  end.

Fixpoint canCompleteCircuit_walk
    (pairs : list (Z * Z))
    (i : nat)
    (tank : Z)
    (start : nat) : Z :=
  match pairs with
  | [] => Z.of_nat start
  | (g, c) :: rest =>
      let newTank := (tank + g - c)%Z in
      if Z.ltb newTank 0%Z
      then canCompleteCircuit_walk rest (S i) 0%Z (S i)
      else canCompleteCircuit_walk rest (S i) newTank start
  end.

Definition canCompleteCircuit
    (gas cost : list Z)
    (_h_precond : canCompleteCircuit_precond gas cost) : Z :=
  let totalGas := fold_left Z.add gas 0%Z in
  let totalCost := fold_left Z.add cost 0%Z in
  if Z.ltb totalGas totalCost
  then (-1)%Z
  else canCompleteCircuit_walk (combine gas cost) 0%nat 0%Z 0%nat.

Definition canCompleteCircuit_prefixTank
    (gas cost : list Z)
    (start i : nat) : Z :=
  fold_left
    (fun tank j =>
      let jdx := Nat.modulo (start + j) (length gas) in
      (tank + nth jdx gas 0%Z - nth jdx cost 0%Z)%Z)
    (seq 0%nat (S i))
    0%Z.

Definition canCompleteCircuit_valid
    (gas cost : list Z)
    (start : nat) : bool :=
  forallb
    (fun i =>
      Z.leb 0%Z (canCompleteCircuit_prefixTank gas cost start i))
    (seq 0%nat (length gas)).

Definition canCompleteCircuit_postcond
    (gas cost : list Z)
    (result : Z)
    (_h_precond : canCompleteCircuit_precond gas cost) : Prop :=
  (-1 <= result)%Z /\
  (result = (-1)%Z ->
    forallb
      (fun start =>
        negb (canCompleteCircuit_valid gas cost start))
      (seq 0%nat (length gas)) = true) /\
  ((0 <= result)%Z ->
    (result < Z.of_nat (length gas))%Z /\
    canCompleteCircuit_valid gas cost (Z.to_nat result) = true /\
    forallb
      (fun start =>
        negb (canCompleteCircuit_valid gas cost start))
      (seq 0%nat (Z.to_nat result)) = true).

Theorem canCompleteCircuit_spec_satisfied
    (gas cost : list Z)
    (h_precond : canCompleteCircuit_precond gas cost) :
  canCompleteCircuit_postcond
    gas cost (canCompleteCircuit gas cost h_precond) h_precond.
Admitted.
