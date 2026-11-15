(* Statement-only formalization of VERINA corpus artifact verina_basic_40,
   catalog title "secondSmallest": an executable recursive scan of an integer
   array for its second-smallest distinct value, together with the distinctness
   precondition, order-theoretic postcondition, and final correctness
   proposition. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List ZArith.

Import ListNotations.

Definition secondSmallest_precond (s : list Z) : Prop :=
  (1 < length s)%nat /\
  exists i j : nat,
    (i < length s)%nat /\
    (j < length s)%nat /\
    nth i s 0%Z <> nth j s 0%Z.

Fixpoint secondSmallestAux_fuel
    (fuel : nat)
    (s : list Z)
    (i minIdx : nat)
    (secondIdx : option nat) : Z :=
  match fuel with
  | O =>
      match secondIdx with
      | Some si => nth si s 0%Z
      | None => 0%Z
      end
  | S remaining_fuel =>
      let x := nth i s 0%Z in
      let m := nth minIdx s 0%Z in
      match secondIdx with
      | None =>
          if Z.ltb x m then
            secondSmallestAux_fuel
              remaining_fuel s (S i) i (Some minIdx)
          else if Z.ltb m x then
            secondSmallestAux_fuel
              remaining_fuel s (S i) minIdx (Some i)
          else
            secondSmallestAux_fuel
              remaining_fuel s (S i) minIdx None
      | Some si =>
          let smin := nth si s 0%Z in
          if Z.ltb x m then
            secondSmallestAux_fuel
              remaining_fuel s (S i) i (Some minIdx)
          else if andb (Z.ltb x smin) (Z.ltb m x) then
            secondSmallestAux_fuel
              remaining_fuel s (S i) minIdx (Some i)
          else
            secondSmallestAux_fuel
              remaining_fuel s (S i) minIdx (Some si)
      end
  end.

Definition secondSmallestAux
    (s : list Z)
    (i minIdx : nat)
    (secondIdx : option nat) : Z :=
  secondSmallestAux_fuel
    (length s - i)%nat s i minIdx secondIdx.

Definition secondSmallest
    (s : list Z)
    (_h_precond : secondSmallest_precond s) : Z :=
  secondSmallestAux s 1%nat 0%nat None.

Definition secondSmallest_postcond
    (s : list Z)
    (result : Z)
    (_h_precond : secondSmallest_precond s) : Prop :=
  (exists i : nat,
      (i < length s)%nat /\
      nth i s 0%Z = result) /\
  exists j : nat,
    (j < length s)%nat /\
    (nth j s 0%Z < result)%Z /\
    forall k : nat,
      (k < length s)%nat ->
      nth k s 0%Z <> nth j s 0%Z ->
      (result <= nth k s 0%Z)%Z.

Theorem secondSmallest_spec_satisfied
    (s : list Z)
    (h_precond : secondSmallest_precond s) :
  secondSmallest_postcond
    s (secondSmallest s h_precond) h_precond.
Admitted.
