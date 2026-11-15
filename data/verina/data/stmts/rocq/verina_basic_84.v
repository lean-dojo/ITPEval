(* Statement-only formalization of VERINA corpus artifact verina_basic_84,
   catalog title "replace": executable left-to-right replacement of every
   integer-array entry greater than a threshold by -1, together with its
   unconditional precondition, pointwise-and-size postcondition, and final
   correctness proposition. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List ZArith.

Import ListNotations.

Module VerinaBasic84.

Definition replace_precond
    (_arr : list Z) (_k : Z) : Prop :=
  True.

Fixpoint replace_set_nth
    (index : nat)
    (value : Z)
    (xs : list Z) : list Z :=
  match xs with
  | [] => []
  | x :: rest =>
      match index with
      | O => value :: rest
      | S index' => x :: replace_set_nth index' value rest
      end
  end.

Fixpoint replace_loop_fuel
    (fuel : nat)
    (oldArr : list Z)
    (k : Z)
    (i : nat)
    (acc : list Z) : list Z :=
  match fuel with
  | O => acc
  | S fuel' =>
      if Nat.ltb i (length oldArr) then
        let acc' :=
          if Z.gtb (nth i oldArr 0%Z) k
          then replace_set_nth i (-1)%Z acc
          else acc in
        replace_loop_fuel fuel' oldArr k (S i) acc'
      else acc
  end.

Definition replace_loop
    (oldArr : list Z)
    (k : Z)
    (i : nat)
    (acc : list Z) : list Z :=
  replace_loop_fuel
    (Nat.sub (length oldArr) i) oldArr k i acc.

Definition replace
    (arr : list Z)
    (k : Z)
    (_h_precond : replace_precond arr k) : list Z :=
  replace_loop arr k O arr.

Definition replace_postcond
    (arr : list Z)
    (k : Z)
    (result : list Z)
    (_h_precond : replace_precond arr k) : Prop :=
  length result = length arr /\
  (forall i : nat,
      (i < length arr)%nat ->
      (nth i arr 0%Z > k)%Z ->
      nth i result 0%Z = (-1)%Z) /\
  (forall i : nat,
      (i < length arr)%nat ->
      (nth i arr 0%Z <= k)%Z ->
      nth i result 0%Z = nth i arr 0%Z).

Theorem replace_spec_satisfied
    (arr : list Z)
    (k : Z)
    (h_precond : replace_precond arr k) :
  replace_postcond
    arr k (replace arr k h_precond) h_precond.
Admitted.

End VerinaBasic84.
