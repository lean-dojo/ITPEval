(* Statement-only formalization of VERINA corpus artifact verina_basic_83,
   catalog title "concat": executable concatenation of two arbitrary integer
   arrays by filling a fresh array from left to right, together with its
   unconditional precondition, pointwise-and-size postcondition, and final
   correctness proposition. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List ZArith.

Import ListNotations.

Module VerinaBasic83.

Definition concat_precond
    (_a _b : list Z) : Prop :=
  True.

Fixpoint concat_set_nth
    (index : nat)
    (value : Z)
    (xs : list Z) : list Z :=
  match xs with
  | [] => []
  | x :: rest =>
      match index with
      | O => value :: rest
      | S index' =>
          x :: concat_set_nth index' value rest
      end
  end.

Fixpoint concat_loop_fuel
    (fuel : nat)
    (a b : list Z)
    (n i : nat)
    (c : list Z) : list Z :=
  match fuel with
  | O => c
  | S fuel' =>
      if Nat.ltb i n then
        let value :=
          if Nat.ltb i (length a)
          then nth i a 0%Z
          else nth (i - length a)%nat b 0%Z in
        let c' := concat_set_nth i value c in
        concat_loop_fuel fuel' a b n (S i) c'
      else c
  end.

Definition concat_loop
    (a b : list Z)
    (n i : nat)
    (c : list Z) : list Z :=
  concat_loop_fuel (n - i)%nat a b n i c.

Definition concat
    (a b : list Z)
    (_h_precond : concat_precond a b) : list Z :=
  let n := (length a + length b)%nat in
  concat_loop a b n 0%nat (repeat 0%Z n).

Definition concat_postcond
    (a b result : list Z)
    (_h_precond : concat_precond a b) : Prop :=
  length result = (length a + length b)%nat /\
  (forall k : nat,
      (k < length a)%nat ->
      nth k result 0%Z = nth k a 0%Z) /\
  (forall k : nat,
      (k < length b)%nat ->
      nth (k + length a)%nat result 0%Z =
      nth k b 0%Z).

Theorem concat_spec_satisfied
    (a b : list Z)
    (h_precond : concat_precond a b) :
  concat_postcond
    a b (concat a b h_precond) h_precond.
Admitted.

End VerinaBasic83.
