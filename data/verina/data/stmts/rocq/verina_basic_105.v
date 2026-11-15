(* Statement-only formalization of VERINA corpus artifact verina_basic_105,
   catalog title "arrayProduct": an executable element-wise product of two
   equal-length integer arrays using default-zero indexing, together with its
   precondition, postcondition, and final correctness proposition. This file
   contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List ZArith.

Import ListNotations.
Open Scope Z_scope.

Definition arrayProduct_precond
    (a b : list Z) : Prop :=
  length a = length b.

Fixpoint arrayProduct_set_nth
    (index : nat)
    (value : Z)
    (xs : list Z) : list Z :=
  match xs with
  | [] => []
  | x :: rest =>
      match index with
      | O => value :: rest
      | S index' =>
          x :: arrayProduct_set_nth index' value rest
      end
  end.

Fixpoint arrayProduct_loop_fuel
    (fuel : nat)
    (a b : list Z)
    (len i : nat)
    (c : list Z) : list Z :=
  match fuel with
  | O => c
  | S fuel' =>
      if Nat.ltb i len then
        let a_val := nth i a 0%Z in
        let b_val := nth i b 0%Z in
        let new_c :=
          arrayProduct_set_nth i (a_val * b_val) c in
        arrayProduct_loop_fuel
          fuel' a b len (S i) new_c
      else c
  end.

Definition loop
    (a b : list Z)
    (len i : nat)
    (c : list Z) : list Z :=
  arrayProduct_loop_fuel
    (Nat.sub len i) a b len i c.

Definition arrayProduct
    (a b : list Z)
    (_h_precond : arrayProduct_precond a b) : list Z :=
  let len := length a in
  let c := repeat 0%Z len in
  loop a b len O c.

Definition arrayProduct_postcond
    (a b result : list Z)
    (_h_precond : arrayProduct_precond a b) : Prop :=
  length result = length a /\
  forall i : nat,
    (i < length a)%nat ->
    (nth i a 0%Z * nth i b 0%Z = nth i result 0%Z)%Z.

Theorem arrayProduct_spec_satisfied
    (a b : list Z)
    (h_precond : arrayProduct_precond a b) :
  arrayProduct_postcond
    a b (arrayProduct a b h_precond) h_precond.
Admitted.
