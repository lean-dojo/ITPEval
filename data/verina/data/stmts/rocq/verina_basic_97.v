(* Statement-only formalization of VERINA corpus artifact verina_basic_97
   (verina__rocq__verina_basic_97), catalog title "TestArrayElements": an
   executable integer-array update that sets the element at a valid natural
   index to 60, together with its bounds precondition, complete array
   postcondition, and final correctness proposition. This file contains no
   proof. *)

From Stdlib Require Import Arith.PeanoNat Lists.List ZArith.

Import ListNotations.

Definition TestArrayElements_getBang
    (a : list Z) (k : nat) : Z :=
  nth k a 0%Z.

Fixpoint TestArrayElements_setBang
    (a : list Z) (k : nat) (value : Z) : list Z :=
  match a with
  | [] => []
  | x :: rest =>
      match k with
      | O => value :: rest
      | S k' => x :: TestArrayElements_setBang rest k' value
      end
  end.

Definition TestArrayElements_precond
    (a : list Z) (j : nat) : Prop :=
  (j < length a)%nat.

Definition TestArrayElements
    (a : list Z)
    (j : nat)
    (_h_precond : TestArrayElements_precond a j) : list Z :=
  TestArrayElements_setBang a j 60%Z.

Definition TestArrayElements_postcond
    (a : list Z)
    (j : nat)
    (result : list Z)
    (_h_precond : TestArrayElements_precond a j) : Prop :=
  length result = length a /\
  TestArrayElements_getBang result j = 60%Z /\
  forall k : nat,
    (k < length a)%nat ->
    k <> j ->
    TestArrayElements_getBang result k =
      TestArrayElements_getBang a k.

Theorem TestArrayElements_spec_satisfied
    (a : list Z)
    (j : nat)
    (h_precond : TestArrayElements_precond a j) :
  TestArrayElements_postcond
    a j (TestArrayElements a j h_precond) h_precond.
Admitted.
