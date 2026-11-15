(* Statement-only formalization of VERINA corpus artifact verina_basic_13,
   catalog title "cubeElements": executable element-wise cubing of an integer
   array, together with its no-precondition contract, length preservation, and
   pointwise correctness proposition. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Lists.List ZArith.

Import ListNotations.
Open Scope Z_scope.

Definition cubeElements_precond (_a : list Z) : Prop :=
  True.

Definition cubeElements
    (a : list Z)
    (_h_precond : cubeElements_precond a) : list Z :=
  map (fun x => x * x * x) a.

Definition cubeElements_postcond
    (a result : list Z)
    (_h_precond : cubeElements_precond a) : Prop :=
  length result = length a /\
  forall i : nat,
    (i < length a)%nat ->
    nth i result 0%Z =
      (nth i a 0%Z * nth i a 0%Z * nth i a 0%Z)%Z.

Theorem cubeElements_spec_satisfied
    (a : list Z)
    (h_precond : cubeElements_precond a) :
  cubeElements_postcond
    a (cubeElements a h_precond) h_precond.
Admitted.
