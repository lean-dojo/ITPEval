(* Statement-only formalization of VERINA corpus artifact verina_basic_4,
   catalog title "kthElement": an executable 1-based lookup in an integer
   array, together with its valid-index precondition, element-selection
   postcondition, and final correctness proposition. This file contains no
   proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List ZArith.

Open Scope Z_scope.

Definition kthElement_precond
    (arr : list Z) (k : nat) : Prop :=
  (1 <= k)%nat /\ (k <= length arr)%nat.

Definition kthElement_getD
    (arr : list Z) (index : nat) : Z :=
  nth index arr 0%Z.

Definition kthElement
    (arr : list Z)
    (k : nat)
    (_h_precond : kthElement_precond arr k) : Z :=
  kthElement_getD arr (Nat.sub k 1%nat).

Definition kthElement_postcond
    (arr : list Z)
    (k : nat)
    (result : Z)
    (_h_precond : kthElement_precond arr k) : Prop :=
  existsb
    (fun x =>
      andb
        (Z.eqb x result)
        (Z.eqb x (kthElement_getD arr (Nat.sub k 1%nat))))
    arr = true.

Theorem kthElement_spec_satisfied
    (arr : list Z)
    (k : nat)
    (h_precond : kthElement_precond arr k) :
  kthElement_postcond
    arr k (kthElement arr k h_precond) h_precond.
Admitted.
