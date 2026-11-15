(* Statement-only formalization of VERINA corpus artifact verina_advanced_7,
   catalog title "binaryToDecimal": executable conversion of a big-endian
   list of binary digits to its natural-number value, together with its
   correctness contract. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Lists.List.

Import ListNotations.

Definition binaryToDecimal_precond (digits : list nat) : Prop :=
  Forall (fun d : nat => d = 0%nat \/ d = 1%nat) digits.

Fixpoint binaryToDecimal_helper (digits : list nat) : nat :=
  match digits with
  | [] => 0%nat
  | first :: rest =>
      first * Nat.pow 2 (length rest) +
      binaryToDecimal_helper rest
  end.

Definition binaryToDecimal
    (digits : list nat)
    (_h_precond : binaryToDecimal_precond digits) : nat :=
  binaryToDecimal_helper digits.

Definition binaryToDecimal_fold (digits : list nat) : nat :=
  fold_left
    (fun acc bit => acc * 2 + bit)
    digits 0%nat.

Definition binaryToDecimal_postcond
    (digits : list nat)
    (result : nat)
    (_h_precond : binaryToDecimal_precond digits) : Prop :=
  Nat.sub result (binaryToDecimal_fold digits) = 0%nat /\
  Nat.sub (binaryToDecimal_fold digits) result = 0%nat.

Theorem binaryToDecimal_spec_satisfied
    (digits : list nat)
    (h_precond : binaryToDecimal_precond digits) :
  binaryToDecimal_postcond
    digits (binaryToDecimal digits h_precond) h_precond.
Admitted.
