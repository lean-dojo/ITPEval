(* Statement-only formalization of VERINA corpus artifact verina_basic_53,
   catalog title "CalSum": an executable recursive sum of the natural numbers
   from one through N, together with its unrestricted precondition, doubled
   closed-form postcondition, and final correctness proposition. This file
   contains no proof. *)

From Stdlib Require Import Arith.PeanoNat.

Definition CalSum_precond (_N : nat) : Prop :=
  True.

Fixpoint CalSum_loop (n : nat) : nat :=
  match n with
  | O => O
  | S k => S k + CalSum_loop k
  end.

Definition CalSum
    (N : nat)
    (_h_precond : CalSum_precond N) : nat :=
  CalSum_loop N.

Definition CalSum_postcond
    (N result : nat)
    (_h_precond : CalSum_precond N) : Prop :=
  2 * result = N * (N + 1).

Theorem CalSum_spec_satisfied
    (N : nat)
    (h_precond : CalSum_precond N) :
  CalSum_postcond N (CalSum N h_precond) h_precond.
Admitted.
