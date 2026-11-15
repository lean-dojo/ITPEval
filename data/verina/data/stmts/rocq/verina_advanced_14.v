(* Statement-only formalization of VERINA corpus artifact verina_advanced_14,
   catalog title "ifPowerOfFour": an executable recursive test for whether a
   natural number is a power of four, together with its correctness contract.
   This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool.

Definition ifPowerOfFour_precond (_n : nat) : Prop :=
  True.

Fixpoint ifPowerOfFour_helper_fuel
    (fuel n : nat) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
      match n with
      | O => false
      | S m =>
          match m with
          | O => true
          | S l =>
              if Nat.eqb (Nat.modulo (l + 2) 4) 0
              then
                ifPowerOfFour_helper_fuel
                  fuel' (Nat.div (l + 2) 4)
              else false
          end
      end
  end.

Definition ifPowerOfFour_helper (n : nat) : bool :=
  ifPowerOfFour_helper_fuel n n.

Definition ifPowerOfFour
    (n : nat)
    (_h_precond : ifPowerOfFour_precond n) : bool :=
  ifPowerOfFour_helper n.

Definition ifPowerOfFour_postcond
    (n : nat)
    (result : bool)
    (_h_precond : ifPowerOfFour_precond n) : Prop :=
  result = true <->
  exists m : nat, n = Nat.pow 4 m.

Theorem ifPowerOfFour_spec_satisfied
    (n : nat)
    (h_precond : ifPowerOfFour_precond n) :
  ifPowerOfFour_postcond
    n (ifPowerOfFour n h_precond) h_precond.
Admitted.
