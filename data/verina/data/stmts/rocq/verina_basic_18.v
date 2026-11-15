(* Statement-only formalization of VERINA corpus artifact verina_basic_18,
   catalog title "sumOfDigits": an executable accumulator loop computes the
   sum of the decimal digits of a natural number, together with its trivial
   precondition, decimal-representation postcondition, and final correctness
   proposition. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Lists.List.

Import ListNotations.

Definition sumOfDigits_precond (_n : nat) : Prop :=
  True.

Fixpoint sumOfDigits_loop_fuel
    (fuel n acc : nat) : nat :=
  match fuel with
  | O => acc
  | S fuel' =>
      if Nat.eqb n 0
      then acc
      else
        sumOfDigits_loop_fuel
          fuel' (Nat.div n 10) (acc + Nat.modulo n 10)
  end.

Definition sumOfDigits
    (n : nat)
    (_h_precond : sumOfDigits_precond n) : nat :=
  sumOfDigits_loop_fuel n n 0.

Fixpoint sumOfDigits_decimal_digits_rev_fuel
    (fuel n : nat) : list nat :=
  match fuel with
  | O => []
  | S fuel' =>
      if Nat.eqb n 0
      then []
      else
        Nat.modulo n 10
          :: sumOfDigits_decimal_digits_rev_fuel
               fuel' (Nat.div n 10)
  end.

Definition sumOfDigits_decimal_digits
    (n : nat) : list nat :=
  if Nat.eqb n 0
  then [0]
  else rev (sumOfDigits_decimal_digits_rev_fuel n n).

Fixpoint sumOfDigits_list_sum
    (digits : list nat) : nat :=
  match digits with
  | [] => 0
  | digit :: rest =>
      digit + sumOfDigits_list_sum rest
  end.

Definition sumOfDigits_decimal_repr_sum
    (n : nat) : nat :=
  sumOfDigits_list_sum (sumOfDigits_decimal_digits n).

Definition sumOfDigits_postcond
    (n result : nat)
    (_h_precond : sumOfDigits_precond n) : Prop :=
  Nat.sub result (sumOfDigits_decimal_repr_sum n) = 0 /\
  Nat.sub (sumOfDigits_decimal_repr_sum n) result = 0.

Theorem sumOfDigits_spec_satisfied
    (n : nat)
    (h_precond : sumOfDigits_precond n) :
  sumOfDigits_postcond
    n (sumOfDigits n h_precond) h_precond.
Admitted.
