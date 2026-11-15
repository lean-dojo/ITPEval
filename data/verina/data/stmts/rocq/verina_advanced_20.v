(* Statement-only formalization of VERINA corpus artifact verina_advanced_20,
   catalog title "isItEight": an executable Boolean test for whether an
   integer is divisible by 8 or has digit 8 in its absolute decimal expansion,
   together with its correctness contract. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool ZArith.

Open Scope Z_scope.

Definition isItEight_precond (_n : Z) : Prop :=
  True.

Fixpoint hasDigitEight_fuel
    (fuel m : nat) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
      if Nat.eqb m 0
      then false
      else
        if Nat.eqb (Nat.modulo m 10) 8
        then true
        else hasDigitEight_fuel fuel' (Nat.div m 10)
  end.

Definition hasDigitEight (m : nat) : bool :=
  hasDigitEight_fuel m m.

Definition isItEight
    (n : Z)
    (_h_precond : isItEight_precond n) : bool :=
  orb
    (Z.eqb (Z.modulo n 8) 0)
    (hasDigitEight (Z.abs_nat n)).

Definition isItEight_postcond
    (n : Z)
    (result : bool)
    (_h_precond : isItEight_precond n) : Prop :=
  let absN := Z.abs_nat n in
  (Z.eqb (Z.modulo n 8) 0 = true \/
   exists i : nat,
     Nat.eqb
       (Nat.modulo (Nat.div absN (Nat.pow 10 i)) 10)
       8 = true) <->
  result = true.

Theorem isItEight_spec_satisfied
    (n : Z)
    (h_precond : isItEight_precond n) :
  isItEight_postcond
    n (isItEight n h_precond) h_precond.
Admitted.
