(* Statement-only formalization of VERINA corpus artifact verina_advanced_18,
   catalog title "isArmstrong": an executable Armstrong-number test and its
   decimal-digit power-sum correctness contract. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Lists.List.

Import ListNotations.

Fixpoint countDigits_go
    (fuel n acc : nat) : nat :=
  match fuel with
  | O => acc
  | S fuel' =>
      if Nat.eqb n 0
      then acc
      else countDigits_go fuel' (Nat.div n 10) (acc + 1)
  end.

Definition countDigits (n : nat) : nat :=
  countDigits_go n n (if Nat.eqb n 0 then 1 else 0).

Definition isArmstrong_precond (_n : nat) : Prop :=
  True.

Fixpoint sumPowers_go
    (fuel n acc k : nat) : nat :=
  match fuel with
  | O => acc
  | S fuel' =>
      if Nat.eqb n 0
      then acc
      else
        let digit := Nat.modulo n 10 in
        sumPowers_go
          fuel' (Nat.div n 10) (acc + Nat.pow digit k) k
  end.

Definition sumPowers (n k : nat) : nat :=
  sumPowers_go n n 0 k.

Definition isArmstrong
    (n : nat)
    (_h_precond : isArmstrong_precond n) : bool :=
  let k := countDigits n in
  Nat.eqb (sumPowers n k) n.

Fixpoint decimalDigits_rev_go
    (fuel n : nat) : list nat :=
  match fuel with
  | O => []
  | S fuel' =>
      if Nat.eqb n 0
      then []
      else
        Nat.modulo n 10
          :: decimalDigits_rev_go fuel' (Nat.div n 10)
  end.

Definition decimalDigits (n : nat) : list nat :=
  if Nat.eqb n 0
  then [0]
  else rev (decimalDigits_rev_go n n).

Definition isArmstrong_digitPowerSum (n : nat) : nat :=
  fold_left
    (fun acc d => acc + Nat.pow d (countDigits n))
    (decimalDigits n) 0.

Definition isArmstrong_postcond
    (n : nat)
    (result : bool)
    (_h_precond : isArmstrong_precond n) : Prop :=
  let n' := isArmstrong_digitPowerSum n in
  (result = true -> n = n') /\
  (result = false -> n <> n').

Theorem isArmstrong_spec_satisfied
    (n : nat)
    (h_precond : isArmstrong_precond n) :
  isArmstrong_postcond
    n (isArmstrong n h_precond) h_precond.
Admitted.
