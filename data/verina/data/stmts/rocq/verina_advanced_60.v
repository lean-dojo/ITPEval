(* Statement-only formalization of VERINA corpus artifact verina_advanced_60,
   catalog title "partitionEvensOdds": an executable stable partition of a
   list of natural numbers into its even and odd elements, together with its
   filtering and parity correctness contract. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List.

Import ListNotations.

Definition partitionEvensOdds_precond
    (_nums : list nat) : Prop :=
  True.

Fixpoint partitionEvensOdds_helper
    (nums : list nat) : list nat * list nat :=
  match nums with
  | [] => ([], [])
  | x :: xs =>
      let '(evens, odds) := partitionEvensOdds_helper xs in
      if Nat.eqb (Nat.modulo x 2) 0
      then (x :: evens, odds)
      else (evens, x :: odds)
  end.

Definition partitionEvensOdds
    (nums : list nat)
    (_h_precond : partitionEvensOdds_precond nums)
    : list nat * list nat :=
  partitionEvensOdds_helper nums.

Definition partitionEvensOdds_postcond
    (nums : list nat)
    (result : list nat * list nat)
    (_h_precond : partitionEvensOdds_precond nums) : Prop :=
  let evens := fst result in
  let odds := snd result in
  evens ++ odds =
    filter (fun n => Nat.eqb (Nat.modulo n 2) 0) nums ++
    filter (fun n => Nat.eqb (Nat.modulo n 2) 1) nums /\
  forallb (fun n => Nat.eqb (Nat.modulo n 2) 0) evens = true /\
  forallb (fun n => Nat.eqb (Nat.modulo n 2) 1) odds = true.

Theorem partitionEvensOdds_spec_satisfied
    (nums : list nat)
    (h_precond : partitionEvensOdds_precond nums) :
  partitionEvensOdds_postcond
    nums (partitionEvensOdds nums h_precond) h_precond.
Admitted.
