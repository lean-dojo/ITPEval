(* Statement-only formalization of VERINA corpus artifact verina_advanced_36,
   catalog title "majorityElement": an executable recursive candidate scan
   over a nonempty natural-number list guaranteed to contain an element
   occurring strictly more than half the time, together with its correctness
   contract. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List.

Import ListNotations.

Fixpoint countOccurrences
    (target : nat)
    (lst : list nat) : nat :=
  match lst with
  | [] => 0
  | y :: ys =>
      if Nat.eqb y target
      then 1 + countOccurrences target ys
      else countOccurrences target ys
  end.

Fixpoint findCandidate
    (lst : list nat)
    (candidate : option nat)
    (count : nat) : nat :=
  match lst with
  | [] =>
      match candidate with
      | Some c => c
      | None => 0
      end
  | x :: xs =>
      match candidate with
      | Some c =>
          if Nat.eqb x c
          then findCandidate xs (Some c) (count + 1)
          else if Nat.eqb count 0
          then findCandidate xs (Some x) 1
          else findCandidate xs (Some c) (count - 1)
      | None =>
          findCandidate xs (Some x) 1
      end
  end.

Definition majorityElement_precond
    (xs : list nat) : Prop :=
  Nat.lt 0 (length xs) /\
  existsb
    (fun x =>
      Nat.ltb
        (Nat.div (length xs) 2)
        (count_occ Nat.eq_dec xs x))
    xs = true.

Definition majorityElement
    (xs : list nat)
    (_h_precond : majorityElement_precond xs) : nat :=
  findCandidate xs None 0.

Definition majorityElement_postcond
    (xs : list nat)
    (result : nat)
    (_h_precond : majorityElement_precond xs) : Prop :=
  Nat.lt
    (Nat.div (length xs) 2)
    (count_occ Nat.eq_dec xs result).

Theorem majorityElement_spec_satisfied
    (xs : list nat)
    (h_precond : majorityElement_precond xs) :
  majorityElement_postcond
    xs (majorityElement xs h_precond) h_precond.
Admitted.
