(* Statement-only formalization of VERINA corpus artifact verina_basic_80,
   catalog title "only_once": an executable scan deciding whether a key
   occurs exactly once in an integer array, together with its helper count,
   unconditional precondition, postcondition, and final correctness
   proposition. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List ZArith.

Import ListNotations.

Definition only_once_precond
    (_a : list Z)
    (_key : Z) : Prop :=
  True.

Fixpoint only_once_loop_fuel {T : Type}
    (eq_dec : forall x y : T, {x = y} + {x <> y})
    (fuel : nat)
    (a : list T)
    (key : T)
    (i keyCount : nat) : bool :=
  match fuel with
  | O => Nat.eqb keyCount 1%nat
  | S fuel' =>
      if Nat.ltb i (length a)
      then
        match nth_error a i with
        | Some value =>
            let newCount :=
              if eq_dec value key then S keyCount else keyCount in
            only_once_loop_fuel
              eq_dec fuel' a key (S i) newCount
        | None => Nat.eqb keyCount 1%nat
        end
      else Nat.eqb keyCount 1%nat
  end.

Definition only_once_loop {T : Type}
    (eq_dec : forall x y : T, {x = y} + {x <> y})
    (a : list T)
    (key : T)
    (i keyCount : nat) : bool :=
  only_once_loop_fuel
    eq_dec (length a - i)%nat a key i keyCount.

Definition only_once
    (a : list Z)
    (key : Z)
    (_h_precond : only_once_precond a key) : bool :=
  only_once_loop Z.eq_dec a key 0%nat 0%nat.

Definition count_occurrences {T : Type}
    (eq_dec : forall x y : T, {x = y} + {x <> y})
    (a : list T)
    (key : T) : nat :=
  fold_left
    (fun count value =>
      if eq_dec value key then S count else count)
    a
    0%nat.

Definition only_once_postcond
    (a : list Z)
    (key : Z)
    (result : bool)
    (_h_precond : only_once_precond a key) : Prop :=
  (count_occurrences Z.eq_dec a key = 1%nat -> Is_true result) /\
  (count_occurrences Z.eq_dec a key <> 1%nat -> ~ Is_true result).

Theorem only_once_spec_satisfied
    (a : list Z)
    (key : Z)
    (h_precond : only_once_precond a key) :
  only_once_postcond
    a key (only_once a key h_precond) h_precond.
Admitted.
