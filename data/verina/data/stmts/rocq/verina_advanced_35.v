(* Statement-only formalization of VERINA corpus artifact verina_advanced_35,
   catalog title "majorityElement": an executable search for the integer
   occurring strictly more than half the time, together with its existence,
   uniqueness, and correctness contract. This file contains no proof. *)

From Stdlib Require Import Lists.List ZArith.

Import ListNotations.

Definition majorityElement_count (x : Z) (nums : list Z) : nat :=
  count_occ Z.eq_dec nums x.

Definition majorityElement_precond (nums : list Z) : Prop :=
  Nat.lt 0 (length nums) /\
  exists x : Z,
    In x nums /\
    Nat.lt
      (Nat.div (length nums) 2)
      (majorityElement_count x nums).

Fixpoint majorityElement_find
    (nums remaining : list Z) : option Z :=
  match remaining with
  | [] => None
  | x :: xs =>
      if Nat.ltb
           (Nat.div (length nums) 2)
           (majorityElement_count x nums)
      then Some x
      else majorityElement_find nums xs
  end.

Definition majorityElement
    (nums : list Z)
    (_h_precond : majorityElement_precond nums) : Z :=
  match majorityElement_find nums nums with
  | Some x => x
  | None => 0%Z
  end.

Definition majorityElement_postcond
    (nums : list Z)
    (result : Z)
    (_h_precond : majorityElement_precond nums) : Prop :=
  Nat.lt
    (Nat.div (length nums) 2)
    (majorityElement_count result nums) /\
  forall x : Z,
    In x nums ->
    x <> result ->
    Nat.le
      (majorityElement_count x nums)
      (Nat.div (length nums) 2).

Theorem majorityElement_spec_satisfied
    (nums : list Z)
    (h_precond : majorityElement_precond nums) :
  majorityElement_postcond
    nums (majorityElement nums h_precond) h_precond.
Admitted.
