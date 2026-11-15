(* Statement-only formalization of VERINA corpus artifact verina_basic_63,
   catalog title "has_close_elements": an executable IEEE binary64 scan
   deciding whether a list contains two distinct elements whose absolute
   difference is below a nonnegative threshold, together with its precondition,
   pairwise-separation postcondition, and final correctness proposition. This
   file contains no proof. *)

From Stdlib Require Import
  Arith.PeanoNat Bool.Bool Floats.PrimFloat Lists.List.

Import ListNotations.

Definition absDiff (a b : float) : float :=
  let difference := PrimFloat.sub a b in
  if PrimFloat.ltb difference PrimFloat.zero
  then PrimFloat.sub b a
  else difference.

Definition has_close_elements_valid_number (x : float) : bool :=
  andb
    (negb (PrimFloat.is_nan x))
    (negb (PrimFloat.is_infinity x)).

Definition has_close_elements_precond
    (numbers : list float)
    (threshold : float) : Prop :=
  PrimFloat.leb PrimFloat.zero threshold = true /\
  PrimFloat.is_nan threshold = false /\
  forallb has_close_elements_valid_number numbers = true.

Fixpoint has_close_elements_inner_fuel
    (fuel : nat)
    (numbers : list float)
    (threshold : float)
    (idx idx2 : nat) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
      if Nat.ltb idx2 idx then
        let a := nth idx2 numbers PrimFloat.zero in
        let b := nth idx numbers PrimFloat.zero in
        let d := absDiff a b in
        if PrimFloat.ltb d threshold
        then true
        else
          has_close_elements_inner_fuel
            fuel' numbers threshold idx (S idx2)
      else false
  end.

Fixpoint has_close_elements_outer_fuel
    (fuel : nat)
    (numbers : list float)
    (threshold : float)
    (len idx : nat) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
      if Nat.ltb idx len then
        if has_close_elements_inner_fuel
             idx numbers threshold idx O
        then true
        else
          has_close_elements_outer_fuel
            fuel' numbers threshold len (S idx)
      else false
  end.

Definition has_close_elements
    (numbers : list float)
    (threshold : float)
    (_h_precond : has_close_elements_precond numbers threshold) : bool :=
  let len := length numbers in
  has_close_elements_outer_fuel len numbers threshold len O.

Fixpoint has_close_elements_pairwise_separated
    (threshold : float)
    (numbers : list float) : Prop :=
  match numbers with
  | [] => True
  | a :: rest =>
      Forall
        (fun b =>
          PrimFloat.leb threshold (absDiff a b) = true)
        rest /\
      has_close_elements_pairwise_separated threshold rest
  end.

Definition has_close_elements_postcond
    (numbers : list float)
    (threshold : float)
    (result : bool)
    (_h_precond : has_close_elements_precond numbers threshold) : Prop :=
  result = false <->
  has_close_elements_pairwise_separated threshold numbers.

Theorem has_close_elements_spec_satisfied
    (numbers : list float)
    (threshold : float)
    (h_precond : has_close_elements_precond numbers threshold) :
  has_close_elements_postcond
    numbers
    threshold
    (has_close_elements numbers threshold h_precond)
    h_precond.
Admitted.
