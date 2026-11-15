(* Statement-only formalization of VERINA corpus artifact verina_basic_21,
   catalog title "isSublist": an executable left-to-right search deciding
   whether one integer list occurs as a contiguous slice of another, together
   with its trivial precondition, exact slice-existence postcondition, and
   final correctness proposition. This file contains no proof. *)

From Stdlib Require Import Bool.Bool Lists.List ZArith.

Import ListNotations.

Definition isSublist_precond
    (_sub _main : list Z) : Prop :=
  True.

Fixpoint isSublist_list_eqb
    (xs ys : list Z) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' =>
      Z.eqb x y && isSublist_list_eqb xs' ys'
  | _, _ => false
  end.

Fixpoint isSublist_check_fuel
    (fuel i subLen mainLen : nat)
    (sub main : list Z) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
      if Nat.ltb mainLen (i + subLen)
      then false
      else
        if isSublist_list_eqb
             sub (firstn subLen (skipn i main))
        then true
        else
          if Nat.leb (i + 1) mainLen
          then
            isSublist_check_fuel
              fuel' (i + 1) subLen mainLen sub main
          else false
  end.

Definition isSublist
    (sub main : list Z)
    (_h_precond : isSublist_precond sub main) : bool :=
  let subLen := length sub in
  let mainLen := length main in
  if Nat.ltb mainLen subLen
  then false
  else
    isSublist_check_fuel
      (S mainLen) 0 subLen mainLen sub main.

Definition isSublist_postcond
    (sub main : list Z)
    (result : bool)
    (_h_precond : isSublist_precond sub main) : Prop :=
  (exists i : nat,
      i + length sub <= length main /\
      sub = firstn (length sub) (skipn i main)) <->
  result = true.

Theorem isSublist_spec_satisfied
    (sub main : list Z)
    (h_precond : isSublist_precond sub main) :
  isSublist_postcond
    sub main (isSublist sub main h_precond) h_precond.
Admitted.
