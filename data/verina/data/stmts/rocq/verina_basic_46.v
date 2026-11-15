(* Statement-only formalization of VERINA corpus artifact verina_basic_46,
   catalog title "lastPosition": an executable full scan of a nondecreasing
   integer array that returns the index of the last occurrence of a specified
   element or -1, together with its complete correctness contract. This file
   contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List Sorting.Sorted
  ZArith.

Import ListNotations.

Definition lastPosition_precond
    (arr : list Z) (_elem : Z) : Prop :=
  StronglySorted Z.le arr.

Fixpoint lastPosition_loop
    (remaining : list Z)
    (elem : Z)
    (i : nat)
    (pos : Z) : Z :=
  match remaining with
  | [] => pos
  | a :: rest =>
      let next_pos :=
        if Z.eqb a elem then Z.of_nat i else pos in
      lastPosition_loop rest elem (S i) next_pos
  end.

Definition lastPosition
    (arr : list Z)
    (elem : Z)
    (_h_precond : lastPosition_precond arr elem) : Z :=
  lastPosition_loop arr elem 0%nat (-1)%Z.

Definition lastPosition_postcond
    (arr : list Z)
    (elem result : Z)
    (_h_precond : lastPosition_precond arr elem) : Prop :=
  (result = (-1)%Z \/ (0 <= result)%Z) /\
  ((0 <= result)%Z ->
    (Z.to_nat result < length arr)%nat /\
    nth (Z.to_nat result) arr 0%Z = elem /\
    forallb
      (fun x => negb (Z.eqb x elem))
      (skipn (S (Z.to_nat result)) arr) = true) /\
  (result = (-1)%Z ->
    forallb
      (fun x => negb (Z.eqb x elem))
      arr = true).

Theorem lastPosition_spec_satisfied
    (arr : list Z)
    (elem : Z)
    (h_precond : lastPosition_precond arr elem) :
  lastPosition_postcond
    arr
    elem
    (lastPosition arr elem h_precond)
    h_precond.
Admitted.
