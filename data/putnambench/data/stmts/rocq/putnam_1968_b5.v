(* Statement-only formalization of PutnamBench artifact putnam_1968_b5:
   counting 2 x 2 matrices over the field with p elements that have trace 1
   and determinant 0. This file contains no proof. *)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition putnam_1968_b5_solution (p : nat) : nat := (p ^ 2 + p)%nat.

Definition putnam_1968_b5_entry
    {p : nat} (M : 4.-tuple 'I_p) (i : 'I_4) : nat :=
  nat_of_ord (tnth M i).

Definition putnam_1968_b5_condition
    {p : nat} (M : 4.-tuple 'I_p) : bool :=
  let a := putnam_1968_b5_entry M (inord 0) in
  let b := putnam_1968_b5_entry M (inord 1) in
  let c := putnam_1968_b5_entry M (inord 2) in
  let d := putnam_1968_b5_entry M (inord 3) in
  (((a + d) %% p == 1) && ((a * d) %% p == (b * c) %% p))%nat.

Theorem putnam_1968_b5
    (p : nat)
    (hp : prime p) :
  #|[pred M : 4.-tuple 'I_p | putnam_1968_b5_condition M]|
    = putnam_1968_b5_solution p.
Proof. Admitted.
