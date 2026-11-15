(* Statement-only formalization of PutnamBench corpus artifact putnam_2010_a1:
   the greatest number of boxes into which 1 through n can be partitioned
   with equal sums is the ceiling of n/2. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat.

Fixpoint putnam_2010_a1_box_sum
    (boxes : nat -> nat) (box n : nat) : nat :=
  match n with
  | O => O
  | S m =>
      putnam_2010_a1_box_sum boxes box m +
      if Nat.eqb (boxes (S m)) box then S m else O
  end.

Definition putnam_2010_a1_admissible (n k : nat) : Prop :=
  exists boxes : nat -> nat,
    (forall m : nat,
        1 <= m <= n ->
        1 <= boxes m <= k) /\
    (forall i j : nat,
        1 <= i <= k ->
        1 <= j <= k ->
        putnam_2010_a1_box_sum boxes i n =
        putnam_2010_a1_box_sum boxes j n).

Definition putnam_2010_a1_is_greatest
    (P : nat -> Prop) (greatest : nat) : Prop :=
  P greatest /\
  forall k : nat, P k -> k <= greatest.

Theorem putnam_2010_a1
    (n : nat)
    (kboxes : nat -> Prop)
    (npos : 0 < n)
    (hkboxes :
      forall k : nat,
        kboxes k <-> putnam_2010_a1_admissible n k) :
  putnam_2010_a1_is_greatest kboxes (Nat.div (n + 1) 2).
Admitted.
