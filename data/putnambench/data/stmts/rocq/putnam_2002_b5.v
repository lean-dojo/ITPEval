(* Statement-only formalization of PutnamBench corpus artifact putnam_2002_b5:
   some natural number has a three-digit palindromic expansion in at least
   2002 different bases. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Lists.List.

Import ListNotations.

Fixpoint putnam_2002_b5_digits_fuel
    (fuel base n : nat) : list nat :=
  match fuel with
  | O => []
  | S fuel' =>
      if Nat.ltb base 2
      then repeat 1 n
      else
        if Nat.eqb n O
        then []
        else
          Nat.modulo n base ::
          putnam_2002_b5_digits_fuel
            fuel' base (Nat.div n base)
  end.

Definition putnam_2002_b5_digits
    (base n : nat) : list nat :=
  putnam_2002_b5_digits_fuel (S n) base n.

Definition putnam_2002_b5_three_digit_palindrome
    (n base : nat) : Prop :=
  (1 <= base)%nat /\
  length (putnam_2002_b5_digits base n) = 3%nat /\
  putnam_2002_b5_digits base n =
    rev (putnam_2002_b5_digits base n).

Definition putnam_2002_b5_has_cardinality_at_least
    (P : nat -> Prop) (minimum : nat) : Prop :=
  exists enumeration : list nat,
    NoDup enumeration /\
    (forall b : nat, In b enumeration <-> P b) /\
    (minimum <= length enumeration)%nat.

Theorem putnam_2002_b5 :
  exists n : nat,
    putnam_2002_b5_has_cardinality_at_least
      (putnam_2002_b5_three_digit_palindrome n)
      2002%nat.
Admitted.
