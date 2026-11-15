(* Statement-only formalization of PutnamBench corpus artifact putnam_1989_a1:
   the number of primes whose usual base-10 digits alternate between 1 and 0,
   beginning and ending with 1, is 1; this file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Lists.List.

Import ListNotations.

Fixpoint putnam_1989_a1_decimal_digits_fuel
    (fuel n : nat) : list nat :=
  match fuel with
  | O => []
  | S fuel' =>
      if Nat.ltb n 10
      then [n]
      else
        Nat.modulo n 10 ::
        putnam_1989_a1_decimal_digits_fuel fuel' (Nat.div n 10)
  end.

Definition putnam_1989_a1_decimal_digits (n : nat) : list nat :=
  putnam_1989_a1_decimal_digits_fuel (S n) n.

Definition putnam_1989_a1_prime (p : nat) : Prop :=
  (2 <= p)%nat /\
  forall d : nat,
    Nat.divide d p ->
    d = 1%nat \/ d = p.

Definition putnam_1989_a1_alternating_digits
    (digits : list nat) : Prop :=
  Nat.Odd (length digits) /\
  forall i : nat,
    (i < length digits)%nat ->
    nth i digits 0 =
      if Nat.even i then 1%nat else 0%nat.

Definition putnam_1989_a1_qualifying_prime (p : nat) : Prop :=
  putnam_1989_a1_prime p /\
  putnam_1989_a1_alternating_digits
    (putnam_1989_a1_decimal_digits p).

Definition putnam_1989_a1_has_cardinality
    (P : nat -> Prop) (cardinality : nat) : Prop :=
  exists enumeration : list nat,
    NoDup enumeration /\
    (forall p : nat, In p enumeration <-> P p) /\
    length enumeration = cardinality.

Definition putnam_1989_a1_solution : nat := 1%nat.

Theorem putnam_1989_a1 :
  putnam_1989_a1_has_cardinality
    putnam_1989_a1_qualifying_prime
    putnam_1989_a1_solution.
Admitted.
