(* Statement-only formalization of PutnamBench artifact putnam_2007_b4:
   counting ordered pairs of real polynomials whose squares sum to
   X^(2n) + 1 and whose degrees are strictly ordered. This file contains no proof. *)

From Stdlib Require Import Reals List Arith.

Import ListNotations.
Open Scope R_scope.

Definition putnam_2007_b4_polynomial : Type := nat -> R.

Definition putnam_2007_b4_finite_support
    (P : putnam_2007_b4_polynomial) : Prop :=
  exists bound : nat, forall k : nat, (bound < k)%nat -> P k = 0.

Definition putnam_2007_b4_poly_eq
    (P Q : putnam_2007_b4_polynomial) : Prop :=
  forall k : nat, P k = Q k.

Definition putnam_2007_b4_poly_add
    (P Q : putnam_2007_b4_polynomial) : putnam_2007_b4_polynomial :=
  fun k : nat => P k + Q k.

Fixpoint putnam_2007_b4_convolution
    (P Q : putnam_2007_b4_polynomial) (k terms : nat) : R :=
  match terms with
  | O => P O * Q k
  | S previous =>
      putnam_2007_b4_convolution P Q k previous
      + P (S previous) * Q ((k - S previous)%nat)
  end.

Definition putnam_2007_b4_poly_mul
    (P Q : putnam_2007_b4_polynomial) : putnam_2007_b4_polynomial :=
  fun k : nat => putnam_2007_b4_convolution P Q k k.

Definition putnam_2007_b4_poly_one : putnam_2007_b4_polynomial :=
  fun k : nat => if Nat.eqb k O then 1 else 0.

Definition putnam_2007_b4_poly_X : putnam_2007_b4_polynomial :=
  fun k : nat => if Nat.eqb k 1%nat then 1 else 0.

Fixpoint putnam_2007_b4_poly_pow
    (P : putnam_2007_b4_polynomial) (exponent : nat)
    : putnam_2007_b4_polynomial :=
  match exponent with
  | O => putnam_2007_b4_poly_one
  | S previous =>
      putnam_2007_b4_poly_mul P
        (putnam_2007_b4_poly_pow P previous)
  end.

Definition putnam_2007_b4_zero_poly
    (P : putnam_2007_b4_polynomial) : Prop :=
  forall k : nat, P k = 0.

Definition putnam_2007_b4_has_degree
    (P : putnam_2007_b4_polynomial) (degree : nat) : Prop :=
  P degree <> 0 /\
  forall k : nat, (degree < k)%nat -> P k = 0.

Definition putnam_2007_b4_degree_gt
    (P Q : putnam_2007_b4_polynomial) : Prop :=
  exists degree_P : nat,
    putnam_2007_b4_has_degree P degree_P /\
    (putnam_2007_b4_zero_poly Q \/
     exists degree_Q : nat,
       putnam_2007_b4_has_degree Q degree_Q /\
       (degree_Q < degree_P)%nat).

Definition putnam_2007_b4_pair_eq
    (left right :
      putnam_2007_b4_polynomial * putnam_2007_b4_polynomial) : Prop :=
  putnam_2007_b4_poly_eq (fst left) (fst right) /\
  putnam_2007_b4_poly_eq (snd left) (snd right).

Inductive putnam_2007_b4_pair_nodup :
    list (putnam_2007_b4_polynomial * putnam_2007_b4_polynomial) -> Prop :=
| putnam_2007_b4_pair_nodup_nil :
    putnam_2007_b4_pair_nodup []
| putnam_2007_b4_pair_nodup_cons :
    forall
      (head : putnam_2007_b4_polynomial * putnam_2007_b4_polynomial)
      (tail : list
        (putnam_2007_b4_polynomial * putnam_2007_b4_polynomial)),
      (forall item, In item tail ->
        ~ putnam_2007_b4_pair_eq head item) ->
      putnam_2007_b4_pair_nodup tail ->
      putnam_2007_b4_pair_nodup (head :: tail).

Definition putnam_2007_b4_has_cardinality
    (property :
      (putnam_2007_b4_polynomial * putnam_2007_b4_polynomial) -> Prop)
    (cardinality : nat) : Prop :=
  exists enumeration :
      list (putnam_2007_b4_polynomial * putnam_2007_b4_polynomial),
    length enumeration = cardinality /\
    (forall item, In item enumeration -> property item) /\
    putnam_2007_b4_pair_nodup enumeration /\
    (forall item, property item ->
      exists representative, In representative enumeration /\
        putnam_2007_b4_pair_eq item representative).

Definition putnam_2007_b4_condition
    (n : nat)
    (pair : putnam_2007_b4_polynomial * putnam_2007_b4_polynomial) : Prop :=
  let P := fst pair in
  let Q := snd pair in
  putnam_2007_b4_finite_support P /\
  putnam_2007_b4_finite_support Q /\
  putnam_2007_b4_poly_eq
    (putnam_2007_b4_poly_add
      (putnam_2007_b4_poly_pow P 2)
      (putnam_2007_b4_poly_pow Q 2))
    (putnam_2007_b4_poly_add
      (putnam_2007_b4_poly_pow putnam_2007_b4_poly_X ((2 * n)%nat))
      putnam_2007_b4_poly_one) /\
  putnam_2007_b4_degree_gt P Q.

Theorem putnam_2007_b4 :
  forall n : nat, (0 < n)%nat ->
    putnam_2007_b4_has_cardinality
      (putnam_2007_b4_condition n)
      (Nat.pow 2 ((n + 1)%nat)).
Admitted.
