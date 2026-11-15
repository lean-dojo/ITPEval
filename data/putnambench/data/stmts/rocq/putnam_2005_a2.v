(* Statement-only formalization of PutnamBench corpus artifact putnam_2005_a2:
   the number of unit-step rook tours through every point of an n-by-3
   integer grid, from (1,1) to (n,1). This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Lists.List ZArith.

Open Scope Z_scope.

Definition putnam_2005_a2_point : Type := (Z * Z)%type.

Definition putnam_2005_a2_board
    (n : nat) (P : putnam_2005_a2_point) : Prop :=
  let '(a, b) := P in
  1 <= a <= Z.of_nat n /\ 1 <= b <= 3.

Definition putnam_2005_a2_unit
    (P Q : putnam_2005_a2_point) : Prop :=
  let '(a, b) := P in
  let '(c, d) := Q in
  (a = c /\ Z.abs (d - b) = 1) \/
  (b = d /\ Z.abs (c - a) = 1).

Definition putnam_2005_a2_same_path
    (p q : nat -> putnam_2005_a2_point) : Prop :=
  forall i : nat, p i = q i.

Fixpoint putnam_2005_a2_pairwise_distinct
    {A : Type} (equiv : A -> A -> Prop) (xs : list A) : Prop :=
  match xs with
  | nil => True
  | cons x tail =>
      (forall y : A, In y tail -> ~ equiv x y) /\
      putnam_2005_a2_pairwise_distinct equiv tail
  end.

Definition putnam_2005_a2_has_cardinality
    {A : Type} (equiv : A -> A -> Prop)
    (P : A -> Prop) (cardinality : nat) : Prop :=
  exists representatives : list A,
    putnam_2005_a2_pairwise_distinct equiv representatives /\
    (forall x : A,
        P x <->
        exists representative : A,
          In representative representatives /\
          equiv x representative) /\
    length representatives = cardinality.

Definition putnam_2005_a2_rook_tour
    (n : nat) (p : nat -> putnam_2005_a2_point) : Prop :=
  (forall P : putnam_2005_a2_point,
      putnam_2005_a2_board n P ->
      exists i : nat,
        ((1 <= i <= 3 * n)%nat /\ p i = P) /\
        forall j : nat,
          ((1 <= j <= 3 * n)%nat /\ p j = P) ->
          j = i) /\
  (forall i : nat,
      (1 <= i <= 3 * n - 1)%nat ->
      putnam_2005_a2_unit (p i) (p (i + 1)%nat)) /\
  p 0%nat = (0, 0) /\
  forall i : nat,
    (3 * n < i)%nat ->
    p i = (0, 0).

Definition putnam_2005_a2_qualifying_tour
    (n : nat) (p : nat -> putnam_2005_a2_point) : Prop :=
  putnam_2005_a2_rook_tour n p /\
  p 1%nat = (1, 1) /\
  p (3 * n)%nat = (Z.of_nat n, 1).

Definition putnam_2005_a2_solution (n : nat) : nat :=
  if Nat.eqb n 1%nat
  then 0%nat
  else Nat.pow 2%nat (n - 2)%nat.

Theorem putnam_2005_a2 :
  forall n : nat,
    (0 < n)%nat ->
    putnam_2005_a2_has_cardinality
      putnam_2005_a2_same_path
      (putnam_2005_a2_qualifying_tour n)
      (putnam_2005_a2_solution n).
Admitted.
