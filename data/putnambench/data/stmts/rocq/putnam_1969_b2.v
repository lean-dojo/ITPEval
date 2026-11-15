(* Statement-only formalization of PutnamBench artifact putnam_1969_b2:
   finite groups cannot be unions of two proper subgroups, and the analogous
   assertion for three proper subgroups is false. This file contains no proof. *)

From Stdlib Require Import Lists.List Arith.PeanoNat.

Record group_structure (G : Type) : Type := {
  group_mul : G -> G -> G;
  group_one : G;
  group_inv : G -> G;
  group_assoc :
    forall x y z : G,
      group_mul x (group_mul y z) = group_mul (group_mul x y) z;
  group_left_identity :
    forall x : G, group_mul group_one x = x;
  group_right_identity :
    forall x : G, group_mul x group_one = x;
  group_left_inverse :
    forall x : G, group_mul (group_inv x) x = group_one;
  group_right_inverse :
    forall x : G, group_mul x (group_inv x) = group_one
}.

Arguments group_mul {G} _ _ _.
Arguments group_one {G} _.
Arguments group_inv {G} _ _.

Definition finite_type (G : Type) : Prop :=
  exists enumeration : list G,
    forall x : G, List.In x enumeration.

Record finite_index (n : nat) : Type := {
  index_value : nat;
  index_bound : index_value < n
}.

Definition is_subgroup
    {G : Type}
    (grp : group_structure G)
    (H : G -> Prop) : Prop :=
  H (group_one grp) /\
  (forall x y : G,
    H x ->
    H y ->
    H (group_mul grp x y)) /\
  (forall x : G,
    H x ->
    H (group_inv grp x)).

Definition putnam_1969_b2_property (n : nat) : Prop :=
  forall
    (G : Type)
    (grp : group_structure G),
    finite_type G ->
    forall H : finite_index n -> G -> Prop,
      (forall i : finite_index n,
        is_subgroup grp (H i) /\
        ~ (forall x : G, H i x)) ->
      ~ (forall x : G,
          exists i : finite_index n, H i x).

Definition putnam_1969_b2_solution : Prop := False.

Theorem putnam_1969_b2
    (P : nat -> Prop)
    (P_def :
      forall n : nat,
        P n <-> putnam_1969_b2_property n) :
  P 2 /\ (P 3 <-> putnam_1969_b2_solution).
Admitted.
