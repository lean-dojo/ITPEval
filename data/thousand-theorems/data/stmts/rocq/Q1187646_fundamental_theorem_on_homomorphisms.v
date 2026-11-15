(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1187646
  (thousand-theorems__rocq__Q1187646), "Fundamental theorem on homomorphisms":
  every homomorphism of arbitrary groups induces a group isomorphism from the
  quotient of its domain by its kernel to its range. This file contains no
  proof.
*)

Set Universe Polymorphism.
Unset Implicit Arguments.

Record q1187646_group : Type := {
  q1187646_carrier : Type;
  q1187646_one : q1187646_carrier;
  q1187646_mul :
    q1187646_carrier -> q1187646_carrier -> q1187646_carrier;
  q1187646_inv : q1187646_carrier -> q1187646_carrier;
  q1187646_mul_assoc :
    forall x y z : q1187646_carrier,
      q1187646_mul x (q1187646_mul y z) =
      q1187646_mul (q1187646_mul x y) z;
  q1187646_one_mul :
    forall x : q1187646_carrier, q1187646_mul q1187646_one x = x;
  q1187646_mul_one :
    forall x : q1187646_carrier, q1187646_mul x q1187646_one = x;
  q1187646_inv_mul :
    forall x : q1187646_carrier,
      q1187646_mul (q1187646_inv x) x = q1187646_one;
  q1187646_mul_inv :
    forall x : q1187646_carrier,
      q1187646_mul x (q1187646_inv x) = q1187646_one
}.

Arguments q1187646_carrier _ : clear implicits.
Arguments q1187646_one {q}.
Arguments q1187646_mul {q} _ _.
Arguments q1187646_inv {q} _.

Definition q1187646_subgroup (G : q1187646_group) : Type :=
  q1187646_carrier G -> Prop.

Definition q1187646_group_homomorphism
    (G H : q1187646_group)
    (f : q1187646_carrier G -> q1187646_carrier H) : Prop :=
  f q1187646_one = q1187646_one /\
  forall x y : q1187646_carrier G,
    f (q1187646_mul x y) = q1187646_mul (f x) (f y).

Definition q1187646_kernel
    {G H : q1187646_group}
    (f : q1187646_carrier G -> q1187646_carrier H) :
    q1187646_subgroup G :=
  fun x => f x = q1187646_one.

Definition q1187646_range
    {G H : q1187646_group}
    (f : q1187646_carrier G -> q1187646_carrier H) :
    q1187646_subgroup H :=
  fun y => exists x : q1187646_carrier G, f x = y.

Definition q1187646_top_subgroup
    (G : q1187646_group) : q1187646_subgroup G :=
  fun _ => True.

Definition q1187646_bottom_subgroup
    (G : q1187646_group) : q1187646_subgroup G :=
  fun x => x = q1187646_one.

Definition q1187646_quotient_equal
    (G : q1187646_group)
    (N : q1187646_subgroup G)
    (x y : q1187646_carrier G) : Prop :=
  N (q1187646_mul (q1187646_inv x) y).

Definition q1187646_relation_map_isomorphism
    (G H : q1187646_group)
    (A : q1187646_subgroup G)
    (C : q1187646_subgroup H)
    (source_equal :
      q1187646_carrier G -> q1187646_carrier G -> Prop)
    (target_equal :
      q1187646_carrier H -> q1187646_carrier H -> Prop)
    (forward : q1187646_carrier G -> q1187646_carrier H) : Prop :=
  q1187646_group_homomorphism G H forward /\
  (forall x : q1187646_carrier G, A x -> C (forward x)) /\
  (forall x y : q1187646_carrier G,
      A x -> A y -> source_equal x y ->
      target_equal (forward x) (forward y)) /\
  exists backward : q1187646_carrier H -> q1187646_carrier G,
    (forall y : q1187646_carrier H, C y -> A (backward y)) /\
    (forall y z : q1187646_carrier H,
      C y -> C z -> target_equal y z ->
      source_equal (backward y) (backward z)) /\
    (forall x : q1187646_carrier G,
      A x -> source_equal (backward (forward x)) x) /\
    (forall y : q1187646_carrier H,
      C y -> target_equal (forward (backward y)) y).

Definition q1187646_quotient_map_isomorphism
    (G H : q1187646_group)
    (A B : q1187646_subgroup G)
    (C D : q1187646_subgroup H)
    (forward : q1187646_carrier G -> q1187646_carrier H) : Prop :=
  q1187646_relation_map_isomorphism
    G H A C
    (q1187646_quotient_equal G B)
    (q1187646_quotient_equal H D)
    forward.

Theorem QuotientGroup_quotientKerEquivRange :
  forall (G H : q1187646_group)
         (phi : q1187646_carrier G -> q1187646_carrier H),
    q1187646_group_homomorphism G H phi ->
    q1187646_quotient_map_isomorphism
      G H
      (q1187646_top_subgroup G)
      (q1187646_kernel phi)
      (q1187646_range phi)
      (q1187646_bottom_subgroup H)
      phi.
Admitted.
