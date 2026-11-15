(*
  Statement-only formalization of Thousand Theorems corpus artifact Q3527189
  (thousand-theorems__rocq__Q3527189), "Lattice theorem": Noether's third
  isomorphism theorem for arbitrary groups, identifying (G/N)/(M/N) with G/M
  for normal subgroups N contained in M. This file contains no proof.
*)

Set Universe Polymorphism.
Unset Implicit Arguments.

Record q3527189_group : Type := {
  q3527189_carrier : Type;
  q3527189_one : q3527189_carrier;
  q3527189_mul :
    q3527189_carrier -> q3527189_carrier -> q3527189_carrier;
  q3527189_inv : q3527189_carrier -> q3527189_carrier;
  q3527189_mul_assoc :
    forall x y z : q3527189_carrier,
      q3527189_mul x (q3527189_mul y z) =
      q3527189_mul (q3527189_mul x y) z;
  q3527189_one_mul :
    forall x : q3527189_carrier, q3527189_mul q3527189_one x = x;
  q3527189_mul_one :
    forall x : q3527189_carrier, q3527189_mul x q3527189_one = x;
  q3527189_inv_mul :
    forall x : q3527189_carrier,
      q3527189_mul (q3527189_inv x) x = q3527189_one;
  q3527189_mul_inv :
    forall x : q3527189_carrier,
      q3527189_mul x (q3527189_inv x) = q3527189_one
}.

Arguments q3527189_carrier _ : clear implicits.
Arguments q3527189_one {q}.
Arguments q3527189_mul {q} _ _.
Arguments q3527189_inv {q} _.

Definition q3527189_subgroup (G : q3527189_group) : Type :=
  q3527189_carrier G -> Prop.

Definition q3527189_is_subgroup
    (G : q3527189_group) (S : q3527189_subgroup G) : Prop :=
  S q3527189_one /\
  (forall x y : q3527189_carrier G,
      S x -> S y -> S (q3527189_mul x y)) /\
  (forall x : q3527189_carrier G,
      S x -> S (q3527189_inv x)).

Definition q3527189_subgroup_le
    {G : q3527189_group}
    (A B : q3527189_subgroup G) : Prop :=
  forall x : q3527189_carrier G, A x -> B x.

Definition q3527189_normal_subgroup
    (G : q3527189_group) (N : q3527189_subgroup G) : Prop :=
  q3527189_is_subgroup G N /\
  forall g n : q3527189_carrier G,
    N n ->
    N (q3527189_mul (q3527189_mul g n) (q3527189_inv g)).

Definition q3527189_top_subgroup
    (G : q3527189_group) : q3527189_subgroup G :=
  fun _ => True.

Definition q3527189_group_homomorphism
    (G H : q3527189_group)
    (f : q3527189_carrier G -> q3527189_carrier H) : Prop :=
  f q3527189_one = q3527189_one /\
  forall x y : q3527189_carrier G,
    f (q3527189_mul x y) = q3527189_mul (f x) (f y).

Definition q3527189_quotient_equal
    (G : q3527189_group)
    (N : q3527189_subgroup G)
    (x y : q3527189_carrier G) : Prop :=
  N (q3527189_mul (q3527189_inv x) y).

Definition q3527189_relation_map_isomorphism
    (G H : q3527189_group)
    (A : q3527189_subgroup G)
    (C : q3527189_subgroup H)
    (source_equal :
      q3527189_carrier G -> q3527189_carrier G -> Prop)
    (target_equal :
      q3527189_carrier H -> q3527189_carrier H -> Prop)
    (forward : q3527189_carrier G -> q3527189_carrier H) : Prop :=
  q3527189_group_homomorphism G H forward /\
  (forall x : q3527189_carrier G, A x -> C (forward x)) /\
  (forall x y : q3527189_carrier G,
      A x -> A y -> source_equal x y ->
      target_equal (forward x) (forward y)) /\
  exists backward : q3527189_carrier H -> q3527189_carrier G,
    (forall y : q3527189_carrier H, C y -> A (backward y)) /\
    (forall y z : q3527189_carrier H,
      C y -> C z -> target_equal y z ->
      source_equal (backward y) (backward z)) /\
    (forall x : q3527189_carrier G,
      A x -> source_equal (backward (forward x)) x) /\
    (forall y : q3527189_carrier H,
      C y -> target_equal (forward (backward y)) y).

Definition q3527189_quotient_image_member
    (G : q3527189_group)
    (N M : q3527189_subgroup G)
    (x : q3527189_carrier G) : Prop :=
  exists m : q3527189_carrier G,
    M m /\ q3527189_quotient_equal G N x m.

Definition q3527189_double_quotient_equal
    (G : q3527189_group)
    (N M : q3527189_subgroup G)
    (x y : q3527189_carrier G) : Prop :=
  q3527189_quotient_image_member G N M
    (q3527189_mul (q3527189_inv x) y).

Theorem QuotientGroup_quotientQuotientEquivQuotient :
  forall (G : q3527189_group)
         (N M : q3527189_subgroup G),
    q3527189_normal_subgroup G N ->
    q3527189_normal_subgroup G M ->
    q3527189_subgroup_le N M ->
    q3527189_relation_map_isomorphism
      G G
      (q3527189_top_subgroup G)
      (q3527189_top_subgroup G)
      (q3527189_double_quotient_equal G N M)
      (q3527189_quotient_equal G M)
      (fun x : q3527189_carrier G => x).
Admitted.
