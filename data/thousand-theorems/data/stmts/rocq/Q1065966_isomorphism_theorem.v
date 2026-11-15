(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1065966
  (thousand-theorems__rocq__Q1065966), "Isomorphism theorem": the first,
  second, and third isomorphism theorems for arbitrary groups and their
  normal-subgroup quotients. This file contains no proof.
*)

Set Universe Polymorphism.
Unset Implicit Arguments.

Record q1065966_group : Type := {
  q1065966_carrier : Type;
  q1065966_one : q1065966_carrier;
  q1065966_mul :
    q1065966_carrier -> q1065966_carrier -> q1065966_carrier;
  q1065966_inv : q1065966_carrier -> q1065966_carrier;
  q1065966_mul_assoc :
    forall x y z : q1065966_carrier,
      q1065966_mul x (q1065966_mul y z) =
      q1065966_mul (q1065966_mul x y) z;
  q1065966_one_mul :
    forall x : q1065966_carrier, q1065966_mul q1065966_one x = x;
  q1065966_mul_one :
    forall x : q1065966_carrier, q1065966_mul x q1065966_one = x;
  q1065966_inv_mul :
    forall x : q1065966_carrier,
      q1065966_mul (q1065966_inv x) x = q1065966_one;
  q1065966_mul_inv :
    forall x : q1065966_carrier,
      q1065966_mul x (q1065966_inv x) = q1065966_one
}.

Arguments q1065966_carrier _ : clear implicits.
Arguments q1065966_one {q}.
Arguments q1065966_mul {q} _ _.
Arguments q1065966_inv {q} _.

Definition q1065966_subgroup (G : q1065966_group) : Type :=
  q1065966_carrier G -> Prop.

Definition q1065966_is_subgroup
    (G : q1065966_group) (S : q1065966_subgroup G) : Prop :=
  S q1065966_one /\
  (forall x y : q1065966_carrier G,
      S x -> S y -> S (q1065966_mul x y)) /\
  (forall x : q1065966_carrier G,
      S x -> S (q1065966_inv x)).

Definition q1065966_subgroup_le
    {G : q1065966_group}
    (A B : q1065966_subgroup G) : Prop :=
  forall x : q1065966_carrier G, A x -> B x.

Definition q1065966_normal_subgroup
    (G : q1065966_group) (N : q1065966_subgroup G) : Prop :=
  q1065966_is_subgroup G N /\
  forall g n : q1065966_carrier G,
    N n ->
    N (q1065966_mul (q1065966_mul g n) (q1065966_inv g)).

Definition q1065966_top_subgroup
    (G : q1065966_group) : q1065966_subgroup G :=
  fun _ => True.

Definition q1065966_bottom_subgroup
    (G : q1065966_group) : q1065966_subgroup G :=
  fun x => x = q1065966_one.

Definition q1065966_subgroup_inf
    {G : q1065966_group}
    (A B : q1065966_subgroup G) : q1065966_subgroup G :=
  fun x => A x /\ B x.

Definition q1065966_subgroup_join
    {G : q1065966_group}
    (A B : q1065966_subgroup G) : q1065966_subgroup G :=
  fun x =>
    forall K : q1065966_subgroup G,
      q1065966_is_subgroup G K ->
      q1065966_subgroup_le A K ->
      q1065966_subgroup_le B K ->
      K x.

Definition q1065966_group_homomorphism
    (G H : q1065966_group)
    (f : q1065966_carrier G -> q1065966_carrier H) : Prop :=
  f q1065966_one = q1065966_one /\
  forall x y : q1065966_carrier G,
    f (q1065966_mul x y) = q1065966_mul (f x) (f y).

Definition q1065966_kernel
    {G H : q1065966_group}
    (f : q1065966_carrier G -> q1065966_carrier H) :
    q1065966_subgroup G :=
  fun x => f x = q1065966_one.

Definition q1065966_range
    {G H : q1065966_group}
    (f : q1065966_carrier G -> q1065966_carrier H) :
    q1065966_subgroup H :=
  fun y => exists x : q1065966_carrier G, f x = y.

Definition q1065966_quotient_equal
    (G : q1065966_group)
    (N : q1065966_subgroup G)
    (x y : q1065966_carrier G) : Prop :=
  N (q1065966_mul (q1065966_inv x) y).

Definition q1065966_relation_map_isomorphism
    (G H : q1065966_group)
    (A : q1065966_subgroup G)
    (C : q1065966_subgroup H)
    (source_equal :
      q1065966_carrier G -> q1065966_carrier G -> Prop)
    (target_equal :
      q1065966_carrier H -> q1065966_carrier H -> Prop)
    (forward : q1065966_carrier G -> q1065966_carrier H) : Prop :=
  q1065966_group_homomorphism G H forward /\
  (forall x : q1065966_carrier G, A x -> C (forward x)) /\
  (forall x y : q1065966_carrier G,
      A x -> A y -> source_equal x y ->
      target_equal (forward x) (forward y)) /\
  exists backward : q1065966_carrier H -> q1065966_carrier G,
    (forall y : q1065966_carrier H, C y -> A (backward y)) /\
    (forall y z : q1065966_carrier H,
      C y -> C z -> target_equal y z ->
      source_equal (backward y) (backward z)) /\
    (forall x : q1065966_carrier G,
      A x -> source_equal (backward (forward x)) x) /\
    (forall y : q1065966_carrier H,
      C y -> target_equal (forward (backward y)) y).

Definition q1065966_quotient_map_isomorphism
    (G H : q1065966_group)
    (A B : q1065966_subgroup G)
    (C D : q1065966_subgroup H)
    (forward : q1065966_carrier G -> q1065966_carrier H) : Prop :=
  q1065966_relation_map_isomorphism
    G H A C
    (q1065966_quotient_equal G B)
    (q1065966_quotient_equal H D)
    forward.

Definition q1065966_quotient_image_member
    (G : q1065966_group)
    (N M : q1065966_subgroup G)
    (x : q1065966_carrier G) : Prop :=
  exists m : q1065966_carrier G,
    M m /\ q1065966_quotient_equal G N x m.

Definition q1065966_double_quotient_equal
    (G : q1065966_group)
    (N M : q1065966_subgroup G)
    (x y : q1065966_carrier G) : Prop :=
  q1065966_quotient_image_member G N M
    (q1065966_mul (q1065966_inv x) y).

Theorem QuotientGroup_quotientKerEquivRange :
  forall (G H : q1065966_group)
         (phi : q1065966_carrier G -> q1065966_carrier H),
    q1065966_group_homomorphism G H phi ->
    q1065966_quotient_map_isomorphism
      G H
      (q1065966_top_subgroup G)
      (q1065966_kernel phi)
      (q1065966_range phi)
      (q1065966_bottom_subgroup H)
      phi.
Admitted.

Theorem QuotientGroup_quotientInfEquivProdNormalQuotient :
  forall (G : q1065966_group)
         (H N : q1065966_subgroup G),
    q1065966_is_subgroup G H ->
    q1065966_normal_subgroup G N ->
    q1065966_quotient_map_isomorphism
      G G
      H
      (q1065966_subgroup_inf H N)
      (q1065966_subgroup_join H N)
      N
      (fun x : q1065966_carrier G => x).
Admitted.

Theorem QuotientGroup_quotientQuotientEquivQuotient :
  forall (G : q1065966_group)
         (N M : q1065966_subgroup G),
    q1065966_normal_subgroup G N ->
    q1065966_normal_subgroup G M ->
    q1065966_subgroup_le N M ->
    q1065966_relation_map_isomorphism
      G G
      (q1065966_top_subgroup G)
      (q1065966_top_subgroup G)
      (q1065966_double_quotient_equal G N M)
      (q1065966_quotient_equal G M)
      (fun x : q1065966_carrier G => x).
Admitted.
