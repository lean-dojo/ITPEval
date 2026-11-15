(*
  Statement-only formalization of Thousand Theorems corpus artifact Q2226800
  (thousand-theorems__rocq__Q2226800), "Schur-Zassenhaus theorem": a normal
  subgroup whose order is coprime to its index has a left complement.
  This file contains no proof.
*)

From Stdlib Require Import Lists.List Arith.PeanoNat.

Set Universe Polymorphism.
Set Implicit Arguments.

Record q2226800_group (G : Type) : Type := {
  q2226800_mul : G -> G -> G;
  q2226800_one : G;
  q2226800_inv : G -> G;
  q2226800_mul_assoc :
    forall x y z : G,
      q2226800_mul x (q2226800_mul y z) =
      q2226800_mul (q2226800_mul x y) z;
  q2226800_one_mul :
    forall x : G, q2226800_mul q2226800_one x = x;
  q2226800_mul_one :
    forall x : G, q2226800_mul x q2226800_one = x;
  q2226800_inv_mul :
    forall x : G,
      q2226800_mul (q2226800_inv x) x = q2226800_one;
  q2226800_mul_inv :
    forall x : G,
      q2226800_mul x (q2226800_inv x) = q2226800_one
}.

Arguments q2226800_mul {G} _ _ _.
Arguments q2226800_one {G} _.
Arguments q2226800_inv {G} _ _.

Record q2226800_subgroup
    {G : Type} (grp : q2226800_group G) : Type := {
  q2226800_mem : G -> Prop;
  q2226800_subgroup_one :
    q2226800_mem (q2226800_one grp);
  q2226800_subgroup_mul :
    forall x y : G,
      q2226800_mem x ->
      q2226800_mem y ->
      q2226800_mem (q2226800_mul grp x y);
  q2226800_subgroup_inv :
    forall x : G,
      q2226800_mem x ->
      q2226800_mem (q2226800_inv grp x)
}.

Arguments q2226800_mem {G grp} _ _.

Definition q2226800_normal
    {G : Type}
    {grp : q2226800_group G}
    (N : q2226800_subgroup grp) : Prop :=
  forall g n : G,
    q2226800_mem N n ->
    q2226800_mem N
      (q2226800_mul grp
        (q2226800_mul grp g n)
        (q2226800_inv grp g)).

Definition q2226800_has_finite_subgroup_card
    {G : Type}
    {grp : q2226800_group G}
    (N : q2226800_subgroup grp)
    (n : nat) : Prop :=
  exists xs : list G,
    NoDup xs /\
    (forall x : G, In x xs <-> q2226800_mem N x) /\
    length xs = n.

Definition q2226800_nat_subgroup_card
    {G : Type}
    {grp : q2226800_group G}
    (N : q2226800_subgroup grp)
    (n : nat) : Prop :=
  q2226800_has_finite_subgroup_card N n \/
  (n = 0 /\
   forall m : nat, ~ q2226800_has_finite_subgroup_card N m).

Definition q2226800_same_left_coset
    {G : Type}
    {grp : q2226800_group G}
    (N : q2226800_subgroup grp)
    (x y : G) : Prop :=
  q2226800_mem N
    (q2226800_mul grp (q2226800_inv grp x) y).

Fixpoint q2226800_coset_reps_nodup
    {G : Type}
    {grp : q2226800_group G}
    (N : q2226800_subgroup grp)
    (xs : list G) : Prop :=
  match xs with
  | nil => True
  | x :: rest =>
      (forall y : G,
        In y rest -> ~ q2226800_same_left_coset N x y) /\
      q2226800_coset_reps_nodup N rest
  end.

Definition q2226800_has_finite_index
    {G : Type}
    {grp : q2226800_group G}
    (N : q2226800_subgroup grp)
    (n : nat) : Prop :=
  exists reps : list G,
    q2226800_coset_reps_nodup N reps /\
    (forall x : G,
      exists r : G,
        In r reps /\ q2226800_same_left_coset N x r) /\
    length reps = n.

Definition q2226800_nat_index
    {G : Type}
    {grp : q2226800_group G}
    (N : q2226800_subgroup grp)
    (n : nat) : Prop :=
  q2226800_has_finite_index N n \/
  (n = 0 /\
   forall m : nat, ~ q2226800_has_finite_index N m).

Definition q2226800_order_coprime_to_index
    {G : Type}
    {grp : q2226800_group G}
    (N : q2226800_subgroup grp) : Prop :=
  exists order index : nat,
    q2226800_nat_subgroup_card N order /\
    q2226800_nat_index N index /\
    Nat.gcd order index = 1.

Definition q2226800_is_left_complement
    {G : Type}
    {grp : q2226800_group G}
    (H N : q2226800_subgroup grp) : Prop :=
  forall g : G,
    exists h n : G,
      q2226800_mem H h /\
      q2226800_mem N n /\
      q2226800_mul grp h n = g /\
      forall h' n' : G,
        q2226800_mem H h' ->
        q2226800_mem N n' ->
        q2226800_mul grp h' n' = g ->
        h' = h /\ n' = n.

Theorem Subgroup_exists_left_complement_of_coprime :
  forall (G : Type)
         (grp : q2226800_group G)
         (N : q2226800_subgroup grp),
    q2226800_normal N ->
    q2226800_order_coprime_to_index N ->
    exists H : q2226800_subgroup grp,
      q2226800_is_left_complement H N.
Admitted.
