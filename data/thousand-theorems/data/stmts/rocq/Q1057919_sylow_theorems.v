(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1057919
  (thousand-theorems__rocq__Q1057919), "Sylow theorems": prime-power
  subgroups, conjugacy of Sylow p-subgroups when their collection is finite,
  the Sylow count divides a Sylow subgroup's index and is congruent to one
  modulo p. This file contains no proof.
*)

From Stdlib Require Import List Arith PeanoNat.

Set Universe Polymorphism.
Set Implicit Arguments.

Record q1057919_group (G : Type) : Type := {
  q1057919_mul : G -> G -> G;
  q1057919_one : G;
  q1057919_inv : G -> G;
  q1057919_mul_assoc :
    forall x y z : G,
      q1057919_mul x (q1057919_mul y z) =
      q1057919_mul (q1057919_mul x y) z;
  q1057919_one_mul :
    forall x : G, q1057919_mul q1057919_one x = x;
  q1057919_mul_one :
    forall x : G, q1057919_mul x q1057919_one = x;
  q1057919_inv_mul :
    forall x : G, q1057919_mul (q1057919_inv x) x = q1057919_one;
  q1057919_mul_inv :
    forall x : G, q1057919_mul x (q1057919_inv x) = q1057919_one
}.

Arguments q1057919_mul {G} _ _ _.
Arguments q1057919_one {G} _.
Arguments q1057919_inv {G} _ _.

Fixpoint q1057919_pow
    {G : Type} (grp : q1057919_group G) (x : G) (n : nat) : G :=
  match n with
  | 0 => q1057919_one grp
  | S k => q1057919_mul grp x (q1057919_pow grp x k)
  end.

Record q1057919_subgroup
    {G : Type} (grp : q1057919_group G) : Type := {
  q1057919_mem : G -> Prop;
  q1057919_subgroup_one :
    q1057919_mem (q1057919_one grp);
  q1057919_subgroup_mul :
    forall x y : G,
      q1057919_mem x ->
      q1057919_mem y ->
      q1057919_mem (q1057919_mul grp x y);
  q1057919_subgroup_inv :
    forall x : G,
      q1057919_mem x ->
      q1057919_mem (q1057919_inv grp x)
}.

Arguments q1057919_mem {G grp} _ _.

Definition q1057919_subgroup_included
    {G : Type}
    {grp : q1057919_group G}
    (H K : q1057919_subgroup grp) : Prop :=
  forall x : G, q1057919_mem H x -> q1057919_mem K x.

Definition q1057919_subgroup_equiv
    {G : Type}
    {grp : q1057919_group G}
    (H K : q1057919_subgroup grp) : Prop :=
  forall x : G, q1057919_mem H x <-> q1057919_mem K x.

Definition q1057919_prime (p : nat) : Prop :=
  (1 < p)%nat /\
  forall d : nat, Nat.divide d p -> d = 1 \/ d = p.

Definition q1057919_is_p_group
    {G : Type}
    {grp : q1057919_group G}
    (p : nat)
    (H : q1057919_subgroup grp) : Prop :=
  forall x : G,
    q1057919_mem H x ->
    exists k : nat,
      q1057919_pow grp x (Nat.pow p k) = q1057919_one grp.

Definition q1057919_is_sylow
    {G : Type}
    {grp : q1057919_group G}
    (p : nat)
    (P : q1057919_subgroup grp) : Prop :=
  q1057919_is_p_group p P /\
  forall Q : q1057919_subgroup grp,
    q1057919_is_p_group p Q ->
    q1057919_subgroup_included P Q ->
    q1057919_subgroup_equiv P Q.

Definition q1057919_conjugate_subgroups
    {G : Type}
    {grp : q1057919_group G}
    (P Q : q1057919_subgroup grp) : Prop :=
  exists g : G,
    forall x : G,
      q1057919_mem Q x <->
      q1057919_mem P
        (q1057919_mul grp
          (q1057919_inv grp g)
          (q1057919_mul grp x g)).

Record q1057919_finite_type (A : Type) : Type := {
  q1057919_enum : list A;
  q1057919_enum_nodup : NoDup q1057919_enum;
  q1057919_enum_complete :
    forall x : A, In x q1057919_enum
}.

Arguments q1057919_enum {A} _.

Definition q1057919_finite_card
    {A : Type} (F : q1057919_finite_type A) : nat :=
  length (q1057919_enum F).

Definition q1057919_subgroup_card
    {G : Type}
    {grp : q1057919_group G}
    (H : q1057919_subgroup grp)
    (n : nat) : Prop :=
  exists xs : list G,
    NoDup xs /\
    (forall x : G, In x xs <-> q1057919_mem H x) /\
    length xs = n.

Fixpoint q1057919_sylow_enum_nodup
    {G : Type}
    {grp : q1057919_group G}
    (xs : list (q1057919_subgroup grp)) : Prop :=
  match xs with
  | nil => True
  | P :: rest =>
      (forall Q : q1057919_subgroup grp,
        In Q rest -> ~ q1057919_subgroup_equiv P Q) /\
      q1057919_sylow_enum_nodup rest
  end.

Record q1057919_finite_sylows
    {G : Type}
    (grp : q1057919_group G)
    (p : nat) : Type := {
  q1057919_sylow_enum : list (q1057919_subgroup grp);
  q1057919_sylow_enum_distinct :
    q1057919_sylow_enum_nodup q1057919_sylow_enum;
  q1057919_sylow_enum_sound :
    forall P : q1057919_subgroup grp,
      In P q1057919_sylow_enum ->
      q1057919_is_sylow p P;
  q1057919_sylow_enum_complete :
    forall P : q1057919_subgroup grp,
      q1057919_is_sylow p P ->
      exists Q : q1057919_subgroup grp,
        In Q q1057919_sylow_enum /\
        q1057919_subgroup_equiv P Q
}.

Arguments q1057919_sylow_enum {G grp p} _.

Definition q1057919_sylow_card
    {G : Type}
    {grp : q1057919_group G}
    {p : nat}
    (F : q1057919_finite_sylows grp p) : nat :=
  length (q1057919_sylow_enum F).

Definition q1057919_same_left_coset
    {G : Type}
    {grp : q1057919_group G}
    (H : q1057919_subgroup grp)
    (x y : G) : Prop :=
  q1057919_mem H
    (q1057919_mul grp (q1057919_inv grp x) y).

Fixpoint q1057919_coset_reps_nodup
    {G : Type}
    {grp : q1057919_group G}
    (H : q1057919_subgroup grp)
    (xs : list G) : Prop :=
  match xs with
  | nil => True
  | x :: rest =>
      (forall y : G,
        In y rest -> ~ q1057919_same_left_coset H x y) /\
      q1057919_coset_reps_nodup H rest
  end.

Definition q1057919_has_finite_index_card
    {G : Type}
    {grp : q1057919_group G}
    (H : q1057919_subgroup grp)
    (n : nat) : Prop :=
  exists reps : list G,
    q1057919_coset_reps_nodup H reps /\
    (forall x : G,
      exists r : G,
        In r reps /\ q1057919_same_left_coset H x r) /\
    length reps = n.

Definition q1057919_nat_index
    {G : Type}
    {grp : q1057919_group G}
    (H : q1057919_subgroup grp)
    (n : nat) : Prop :=
  q1057919_has_finite_index_card H n \/
  (n = 0 /\
   forall m : nat, ~ q1057919_has_finite_index_card H m).

Definition q1057919_mod_eq
    (modulus a b : nat) : Prop :=
  Nat.modulo a modulus = Nat.modulo b modulus.

Theorem Sylow_exists_subgroup_card_pow_prime :
  forall (G : Type)
         (grp : q1057919_group G)
         (F : q1057919_finite_type G)
         (p n : nat),
    q1057919_prime p ->
    Nat.divide (Nat.pow p n) (q1057919_finite_card F) ->
    exists K : q1057919_subgroup grp,
      q1057919_subgroup_card K (Nat.pow p n).
Admitted.

Theorem Sylow_isPretransitive_of_finite :
  forall (G : Type)
         (grp : q1057919_group G)
         (p : nat)
         (F : q1057919_finite_sylows grp p),
    q1057919_prime p ->
    forall P Q : q1057919_subgroup grp,
      q1057919_is_sylow p P ->
      q1057919_is_sylow p Q ->
      q1057919_conjugate_subgroups P Q.
Admitted.

Theorem Sylow_card_dvd_index :
  forall (G : Type)
         (grp : q1057919_group G)
         (p : nat)
         (F : q1057919_finite_sylows grp p)
         (P : q1057919_subgroup grp)
         (index : nat),
    q1057919_prime p ->
    q1057919_is_sylow p P ->
    q1057919_nat_index P index ->
    Nat.divide (q1057919_sylow_card F) index.
Admitted.

Theorem card_sylow_modEq_one :
  forall (G : Type)
         (grp : q1057919_group G)
         (p : nat)
         (F : q1057919_finite_sylows grp p),
    q1057919_prime p ->
    q1057919_mod_eq p (q1057919_sylow_card F) 1.
Admitted.
