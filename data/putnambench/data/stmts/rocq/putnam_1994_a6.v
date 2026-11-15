(* Statement-only formalization of PutnamBench corpus artifact putnam_1994_a6:
   ten permutations of the integers whose finite compositions act transitively
   have at most 512 optional ordered compositions stabilizing any nonempty
   finite set of integers. This file contains no proof. *)

From Stdlib Require Import Lists.List ZArith Arith.PeanoNat.

Open Scope Z_scope.

Inductive putnam_1994_a6_index : Type :=
| putnam_1994_a6_i0
| putnam_1994_a6_i1
| putnam_1994_a6_i2
| putnam_1994_a6_i3
| putnam_1994_a6_i4
| putnam_1994_a6_i5
| putnam_1994_a6_i6
| putnam_1994_a6_i7
| putnam_1994_a6_i8
| putnam_1994_a6_i9.

Definition putnam_1994_a6_bijective (h : Z -> Z) : Prop :=
  (forall x y : Z, h x = h y -> x = y) /\
  (forall y : Z, exists x : Z, h x = y).

Fixpoint putnam_1994_a6_apply_word
    (f : putnam_1994_a6_index -> Z -> Z)
    (word : list putnam_1994_a6_index)
    (x : Z) : Z :=
  match word with
  | nil => x
  | i :: rest => f i (putnam_1994_a6_apply_word f rest x)
  end.

Definition putnam_1994_a6_apply_optional
    (choice : bool) (h : Z -> Z) (x : Z) : Z :=
  if choice then h x else x.

Definition putnam_1994_a6_optional_composition
    (f : putnam_1994_a6_index -> Z -> Z)
    (e : putnam_1994_a6_index -> bool) : Z -> Z :=
  fun x : Z =>
    putnam_1994_a6_apply_optional
      (e putnam_1994_a6_i0) (f putnam_1994_a6_i0)
      (putnam_1994_a6_apply_optional
        (e putnam_1994_a6_i1) (f putnam_1994_a6_i1)
        (putnam_1994_a6_apply_optional
          (e putnam_1994_a6_i2) (f putnam_1994_a6_i2)
          (putnam_1994_a6_apply_optional
            (e putnam_1994_a6_i3) (f putnam_1994_a6_i3)
            (putnam_1994_a6_apply_optional
              (e putnam_1994_a6_i4) (f putnam_1994_a6_i4)
              (putnam_1994_a6_apply_optional
                (e putnam_1994_a6_i5) (f putnam_1994_a6_i5)
                (putnam_1994_a6_apply_optional
                  (e putnam_1994_a6_i6) (f putnam_1994_a6_i6)
                  (putnam_1994_a6_apply_optional
                    (e putnam_1994_a6_i7) (f putnam_1994_a6_i7)
                    (putnam_1994_a6_apply_optional
                      (e putnam_1994_a6_i8) (f putnam_1994_a6_i8)
                      (putnam_1994_a6_apply_optional
                        (e putnam_1994_a6_i9) (f putnam_1994_a6_i9)
                        x))))))))).

Definition putnam_1994_a6_finite_set (A : Z -> Prop) : Prop :=
  exists enumeration : list Z,
    NoDup enumeration /\
    forall x : Z, In x enumeration <-> A x.

Definition putnam_1994_a6_nonempty_set (A : Z -> Prop) : Prop :=
  exists x : Z, A x.

Definition putnam_1994_a6_image
    (g : Z -> Z) (A : Z -> Prop) : Z -> Prop :=
  fun y : Z => exists x : Z, A x /\ y = g x.

Definition putnam_1994_a6_maps_set_to_itself
    (g : Z -> Z) (A : Z -> Prop) : Prop :=
  forall y : Z,
    putnam_1994_a6_image g A y <-> A y.

Definition putnam_1994_a6_has_at_most_cardinality
    {X : Type} (P : X -> Prop) (bound : nat) : Prop :=
  exists enumeration : list X,
    NoDup enumeration /\
    (length enumeration <= bound)%nat /\
    forall x : X, In x enumeration <-> P x.

Theorem putnam_1994_a6
    (f : putnam_1994_a6_index -> Z -> Z)
    (hfperm :
      forall i : putnam_1994_a6_index,
        putnam_1994_a6_bijective (f i))
    (hfcomp :
      forall n : Z,
        exists word : list putnam_1994_a6_index,
          word <> nil /\
          putnam_1994_a6_apply_word f word 0 = n) :
  forall A : Z -> Prop,
    putnam_1994_a6_finite_set A ->
    putnam_1994_a6_nonempty_set A ->
    putnam_1994_a6_has_at_most_cardinality
      (fun g : Z -> Z =>
        (exists e : putnam_1994_a6_index -> bool,
          g = putnam_1994_a6_optional_composition f e) /\
        putnam_1994_a6_maps_set_to_itself g A)
      512%nat.
Admitted.
