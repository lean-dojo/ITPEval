(*
  Statement-only formalization of Thousand Theorems corpus artifact Q764287
  (thousand-theorems__rocq__Q764287), "Van der Waerden's theorem": every
  finite coloring of a commutative additive monoid has a monochromatic
  homothetic copy of each finite subset. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat Lists.List.

Set Universe Polymorphism.
Set Implicit Arguments.

Record q764287_add_comm_monoid (M : Type) : Type := {
  q764287_zero : M;
  q764287_add : M -> M -> M;
  q764287_add_assoc :
    forall x y z : M,
      q764287_add x (q764287_add y z) =
      q764287_add (q764287_add x y) z;
  q764287_zero_add :
    forall x : M, q764287_add q764287_zero x = x;
  q764287_add_zero :
    forall x : M, q764287_add x q764287_zero = x;
  q764287_add_comm :
    forall x y : M, q764287_add x y = q764287_add y x
}.

Arguments q764287_zero {M} _.
Arguments q764287_add {M} _ _ _.

Record q764287_finset (X : Type) : Type := {
  q764287_elements : list X;
  q764287_elements_nodup : NoDup q764287_elements
}.

Arguments q764287_elements {X} _.

Definition q764287_mem
    {X : Type} (x : X) (s : q764287_finset X) : Prop :=
  In x (q764287_elements s).

Record q764287_finite_type (X : Type) : Type := {
  q764287_enumeration : list X;
  q764287_enumeration_complete :
    forall x : X, In x q764287_enumeration
}.

Fixpoint q764287_nat_smul
    {M : Type} (A : q764287_add_comm_monoid M)
    (n : nat) (x : M) : M :=
  match n with
  | O => q764287_zero A
  | S k => q764287_add A x (q764287_nat_smul A k x)
  end.

Theorem Combinatorics_exists_mono_homothetic_copy :
  forall (M K : Type)
         (A : q764287_add_comm_monoid M)
         (S : q764287_finset M)
         (_ : q764287_finite_type K)
         (C : M -> K),
    exists a : nat,
      (0 < a)%nat /\
      exists (b : M) (c : K),
        forall s : M,
          q764287_mem s S ->
          C (q764287_add A (q764287_nat_smul A a s) b) = c.
Admitted.
