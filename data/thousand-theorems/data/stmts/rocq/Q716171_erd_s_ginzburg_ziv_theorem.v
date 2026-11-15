(*
  Statement-only formalization of Thousand Theorems corpus artifact Q716171
  (thousand-theorems__rocq__Q716171), "Erdős–Ginzburg–Ziv theorem": among at
  least 2n - 1 indexed residues modulo n, there is an n-element subcollection
  whose sum is zero modulo n. This file contains no proof.
*)

From Stdlib Require Import Lists.List ZArith.

Set Universe Polymorphism.
Set Implicit Arguments.

Record q716171_finset (X : Type) : Type := {
  q716171_elements : list X;
  q716171_elements_nodup : NoDup q716171_elements
}.

Arguments q716171_elements {X} _.

Definition q716171_subset
    {X : Type} (t s : q716171_finset X) : Prop :=
  forall x : X, In x (q716171_elements t) -> In x (q716171_elements s).

Record q716171_zmod (n : nat) : Type := {
  q716171_zmod_rep : Z
}.

Arguments q716171_zmod_rep {n} _.

Definition q716171_zmod_zero (n : nat) : q716171_zmod n :=
  {| q716171_zmod_rep := 0%Z |}.

Definition q716171_zmod_add
    {n : nat} (x y : q716171_zmod n) : q716171_zmod n :=
  {| q716171_zmod_rep :=
       Z.add (q716171_zmod_rep x) (q716171_zmod_rep y) |}.

Definition q716171_zmod_eq
    {n : nat} (x y : q716171_zmod n) : Prop :=
  Z.divide
    (Z.of_nat n)
    (Z.sub (q716171_zmod_rep x) (q716171_zmod_rep y)).

Fixpoint q716171_zmod_sum
    {X : Type} {n : nat}
    (a : X -> q716171_zmod n) (xs : list X) : q716171_zmod n :=
  match xs with
  | nil => q716171_zmod_zero n
  | cons x tail =>
      q716171_zmod_add (a x) (q716171_zmod_sum a tail)
  end.

Module ZMod.

Theorem erdos_ginzburg_ziv :
  forall (I : Type) (n : nat)
         (a : I -> q716171_zmod n) (s : q716171_finset I),
    (2 * n - 1 <= length (q716171_elements s))%nat ->
    exists t : q716171_finset I,
      q716171_subset t s /\
      length (q716171_elements t) = n /\
      q716171_zmod_eq
        (q716171_zmod_sum a (q716171_elements t))
        (q716171_zmod_zero n).
Admitted.

End ZMod.
