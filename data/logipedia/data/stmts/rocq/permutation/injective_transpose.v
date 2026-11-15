(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.injective_transpose (catalog title
  "permutation.injective_transpose"): every transposition of two natural
  numbers is an injective function on the natural numbers. This file contains
  no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Definition logipedia_relations_injective
    (A B : Type) (f : A -> B) : Prop :=
  forall x y : A, f x = f y -> x = y.

Definition logipedia_permutation_transpose
    (i j k : nat) : nat :=
  if Nat.eqb k i then j
  else if Nat.eqb k j then i
  else k.

Theorem injective_transpose :
  forall i j : nat,
    logipedia_relations_injective
      nat nat (logipedia_permutation_transpose i j).
Admitted.
