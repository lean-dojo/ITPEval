(*
  Statement-only formalization of Logipedia corpus artifact
  fermat.prime_to_not_divides_fact (catalog title
  "fermat.prime_to_not_divides_fact"): if n is less than a natural prime p,
  then p does not divide n factorial. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Definition fermat_divides (n m : nat) : Prop :=
  exists q : nat, m = n * q.

Definition fermat_prime (p : nat) : Prop :=
  1 < p /\
  forall m : nat,
    fermat_divides m p ->
    1 < m ->
    m = p.

Fixpoint fermat_fact (n : nat) : nat :=
  match n with
  | O => 1
  | S k => fermat_fact k * S k
  end.

Theorem prime_to_not_divides_fact :
  forall p : nat,
    fermat_prime p ->
    forall n : nat,
      n < p ->
      ~ fermat_divides p (fermat_fact n).
Admitted.
