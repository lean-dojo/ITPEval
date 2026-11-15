(*
  Statement-only extraction of the quadratic reciprocity theorem from the
  Rocq Reciprocity development. For distinct odd primes p and q, the product
  of their Legendre symbols has the standard parity sign. This file contains
  no proof.
*)

Require Import ZArith.
Require Import Zpow_facts.
Require Import Znumtheory.
Require Import Reciprocity.Reciprocity.Finite.
Require Import Reciprocity.Reciprocity.Accumulation.

Section Quadratic_reciprocity.

Variable p q : Z.

Hypothesis p_prime : prime p.
Hypothesis q_prime : prime q.
Hypothesis p_odd : p mod 2 = 1.
Hypothesis q_odd : q mod 2 = 1.
Hypothesis p_not_q : p <> q.

Theorem Quadratic_reciprocity :
  (legendre p q) * (legendre q p) =
    (-1) ^ (((p - 1) / 2) * ((q - 1) / 2)).
Proof.
Admitted.

End Quadratic_reciprocity.
