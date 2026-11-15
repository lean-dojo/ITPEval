(*
  Statement-only formalization of Thousand Theorems corpus artifact Q718875
  (thousand-theorems__rocq__Q718875), "Erdős–Ko–Rado theorem": an
  intersecting family of r-element subsets of a finite ordinal of size n,
  with r at most n divided by two, has cardinality at most the binomial
  coefficient choosing r - 1 elements from n - 1. This file contains no proof.
*)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition q718875_uniform
    {n : nat} (family : {set {set 'I_n}}) (r : nat) : Prop :=
  forall A : {set 'I_n},
    A \in family ->
    #|A| = r.

Definition q718875_intersecting
    {n : nat} (family : {set {set 'I_n}}) : Prop :=
  forall A B : {set 'I_n},
    A \in family ->
    B \in family ->
    exists x : 'I_n, x \in A /\ x \in B.

Theorem erdos_ko_rado :
  forall (n r : nat) (family : {set {set 'I_n}}),
    q718875_intersecting family ->
    q718875_uniform family r ->
    (r <= Nat.div n 2)%nat ->
    (#|family| <= binomial (n - 1) (r - 1))%nat.
Admitted.
