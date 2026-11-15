(*
  Statement-only formalization of Thousand Theorems corpus artifact Q3527102
  (thousand-theorems__rocq__Q3527102), "Kruskal-Katona theorem": among
  uniform families of subsets of a finite ordinal, a colex initial segment
  has a lower shadow no larger than that of any family of at least the same
  cardinality. This file contains no proof.
*)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition q3527102_uniform
    {n : nat} (family : {set {set 'I_n}}) (r : nat) : Prop :=
  forall A : {set 'I_n},
    A \in family ->
    #|A| = r.

Definition q3527102_colex_lt
    {n : nat} (A B : {set 'I_n}) : Prop :=
  A <> B /\
  forall a : 'I_n,
    a \in A ->
    a \notin B ->
    exists b : 'I_n,
      b \in B /\
      b \notin A /\
      (val a <= val b)%nat.

Definition q3527102_is_initial_segment
    {n : nat} (family : {set {set 'I_n}}) (r : nat) : Prop :=
  q3527102_uniform family r /\
  forall A B : {set 'I_n},
    A \in family ->
    q3527102_colex_lt B A /\ #|B| = r ->
    B \in family.

Definition q3527102_shadow
    {n : nat} (family : {set {set 'I_n}}) : {set {set 'I_n}} :=
  [set B : {set 'I_n} |
    [exists A : {set 'I_n},
      (A \in family) &&
      [exists x : 'I_n,
        (x \in A) && (B == A :\ x)]]].

Theorem kruskal_katona :
  forall (n r : nat) (family initial : {set {set 'I_n}}),
    q3527102_uniform family r ->
    (#|initial| <= #|family|)%nat ->
    q3527102_is_initial_segment initial r ->
    (#|q3527102_shadow initial| <= #|q3527102_shadow family|)%nat.
Admitted.
