(*
  Statement-only formalization of Thousand Theorems corpus artifact Q2226786
  (thousand-theorems__rocq__Q2226786), "Sperner's theorem": an antichain of
  subsets of a finite type has cardinality at most the central binomial
  coefficient. This file contains no proof.
*)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition q2226786_is_antichain
    {T : finType} (family : {set {set T}}) : Prop :=
  forall A B : {set T},
    A \in family ->
    B \in family ->
    A \subset B ->
    A = B.

Theorem sperner :
  forall (T : finType) (family : {set {set T}}),
    q2226786_is_antichain family ->
    (#|family| <= binomial #|T| (Nat.div #|T| 2))%nat.
Admitted.
