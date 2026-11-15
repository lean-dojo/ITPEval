(* Statement-only formalization of PutnamBench corpus artifact putnam_1989_b4:
   a countably infinite set has an uncountable family of nonempty subsets
   whose pairwise intersections are finite. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Ensembles Finite_sets.

Definition putnam_1989_b4_countable
    (C : Ensemble (Ensemble nat)) : Prop :=
  exists code : Ensemble nat -> nat,
    forall A B : Ensemble nat,
      In (Ensemble nat) C A ->
      In (Ensemble nat) C B ->
      code A = code B ->
      Same_set nat A B.

Definition putnam_1989_b4_solution : Prop := True.

Theorem putnam_1989_b4 :
  (exists C : Ensemble (Ensemble nat),
      ~ putnam_1989_b4_countable C /\
      (forall R : Ensemble nat,
          In (Ensemble nat) C R ->
          exists n : nat, In nat R n) /\
      (forall A B : Ensemble nat,
          In (Ensemble nat) C A ->
          In (Ensemble nat) C B ->
          ~ Same_set nat A B ->
          Finite nat (Intersection nat A B))) <->
  putnam_1989_b4_solution.
Admitted.
