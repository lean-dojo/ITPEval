(* Statement-only formalization of PutnamBench corpus artifact putnam_2019_b6:
   existence of an independent perfect dominating set in the integer lattice
   Z^n exactly for positive dimensions. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Vectors.Fin ZArith.

Open Scope Z_scope.

Definition putnam_2019_b6_solution (n : nat) : Prop :=
  (1 <= n)%nat.

Theorem putnam_2019_b6
    (n : nat)
    (neighbors :
      (Fin.t n -> Z) -> (Fin.t n -> Z) -> Prop)
    (neighbors_def :
      forall p q : Fin.t n -> Z,
        neighbors p q <->
        exists i : Fin.t n,
          Z.abs (p i - q i) = 1 /\
          forall j : Fin.t n, j <> i -> p j = q j) :
  ((1 <= n)%nat /\
   exists S : (Fin.t n -> Z) -> Prop,
     (forall p : Fin.t n -> Z,
        S p ->
        forall q : Fin.t n -> Z,
          neighbors p q -> ~ S q) /\
     (forall p : Fin.t n -> Z,
        ~ S p ->
        exists! q : Fin.t n -> Z,
          S q /\ neighbors p q))
  <-> putnam_2019_b6_solution n.
Admitted.
