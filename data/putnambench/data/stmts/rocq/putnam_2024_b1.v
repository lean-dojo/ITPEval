(* Statement-only formalization of PutnamBench corpus artifact putnam_2024_b1
   (putnambench__rocq__putnam_2024_b1): classification of positive grid
   dimensions and offsets admitting a nonattacking selection whose entries
   are exactly the integers from 1 through the dimension. This file contains
   no proof. *)

From Stdlib Require Import Arith.PeanoNat Vectors.Fin ZArith.

Definition putnam_2024_b1_index
    {n : nat} (i : Fin.t n) : nat :=
  proj1_sig (Fin.to_nat i).

Definition putnam_2024_b1_grid_value
    {n : nat} (k : nat) (i j : Fin.t n) : Z :=
  (Z.of_nat (S (putnam_2024_b1_index i)) +
   Z.of_nat (S (putnam_2024_b1_index j)) -
   Z.of_nat k)%Z.

Definition putnam_2024_b1_valid (n k : nat) : Prop :=
  (0 < n)%nat /\
  (0 < k)%nat /\
  exists f : Fin.t n -> Fin.t n,
    (forall i j : Fin.t n, f i = f j -> i = j) /\
    forall z : Z,
      (exists i : Fin.t n,
        putnam_2024_b1_grid_value k i (f i) = z) <->
      (1 <= z <= Z.of_nat n)%Z.

Definition putnam_2024_b1_solution (n k : nat) : Prop :=
  exists l : nat,
    n = (2 * l + 1)%nat /\
    k = (l + 1)%nat.

Theorem putnam_2024_b1 :
  forall n k : nat,
    putnam_2024_b1_valid n k <->
    putnam_2024_b1_solution n k.
Admitted.
