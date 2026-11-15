(* Statement-only formalization of PutnamBench corpus artifact putnam_2009_b3:
   characterization of the positive indices where the second difference of
   the number of average-closed subsets equals one. This file contains no proof. *)

From Stdlib Require Import ZArith List Ensembles.

Open Scope Z_scope.

Definition putnam_2009_b3_mediocre
    (n : Z) (S : Ensemble Z) : Prop :=
  (forall x : Z, In Z S x -> 1 <= x <= n) /\
  forall a b q : Z,
    In Z S a ->
    In Z S b ->
    a + b = 2 * q ->
    In Z S q.

Definition putnam_2009_b3_has_integer_cardinality
    (P : Ensemble Z -> Prop) (cardinality : Z) : Prop :=
  exists enumeration : list (Ensemble Z),
    List.NoDup enumeration /\
    (forall S T : Ensemble Z,
      List.In S enumeration ->
      List.In T enumeration ->
      Same_set Z S T ->
      S = T) /\
    (forall S : Ensemble Z,
      P S <->
      exists T : Ensemble Z,
        List.In T enumeration /\ Same_set Z S T) /\
    cardinality = Z.of_nat (List.length enumeration).

Theorem putnam_2009_b3
    (A : Z -> Z)
    (hA :
      forall n : Z,
        putnam_2009_b3_has_integer_cardinality
          (putnam_2009_b3_mediocre n)
          (A n)) :
  forall n : Z,
    (0 < n /\
      A (n + 2) - 2 * A (n + 1) + A n = 1) <->
    exists k : nat,
      (1 <= k)%nat /\
      n = Z.of_nat (Nat.pow 2 k) - 1.
Admitted.
