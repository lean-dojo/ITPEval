(* Statement-only formalization of PutnamBench corpus artifact putnam_2020_a5:
   the greatest integer having exactly 2020 representations by sets of
   positive indices whose Fibonacci values sum to it. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Sorting.Sorted ZArith.

Open Scope Z_scope.

Fixpoint putnam_2020_a5_fibonacci_pair (n : nat) : nat * nat :=
  match n with
  | O => (O, 1%nat)
  | S k =>
      let '(a, b) := putnam_2020_a5_fibonacci_pair k in
      (b, (a + b)%nat)
  end.

Definition putnam_2020_a5_fibonacci (n : nat) : nat :=
  fst (putnam_2020_a5_fibonacci_pair n).

Definition putnam_2020_a5_canonical_set (indices : list nat) : Prop :=
  StronglySorted Nat.lt indices /\
  Forall (fun k : nat => (0 < k)%nat) indices.

Definition putnam_2020_a5_sum (indices : list nat) : nat :=
  fold_right Nat.add 0%nat (map putnam_2020_a5_fibonacci indices).

Definition putnam_2020_a5_represents
    (n : Z) (indices : list nat) : Prop :=
  putnam_2020_a5_canonical_set indices /\
  Z.of_nat (putnam_2020_a5_sum indices) = n.

Definition putnam_2020_a5_has_cardinality
    {A : Type} (P : A -> Prop) (cardinality : nat) : Prop :=
  exists enumeration : list A,
    NoDup enumeration /\
    length enumeration = cardinality /\
    forall x : A, In x enumeration <-> P x.

Definition putnam_2020_a5_is_greatest
    (P : Z -> Prop) (greatest : Z) : Prop :=
  P greatest /\
  forall n : Z, P n -> n <= greatest.

Definition putnam_2020_a5_solution : Z :=
  Z.of_nat (putnam_2020_a5_fibonacci 4040%nat) - 1.

Theorem putnam_2020_a5 :
  putnam_2020_a5_is_greatest
    (fun n : Z =>
      putnam_2020_a5_has_cardinality
        (putnam_2020_a5_represents n)
        2020%nat)
    putnam_2020_a5_solution.
Admitted.
