(* Statement-only formalization of PutnamBench artifact putnam_1996_b1:
   counting the minimal finite subsets of {1,...,n} that contain their own
   cardinality; this file contains no proof. *)

From Stdlib Require Import List Sorting.Sorted Arith.PeanoNat Finite_sets.

Definition putnam_1996_b1_canonical_set (s : list nat) : Prop :=
  StronglySorted Nat.lt s.

Definition putnam_1996_b1_included
    (s t : list nat) : Prop :=
  forall x : nat, List.In x s -> List.In x t.

Definition putnam_1996_b1_proper_subset
    (s t : list nat) : Prop :=
  putnam_1996_b1_included s t /\
  exists x : nat, List.In x t /\ ~ List.In x s.

Definition putnam_1996_b1_selfish (s : list nat) : Prop :=
  List.In (List.length s) s.

Definition putnam_1996_b1_bounded
    (n : nat) (s : list nat) : Prop :=
  forall x : nat,
    List.In x s ->
    1 <= x /\ x <= n.

Definition putnam_1996_b1_minimal_selfish
    (n : nat) (s : list nat) : Prop :=
  putnam_1996_b1_canonical_set s /\
  putnam_1996_b1_bounded n s /\
  putnam_1996_b1_selfish s /\
  forall ss : list nat,
    putnam_1996_b1_canonical_set ss ->
    putnam_1996_b1_proper_subset ss s ->
    ~ putnam_1996_b1_selfish ss.

Fixpoint putnam_1996_b1_fibonacci_pair (n : nat) : nat * nat :=
  match n with
  | O => (O, 1)
  | S k =>
      let '(a, b) := putnam_1996_b1_fibonacci_pair k in
      (b, a + b)
  end.

Definition putnam_1996_b1_solution (n : nat) : nat :=
  fst (putnam_1996_b1_fibonacci_pair n).

Theorem putnam_1996_b1
    (n : nat)
    (npos : 1 <= n) :
  cardinal
    (list nat)
    (putnam_1996_b1_minimal_selfish n)
    (putnam_1996_b1_solution n).
Admitted.
