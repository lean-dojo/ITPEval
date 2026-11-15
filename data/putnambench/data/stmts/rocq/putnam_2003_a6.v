(* Statement-only formalization of PutnamBench corpus artifact putnam_2003_a6:
   a partition of the nonnegative integers into two sets with equal numbers
   of ordered distinct-pair representations of every sum; this file contains
   no proof. *)

From Stdlib Require Import Arith.PeanoNat Lists.List ClassicalDescription.

Definition putnam_2003_a6_pairs (n : nat) : list (nat * nat) :=
  flat_map
    (fun s1 : nat =>
      map (fun s2 : nat => (s1, s2)) (seq 0 (Nat.succ n)))
    (seq 0 (Nat.succ n)).

Definition putnam_2003_a6_representation_pairb
    (S : nat -> Prop) (n : nat) (pair : nat * nat) : bool :=
  if excluded_middle_informative
       (S (fst pair) /\
        S (snd pair) /\
        fst pair <> snd pair /\
        (fst pair + snd pair = n)%nat)
  then true
  else false.

Definition putnam_2003_a6_representation_count
    (S : nat -> Prop) (n : nat) : nat :=
  length
    (filter
      (putnam_2003_a6_representation_pairb S n)
      (putnam_2003_a6_pairs n)).

Definition putnam_2003_a6_solution : Prop := True.

Theorem putnam_2003_a6 :
  (exists A B : nat -> Prop,
      (forall n : nat, A n \/ B n) /\
      (forall n : nat, ~ (A n /\ B n)) /\
      (forall n : nat,
        putnam_2003_a6_representation_count A n =
        putnam_2003_a6_representation_count B n))
  <-> putnam_2003_a6_solution.
Admitted.
