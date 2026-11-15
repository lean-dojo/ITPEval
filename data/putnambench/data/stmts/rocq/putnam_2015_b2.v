(* Statement-only formalization of PutnamBench corpus artifact putnam_2015_b2:
   the iterative deletion of the three least positive integers remaining and
   their sum eventually produces a sum ending in 2015; this file contains no
   proof. *)

From Stdlib Require Import Arith.PeanoNat.

Definition putnam_2015_b2_set : Type := nat -> Prop.

Record putnam_2015_b2_triple : Type := {
  putnam_2015_b2_first : nat;
  putnam_2015_b2_second : nat;
  putnam_2015_b2_third : nat
}.

Definition putnam_2015_b2_has_at_least_three
    (S : putnam_2015_b2_set) : Prop :=
  exists a b c : nat,
    S a /\
    S b /\
    S c /\
    a <> b /\
    a <> c /\
    b <> c.

Definition putnam_2015_b2_is_minimum
    (S : putnam_2015_b2_set) (m : nat) : Prop :=
  S m /\ forall x : nat, S x -> (m <= x)%nat.

Definition putnam_2015_b2_remove_one
    (S : putnam_2015_b2_set) (a : nat) : putnam_2015_b2_set :=
  fun x : nat => S x /\ x <> a.

Definition putnam_2015_b2_remove_two
    (S : putnam_2015_b2_set) (a b : nat) : putnam_2015_b2_set :=
  fun x : nat => S x /\ x <> a /\ x <> b.

Definition putnam_2015_b2_remove_four
    (S : putnam_2015_b2_set) (a b c d : nat) :
    putnam_2015_b2_set :=
  fun x : nat =>
    S x /\ x <> a /\ x <> b /\ x <> c /\ x <> d.

Definition putnam_2015_b2_solution : Prop := True.

Theorem putnam_2015_b2
    (sets : nat -> putnam_2015_b2_set)
    (Smin3 : putnam_2015_b2_set -> putnam_2015_b2_triple)
    (sums : nat -> nat)
    (hsets0 :
      forall x : nat, sets 0 x <-> (1 <= x)%nat)
    (hmin3 :
      forall S : putnam_2015_b2_set,
        putnam_2015_b2_has_at_least_three S ->
        putnam_2015_b2_is_minimum
          S
          (putnam_2015_b2_first (Smin3 S)) /\
        putnam_2015_b2_is_minimum
          (putnam_2015_b2_remove_one
            S
            (putnam_2015_b2_first (Smin3 S)))
          (putnam_2015_b2_second (Smin3 S)) /\
        putnam_2015_b2_is_minimum
          (putnam_2015_b2_remove_two
            S
            (putnam_2015_b2_first (Smin3 S))
            (putnam_2015_b2_second (Smin3 S)))
          (putnam_2015_b2_third (Smin3 S)))
    (hsums :
      forall n : nat,
        sums n =
        (putnam_2015_b2_first (Smin3 (sets n)) +
         putnam_2015_b2_second (Smin3 (sets n)) +
         putnam_2015_b2_third (Smin3 (sets n)))%nat)
    (hsetsn :
      forall n x : nat,
        sets (n + 1)%nat x <->
        putnam_2015_b2_remove_four
          (sets n)
          (putnam_2015_b2_first (Smin3 (sets n)))
          (putnam_2015_b2_second (Smin3 (sets n)))
          (putnam_2015_b2_third (Smin3 (sets n)))
          (sums n)
          x) :
  (exists n : nat, Nat.modulo (sums n) 10000 = 2015%nat) <->
  putnam_2015_b2_solution.
Admitted.
