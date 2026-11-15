(* Statement-only formalization of PutnamBench artifact putnam_1983_b2:
   existence of a real polynomial whose floor on each positive integer counts
   representations as sums of powers of two, with each power used at most
   three times. This file contains no proof. *)

From Stdlib Require Import Reals List Sorting.Sorted ZArith.

Open Scope R_scope.

Definition putnam_1983_b2_has_cardinality
    {A : Type} (P : A -> Prop) (cardinality : nat) : Prop :=
  exists enumeration : list A,
    NoDup enumeration /\
    length enumeration = cardinality /\
    forall x : A, In x enumeration <-> P x.

Definition putnam_1983_b2_representation
    (n : nat) (terms : list nat) : Prop :=
  StronglySorted Nat.le terms /\
  Forall
    (fun m : nat => exists k : nat, m = Nat.pow 2 k)
    terms /\
  (forall m : nat,
      In m terms ->
      (count_occ Nat.eq_dec terms m <= 3)%nat) /\
  fold_right Nat.add 0%nat terms = n.

Fixpoint putnam_1983_b2_polynomial_eval
    (coefficients : list R) (x : R) : R :=
  match coefficients with
  | nil => 0
  | coefficient :: remaining =>
      coefficient +
      x * putnam_1983_b2_polynomial_eval remaining x
  end.

Definition putnam_1983_b2_solution : Prop := True.

Theorem putnam_1983_b2
    (f : nat -> nat)
    (hf :
      forall n : nat,
        putnam_1983_b2_has_cardinality
          (putnam_1983_b2_representation n)
          (f n)) :
  putnam_1983_b2_solution <->
  exists coefficients : list R,
    forall n : nat,
      (0 < n)%nat ->
      INR (f n) <=
        putnam_1983_b2_polynomial_eval coefficients (INR n) <
      INR (f n) + 1.
Admitted.
