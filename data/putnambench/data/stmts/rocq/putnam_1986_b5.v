(* Statement-only formalization of PutnamBench artifact putnam_1986_b5:
   real trivariate polynomial substitutions preserving
   x^2 + y^2 + z^2 + xyz and the four permitted sign patterns, up to
   permutation. This file contains no proof. *)

From Stdlib Require Import Reals Arith.PeanoNat Bool.

Open Scope R_scope.

Record putnam_1986_b5_polynomial : Type := {
  putnam_1986_b5_raw_coefficient : nat -> nat -> nat -> R;
  putnam_1986_b5_x_bound : nat;
  putnam_1986_b5_y_bound : nat;
  putnam_1986_b5_z_bound : nat
}.

Definition putnam_1986_b5_coefficient
    (p : putnam_1986_b5_polynomial) (i j k : nat) : R :=
  if andb
       (Nat.leb i (putnam_1986_b5_x_bound p))
       (andb
          (Nat.leb j (putnam_1986_b5_y_bound p))
          (Nat.leb k (putnam_1986_b5_z_bound p)))
  then putnam_1986_b5_raw_coefficient p i j k
  else 0.

Definition putnam_1986_b5_polynomial_eq
    (p q : putnam_1986_b5_polynomial) : Prop :=
  forall i j k : nat,
    putnam_1986_b5_coefficient p i j k =
    putnam_1986_b5_coefficient q i j k.

Fixpoint putnam_1986_b5_sum_to
    (n : nat) (term : nat -> R) : R :=
  match n with
  | O => term O
  | S m => putnam_1986_b5_sum_to m term + term (S m)
  end.

Definition putnam_1986_b5_eval
    (p : putnam_1986_b5_polynomial) (x y z : R) : R :=
  putnam_1986_b5_sum_to
    (putnam_1986_b5_x_bound p)
    (fun i : nat =>
      putnam_1986_b5_sum_to
        (putnam_1986_b5_y_bound p)
        (fun j : nat =>
          putnam_1986_b5_sum_to
            (putnam_1986_b5_z_bound p)
            (fun k : nat =>
              putnam_1986_b5_coefficient p i j k *
              x ^ i * y ^ j * z ^ k))).

Definition putnam_1986_b5_monomial
    (i j k : nat) (coefficient : R) :
    putnam_1986_b5_polynomial :=
  {|
    putnam_1986_b5_raw_coefficient :=
      fun a b c : nat =>
        if andb
             (Nat.eqb a i)
             (andb (Nat.eqb b j) (Nat.eqb c k))
        then coefficient
        else 0;
    putnam_1986_b5_x_bound := i;
    putnam_1986_b5_y_bound := j;
    putnam_1986_b5_z_bound := k
  |}.

Definition putnam_1986_b5_x : putnam_1986_b5_polynomial :=
  putnam_1986_b5_monomial 1%nat 0%nat 0%nat 1.

Definition putnam_1986_b5_y : putnam_1986_b5_polynomial :=
  putnam_1986_b5_monomial 0%nat 1%nat 0%nat 1.

Definition putnam_1986_b5_z : putnam_1986_b5_polynomial :=
  putnam_1986_b5_monomial 0%nat 0%nat 1%nat 1.

Definition putnam_1986_b5_neg_x : putnam_1986_b5_polynomial :=
  putnam_1986_b5_monomial 1%nat 0%nat 0%nat (-1).

Definition putnam_1986_b5_neg_y : putnam_1986_b5_polynomial :=
  putnam_1986_b5_monomial 0%nat 1%nat 0%nat (-1).

Definition putnam_1986_b5_neg_z : putnam_1986_b5_polynomial :=
  putnam_1986_b5_monomial 0%nat 0%nat 1%nat (-1).

Definition putnam_1986_b5_f (x y z : R) : R :=
  x ^ 2 + y ^ 2 + z ^ 2 + x * y * z.

Definition putnam_1986_b5_same_unordered_triple
    (p q r a b c : putnam_1986_b5_polynomial) : Prop :=
  forall s : putnam_1986_b5_polynomial,
    (putnam_1986_b5_polynomial_eq s p \/
     putnam_1986_b5_polynomial_eq s q \/
     putnam_1986_b5_polynomial_eq s r) <->
    (putnam_1986_b5_polynomial_eq s a \/
     putnam_1986_b5_polynomial_eq s b \/
     putnam_1986_b5_polynomial_eq s c).

Definition putnam_1986_b5_permitted
    (p q r : putnam_1986_b5_polynomial) : Prop :=
  putnam_1986_b5_same_unordered_triple
    p q r
    putnam_1986_b5_x putnam_1986_b5_y putnam_1986_b5_z \/
  putnam_1986_b5_same_unordered_triple
    p q r
    putnam_1986_b5_x putnam_1986_b5_neg_y putnam_1986_b5_neg_z \/
  putnam_1986_b5_same_unordered_triple
    p q r
    putnam_1986_b5_neg_x putnam_1986_b5_y putnam_1986_b5_neg_z \/
  putnam_1986_b5_same_unordered_triple
    p q r
    putnam_1986_b5_neg_x putnam_1986_b5_neg_y putnam_1986_b5_z.

Definition putnam_1986_b5_solution : Prop := False.

Theorem putnam_1986_b5 :
  putnam_1986_b5_solution <->
  forall p q r : putnam_1986_b5_polynomial,
    (forall x y z : R,
      putnam_1986_b5_f
        (putnam_1986_b5_eval p x y z)
        (putnam_1986_b5_eval q x y z)
        (putnam_1986_b5_eval r x y z) =
      putnam_1986_b5_f x y z) ->
    putnam_1986_b5_permitted p q r.
Admitted.
