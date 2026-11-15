(*
  Statement-only formalization of Thousand Theorems corpus artifact Q472883
  (thousand-theorems__rocq__Q472883), "Quadratic reciprocity theorem": the
  Legendre symbols of distinct odd primes and the Jacobi symbols of arbitrary
  odd natural numbers obey the quadratic-reciprocity sign law. This file
  contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat ZArith ClassicalDescription.

Definition q472883_prime (p : nat) : Prop :=
  (2 <= p)%nat /\
  forall d : nat, Nat.divide d p -> d = 1%nat \/ d = p.

Definition q472883_quadratic_residue (p a : nat) : Prop :=
  exists x : nat,
    Nat.modulo (Nat.mul x x) p = Nat.modulo a p.

Definition q472883_legendre_symbol (p a : nat) : Z :=
  if Nat.eq_dec (Nat.modulo a p) 0%nat then
    0%Z
  else if excluded_middle_informative
            (q472883_quadratic_residue p a) then
    1%Z
  else
    (-1)%Z.

Fixpoint q472883_prime_multiplicity_fuel
    (p n fuel : nat) : nat :=
  match fuel with
  | 0%nat => 0%nat
  | S fuel' =>
      if Nat.eq_dec n 0%nat then
        0%nat
      else if Nat.eq_dec (Nat.modulo n p) 0%nat then
        S (q472883_prime_multiplicity_fuel
             p (Nat.div n p) fuel')
      else
        0%nat
  end.

Definition q472883_prime_multiplicity (p n : nat) : nat :=
  q472883_prime_multiplicity_fuel p n n.

Fixpoint q472883_jacobi_product
    (a b bound : nat) : Z :=
  match bound with
  | 0%nat => 1%Z
  | S bound' =>
      (q472883_jacobi_product a b bound' *
       if excluded_middle_informative
            (q472883_prime (S bound')) then
         Z.pow
           (q472883_legendre_symbol (S bound') a)
           (Z.of_nat
             (q472883_prime_multiplicity (S bound') b))
       else
         1%Z)%Z
  end.

Definition q472883_jacobi_symbol (a b : nat) : Z :=
  q472883_jacobi_product a b b.

Definition q472883_odd (n : nat) : Prop :=
  exists k : nat, n = (2 * k + 1)%nat.

Theorem q472883_legendre_quadratic_reciprocity :
  forall p q : nat,
    q472883_prime p ->
    q472883_prime q ->
    p <> 2%nat ->
    q <> 2%nat ->
    p <> q ->
    (q472883_legendre_symbol q p *
     q472883_legendre_symbol p q)%Z =
    Z.pow (-1)
      (Z.of_nat
        (Nat.mul (Nat.div p 2%nat) (Nat.div q 2%nat))).
Admitted.

Theorem q472883_jacobi_quadratic_reciprocity :
  forall a b : nat,
    q472883_odd a ->
    q472883_odd b ->
    q472883_jacobi_symbol a b =
    (Z.pow (-1)
       (Z.of_nat
         (Nat.mul (Nat.div a 2%nat) (Nat.div b 2%nat))) *
     q472883_jacobi_symbol b a)%Z.
Admitted.
