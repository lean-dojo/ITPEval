(* Statement-only formalization of PutnamBench corpus artifact putnam_2002_b6:
   coefficientwise congruence modulo a prime between a three-variable
   polynomial determinant and a finite product of integer linear forms.
   This file contains no proof. *)

From Stdlib Require Import ZArith List Arith.PeanoNat Bool.

Import ListNotations.
Open Scope Z_scope.

Record putnam_2002_b6_monomial : Type := {
  putnam_2002_b6_x_exponent : nat;
  putnam_2002_b6_y_exponent : nat;
  putnam_2002_b6_z_exponent : nat;
  putnam_2002_b6_monomial_coefficient : Z
}.

Definition putnam_2002_b6_polynomial : Type :=
  list putnam_2002_b6_monomial.

Fixpoint putnam_2002_b6_coefficient
    (p : putnam_2002_b6_polynomial) (i j k : nat) : Z :=
  match p with
  | [] => 0
  | m :: p' =>
      let rest := putnam_2002_b6_coefficient p' i j k in
      if andb
           (Nat.eqb (putnam_2002_b6_x_exponent m) i)
           (andb
              (Nat.eqb (putnam_2002_b6_y_exponent m) j)
              (Nat.eqb (putnam_2002_b6_z_exponent m) k))
      then putnam_2002_b6_monomial_coefficient m + rest
      else rest
  end.

Definition putnam_2002_b6_monomial_product
    (m n : putnam_2002_b6_monomial) :
    putnam_2002_b6_monomial :=
  {|
    putnam_2002_b6_x_exponent :=
      (putnam_2002_b6_x_exponent m +
       putnam_2002_b6_x_exponent n)%nat;
    putnam_2002_b6_y_exponent :=
      (putnam_2002_b6_y_exponent m +
       putnam_2002_b6_y_exponent n)%nat;
    putnam_2002_b6_z_exponent :=
      (putnam_2002_b6_z_exponent m +
       putnam_2002_b6_z_exponent n)%nat;
    putnam_2002_b6_monomial_coefficient :=
      putnam_2002_b6_monomial_coefficient m *
      putnam_2002_b6_monomial_coefficient n
  |}.

Definition putnam_2002_b6_polynomial_add
    (p q : putnam_2002_b6_polynomial) :
    putnam_2002_b6_polynomial :=
  p ++ q.

Definition putnam_2002_b6_polynomial_neg
    (p : putnam_2002_b6_polynomial) :
    putnam_2002_b6_polynomial :=
  map
    (fun m =>
      {|
        putnam_2002_b6_x_exponent :=
          putnam_2002_b6_x_exponent m;
        putnam_2002_b6_y_exponent :=
          putnam_2002_b6_y_exponent m;
        putnam_2002_b6_z_exponent :=
          putnam_2002_b6_z_exponent m;
        putnam_2002_b6_monomial_coefficient :=
          - putnam_2002_b6_monomial_coefficient m
      |})
    p.

Definition putnam_2002_b6_polynomial_sub
    (p q : putnam_2002_b6_polynomial) :
    putnam_2002_b6_polynomial :=
  putnam_2002_b6_polynomial_add
    p (putnam_2002_b6_polynomial_neg q).

Definition putnam_2002_b6_polynomial_mul
    (p q : putnam_2002_b6_polynomial) :
    putnam_2002_b6_polynomial :=
  flat_map
    (fun m => map (putnam_2002_b6_monomial_product m) q)
    p.

Definition putnam_2002_b6_one :
    putnam_2002_b6_polynomial :=
  [{|
    putnam_2002_b6_x_exponent := 0%nat;
    putnam_2002_b6_y_exponent := 0%nat;
    putnam_2002_b6_z_exponent := 0%nat;
    putnam_2002_b6_monomial_coefficient := 1
  |}].

Fixpoint putnam_2002_b6_polynomial_pow
    (p : putnam_2002_b6_polynomial) (n : nat) :
    putnam_2002_b6_polynomial :=
  match n with
  | O => putnam_2002_b6_one
  | S n' =>
      putnam_2002_b6_polynomial_mul
        p (putnam_2002_b6_polynomial_pow p n')
  end.

Definition putnam_2002_b6_x :
    putnam_2002_b6_polynomial :=
  [{|
    putnam_2002_b6_x_exponent := 1%nat;
    putnam_2002_b6_y_exponent := 0%nat;
    putnam_2002_b6_z_exponent := 0%nat;
    putnam_2002_b6_monomial_coefficient := 1
  |}].

Definition putnam_2002_b6_y :
    putnam_2002_b6_polynomial :=
  [{|
    putnam_2002_b6_x_exponent := 0%nat;
    putnam_2002_b6_y_exponent := 1%nat;
    putnam_2002_b6_z_exponent := 0%nat;
    putnam_2002_b6_monomial_coefficient := 1
  |}].

Definition putnam_2002_b6_z :
    putnam_2002_b6_polynomial :=
  [{|
    putnam_2002_b6_x_exponent := 0%nat;
    putnam_2002_b6_y_exponent := 0%nat;
    putnam_2002_b6_z_exponent := 1%nat;
    putnam_2002_b6_monomial_coefficient := 1
  |}].

Definition putnam_2002_b6_determinant
    (p : nat) : putnam_2002_b6_polynomial :=
  let xp :=
    putnam_2002_b6_polynomial_pow putnam_2002_b6_x p in
  let yp :=
    putnam_2002_b6_polynomial_pow putnam_2002_b6_y p in
  let zp :=
    putnam_2002_b6_polynomial_pow putnam_2002_b6_z p in
  let xp2 :=
    putnam_2002_b6_polynomial_pow
      putnam_2002_b6_x (Nat.pow p 2) in
  let yp2 :=
    putnam_2002_b6_polynomial_pow
      putnam_2002_b6_y (Nat.pow p 2) in
  let zp2 :=
    putnam_2002_b6_polynomial_pow
      putnam_2002_b6_z (Nat.pow p 2) in
  putnam_2002_b6_polynomial_add
    (putnam_2002_b6_polynomial_sub
      (putnam_2002_b6_polynomial_mul
        putnam_2002_b6_x
        (putnam_2002_b6_polynomial_sub
          (putnam_2002_b6_polynomial_mul yp zp2)
          (putnam_2002_b6_polynomial_mul zp yp2)))
      (putnam_2002_b6_polynomial_mul
        putnam_2002_b6_y
        (putnam_2002_b6_polynomial_sub
          (putnam_2002_b6_polynomial_mul xp zp2)
          (putnam_2002_b6_polynomial_mul zp xp2))))
    (putnam_2002_b6_polynomial_mul
      putnam_2002_b6_z
      (putnam_2002_b6_polynomial_sub
        (putnam_2002_b6_polynomial_mul xp yp2)
        (putnam_2002_b6_polynomial_mul yp xp2))).

Record putnam_2002_b6_linear_coefficients : Type := {
  putnam_2002_b6_linear_x_coefficient : Z;
  putnam_2002_b6_linear_y_coefficient : Z;
  putnam_2002_b6_linear_z_coefficient : Z
}.

Definition putnam_2002_b6_linear_form
    (c : putnam_2002_b6_linear_coefficients) :
    putnam_2002_b6_polynomial :=
  [
    {|
      putnam_2002_b6_x_exponent := 1%nat;
      putnam_2002_b6_y_exponent := 0%nat;
      putnam_2002_b6_z_exponent := 0%nat;
      putnam_2002_b6_monomial_coefficient :=
        putnam_2002_b6_linear_x_coefficient c
    |};
    {|
      putnam_2002_b6_x_exponent := 0%nat;
      putnam_2002_b6_y_exponent := 1%nat;
      putnam_2002_b6_z_exponent := 0%nat;
      putnam_2002_b6_monomial_coefficient :=
        putnam_2002_b6_linear_y_coefficient c
    |};
    {|
      putnam_2002_b6_x_exponent := 0%nat;
      putnam_2002_b6_y_exponent := 0%nat;
      putnam_2002_b6_z_exponent := 1%nat;
      putnam_2002_b6_monomial_coefficient :=
        putnam_2002_b6_linear_z_coefficient c
    |}
  ].

Fixpoint putnam_2002_b6_linear_product
    (factors : list putnam_2002_b6_linear_coefficients) :
    putnam_2002_b6_polynomial :=
  match factors with
  | [] => putnam_2002_b6_one
  | c :: factors' =>
      putnam_2002_b6_polynomial_mul
        (putnam_2002_b6_linear_form c)
        (putnam_2002_b6_linear_product factors')
  end.

Definition putnam_2002_b6_prime (p : nat) : Prop :=
  (2 <= p)%nat /\
  forall d : nat,
    (exists q : nat, p = (d * q)%nat) ->
    d = 1%nat \/ d = p.

Definition putnam_2002_b6_mod_eq
    (p : nat) (a b : Z) : Prop :=
  exists q : Z, a - b = Z.of_nat p * q.

Theorem putnam_2002_b6 :
  forall p : nat,
    putnam_2002_b6_prime p ->
    exists factors : list putnam_2002_b6_linear_coefficients,
      forall i j k : nat,
        putnam_2002_b6_mod_eq p
          (putnam_2002_b6_coefficient
            (putnam_2002_b6_determinant p) i j k)
          (putnam_2002_b6_coefficient
            (putnam_2002_b6_linear_product factors) i j k).
Admitted.
