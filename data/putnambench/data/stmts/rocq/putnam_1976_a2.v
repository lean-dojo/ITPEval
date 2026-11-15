(* Statement-only formalization of PutnamBench artifact putnam_1976_a2:
   for every positive integer n, either (x+y)^n-x^n-y^n or
   (x+y)^n+x^n+y^n is an integer polynomial in x^2*y+x*y^2 and
   x^2+x*y+y^2. This file contains no proof. *)

From Stdlib Require Import ZArith List.

Open Scope Z_scope.

Fixpoint zpow_nat (x : Z) (n : nat) : Z :=
  match n with
  | O => 1
  | S k => x * zpow_nat x k
  end.

Fixpoint eval_int_poly (A : list Z) (x : Z) : Z :=
  match A with
  | nil => 0
  | coefficient :: rest =>
      coefficient + x * eval_int_poly rest x
  end.

Fixpoint eval_int_bivariate_poly
    (A : list (list Z)) (x y : Z) : Z :=
  match A with
  | nil => 0
  | coefficient :: rest =>
      eval_int_poly coefficient y +
      x * eval_int_bivariate_poly rest x y
  end.

Definition putnam_1976_a2_P (x y : Z) : Z :=
  zpow_nat x 2 * y + x * zpow_nat y 2.

Definition putnam_1976_a2_Q (x y : Z) : Z :=
  zpow_nat x 2 + x * y + zpow_nat y 2.

Definition putnam_1976_a2_F (n : nat) (x y : Z) : Z :=
  zpow_nat (x + y) n - zpow_nat x n - zpow_nat y n.

Definition putnam_1976_a2_G (n : nat) (x y : Z) : Z :=
  zpow_nat (x + y) n + zpow_nat x n + zpow_nat y n.

Theorem putnam_1976_a2
    (n : nat)
    (hn : (n > 0)%nat) :
  exists A : list (list Z),
    (forall x y : Z,
      putnam_1976_a2_F n x y =
      eval_int_bivariate_poly A
        (putnam_1976_a2_P x y)
        (putnam_1976_a2_Q x y)) \/
    (forall x y : Z,
      putnam_1976_a2_G n x y =
      eval_int_bivariate_poly A
        (putnam_1976_a2_P x y)
        (putnam_1976_a2_Q x y)).
Admitted.
