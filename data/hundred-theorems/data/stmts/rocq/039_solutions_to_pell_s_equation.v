(*
  Statement-only formalization of "Solutions to Pell's Equation" from Hundred Theorems item 039.
  For every nonsquare natural parameter, a positive fundamental solution generates all integer
  solutions by Pell multiplication; for D = a^2 - 1 it is (a, 1). This file contains no proof.
*)

From Stdlib Require Import ZArith.

Open Scope Z_scope.

Definition pell_mul
    (D : nat) (p q : (Z * Z)%type) : (Z * Z)%type :=
  (fst p * fst q + Z.of_nat D * snd p * snd q,
   fst p * snd q + snd p * fst q).

Fixpoint pell_power
    (D : nat) (base : (Z * Z)%type) (n : nat) : (Z * Z)%type :=
  match n with
  | O => (1, 0)
  | S m => pell_mul D (pell_power D base m) base
  end.

Theorem solutions_to_pell_equation :
  forall D : nat,
    ~ (exists k : nat, D = (k * k)%nat) ->
    exists x0 y0 : nat,
      (0 < y0)%nat /\
      (Z.of_nat x0 * Z.of_nat x0 -
       Z.of_nat D * (Z.of_nat y0 * Z.of_nat y0) = 1)%Z /\
      (forall a : nat,
          (1 < a)%nat ->
          D = (a * a - 1)%nat ->
          x0 = a /\ y0 = 1%nat) /\
      forall x y : Z,
        (x * x - Z.of_nat D * (y * y) = 1)%Z <->
        exists n : nat,
          (Z.abs x, Z.abs y) =
          pell_power D (Z.of_nat x0, Z.of_nat y0) n.
Admitted.
