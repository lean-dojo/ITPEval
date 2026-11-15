(* Statement-only formalization of PutnamBench artifact putnam_1968_a6:
   classification of polynomials with coefficients in {-1, 1} whose roots
   are all real. This file contains no proof. *)

From Stdlib Require Import Reals List Arith.

Import ListNotations.
Open Scope R_scope.

Record complex : Type := Complex {
  real_part : R;
  imaginary_part : R
}.

Definition Czero : complex := Complex 0 0.
Definition Cone : complex := Complex 1 0.

Definition Cadd (z w : complex) : complex :=
  Complex
    (real_part z + real_part w)
    (imaginary_part z + imaginary_part w).

Definition Cneg (z : complex) : complex :=
  Complex (- real_part z) (- imaginary_part z).

Definition Cmul (z w : complex) : complex :=
  Complex
    (real_part z * real_part w - imaginary_part z * imaginary_part w)
    (real_part z * imaginary_part w + imaginary_part z * real_part w).

Fixpoint Cpow (z : complex) (n : nat) : complex :=
  match n with
  | O => Cone
  | S m => Cmul z (Cpow z m)
  end.

Record polynomial : Type := Polynomial {
  poly_coeff : nat -> complex;
  poly_bound : nat;
  poly_vanishes_above :
    forall k : nat, Nat.lt poly_bound k -> poly_coeff k = Czero
}.

Fixpoint eval_up_to
    (a : nat -> complex) (z : complex) (n : nat) : complex :=
  match n with
  | O => a O
  | S m => Cadd (eval_up_to a z m) (Cmul (a (S m)) (Cpow z (S m)))
  end.

Definition poly_eval (P : polynomial) (z : complex) : complex :=
  eval_up_to (poly_coeff P) z (poly_bound P).

Definition same_coefficients
    (P : polynomial) (coefficients : list complex) : Prop :=
  forall k : nat, poly_coeff P k = nth k coefficients Czero.

Definition cminus_one : complex := Complex (-1) 0.

Definition putnam_1968_a6_base_coefficients : list (list complex) :=
  [[cminus_one; Cone];
   [Cone; Cone];
   [cminus_one; Cone; Cone];
   [cminus_one; cminus_one; Cone];
   [cminus_one; cminus_one; Cone; Cone];
   [Cone; cminus_one; cminus_one; Cone]].

Definition putnam_1968_a6_solution (P : polynomial) : Prop :=
  exists coefficients : list complex,
    In coefficients putnam_1968_a6_base_coefficients /\
    (same_coefficients P coefficients \/
     same_coefficients P (map Cneg coefficients)).

Definition putnam_1968_a6_conditions (P : polynomial) : Prop :=
  exists n : nat,
    Nat.le 1 n /\
    (forall k : nat, Nat.le k n ->
      poly_coeff P k = Cone \/ poly_coeff P k = Cneg Cone) /\
    (forall k : nat, Nat.lt n k -> poly_coeff P k = Czero) /\
    (forall z : complex, poly_eval P z = Czero ->
      exists r : R, z = Complex r 0).

Theorem putnam_1968_a6 :
  forall P : polynomial,
    putnam_1968_a6_conditions P <-> putnam_1968_a6_solution P.
Proof. Admitted.
