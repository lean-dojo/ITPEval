(* Statement-only formalization of PutnamBench artifact putnam_2009_b4:
   the real vector space of bivariate polynomials of total degree at most
   2009 whose average on every circle centered at the origin is zero has
   dimension 2020050; this file contains no proof. *)

From Stdlib Require Import Reals RiemannInt List.

Open Scope R_scope.

Definition putnam_2009_b4_polynomial : Type :=
  nat -> nat -> R.

Definition putnam_2009_b4_degree_at_most
    (degree : nat) (P : putnam_2009_b4_polynomial) : Prop :=
  forall i j : nat,
    (degree < i + j)%nat ->
    P i j = 0.

Fixpoint putnam_2009_b4_finite_sum
    (n : nat) (f : nat -> R) : R :=
  match n with
  | O => f O
  | S k => putnam_2009_b4_finite_sum k f + f (S k)
  end.

Definition putnam_2009_b4_eval
    (P : putnam_2009_b4_polynomial) (x y : R) : R :=
  putnam_2009_b4_finite_sum 2009
    (fun i : nat =>
      putnam_2009_b4_finite_sum 2009
        (fun j : nat => P i j * x ^ i * y ^ j)).

Definition putnam_2009_b4_balanced
    (P : putnam_2009_b4_polynomial) : Prop :=
  forall r : R,
    0 < r ->
    exists integrable :
      Riemann_integrable
        (fun t : R =>
          putnam_2009_b4_eval P (r * cos t) (r * sin t))
        0 (2 * PI),
      RiemannInt integrable / (2 * PI * r) = 0.

Definition putnam_2009_b4_space
    (P : putnam_2009_b4_polynomial) : Prop :=
  putnam_2009_b4_balanced P /\
  putnam_2009_b4_degree_at_most 2009 P.

Definition putnam_2009_b4_polynomial_eq
    (P Q : putnam_2009_b4_polynomial) : Prop :=
  forall i j : nat, P i j = Q i j.

Fixpoint putnam_2009_b4_linear_combination
    (coefficients : list R)
    (polynomials : list putnam_2009_b4_polynomial)
    : putnam_2009_b4_polynomial :=
  match coefficients, polynomials with
  | coefficient :: coefficients', P :: polynomials' =>
      fun i j =>
        coefficient * P i j +
        putnam_2009_b4_linear_combination
          coefficients' polynomials' i j
  | _, _ => fun _ _ => 0
  end.

Definition putnam_2009_b4_linearly_independent
    (polynomials : list putnam_2009_b4_polynomial) : Prop :=
  forall coefficients : list R,
    length coefficients = length polynomials ->
    putnam_2009_b4_polynomial_eq
      (putnam_2009_b4_linear_combination coefficients polynomials)
      (fun _ _ => 0) ->
    Forall (fun coefficient : R => coefficient = 0) coefficients.

Definition putnam_2009_b4_spans
    (polynomials : list putnam_2009_b4_polynomial) : Prop :=
  forall P : putnam_2009_b4_polynomial,
    putnam_2009_b4_space P ->
    exists coefficients : list R,
      length coefficients = length polynomials /\
      putnam_2009_b4_polynomial_eq
        (putnam_2009_b4_linear_combination coefficients polynomials)
        P.

Definition putnam_2009_b4_exact_dimension (dimension : nat) : Prop :=
  exists basis : list putnam_2009_b4_polynomial,
    length basis = dimension /\
    Forall putnam_2009_b4_space basis /\
    putnam_2009_b4_linearly_independent basis /\
    putnam_2009_b4_spans basis.

Definition putnam_2009_b4_solution : nat := 2020050.

Theorem putnam_2009_b4 :
  putnam_2009_b4_exact_dimension putnam_2009_b4_solution.
Admitted.
