(* Statement-only formalization of PutnamBench artifact putnam_1969_a1:
   the possible ranges over R^2 of real bivariate polynomials are precisely
   singletons, open or closed rays, and R itself. This file contains no proof. *)

From Stdlib Require Import Reals.

Open Scope R_scope.

Record bivariate_polynomial : Type := {
  x_degree_bound : nat;
  y_degree_bound : nat;
  coefficient : nat -> nat -> R;
  coefficient_outside_bounds :
    forall i j : nat,
      ((x_degree_bound < i)%nat \/ (y_degree_bound < j)%nat) ->
      coefficient i j = 0
}.

Fixpoint finite_sum (n : nat) (f : nat -> R) : R :=
  match n with
  | O => f O
  | S k => finite_sum k f + f (S k)
  end.

Definition polynomial_eval
    (p : bivariate_polynomial) (x y : R) : R :=
  finite_sum (x_degree_bound p) (fun i : nat =>
    finite_sum (y_degree_bound p) (fun j : nat =>
      coefficient p i j * x ^ i * y ^ j)).

Definition is_polynomial_range
    (S : R -> Prop) : Prop :=
  exists p : bivariate_polynomial,
    forall z : R,
      S z <-> exists x y : R, polynomial_eval p x y = z.

Definition putnam_1969_a1_solution
    (S : R -> Prop) : Prop :=
  (exists c : R, forall z : R, S z <-> z = c) \/
  (exists c : R, forall z : R, S z <-> c <= z) \/
  (exists c : R, forall z : R, S z <-> z <= c) \/
  (exists c : R, forall z : R, S z <-> c < z) \/
  (exists c : R, forall z : R, S z <-> z < c) \/
  (forall z : R, S z).

Theorem putnam_1969_a1 :
  forall S : R -> Prop,
    is_polynomial_range S <-> putnam_1969_a1_solution S.
Admitted.
