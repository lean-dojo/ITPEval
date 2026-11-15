(* Statement-only formalization of PutnamBench artifact putnam_1982_b2:
   evaluation of a Gaussian double integral weighted by the number of
   integer lattice points in a disk as a polynomial in a Gaussian series.
   This file contains no proof. *)

From Stdlib Require Import
  Reals ZArith Ensembles Finite_sets RiemannInt SeqSeries
  ClassicalEpsilon List.

Open Scope R_scope.

Definition putnam_1982_b2_lattice_points
    (x y : R) : Ensemble (Z * Z) :=
  fun p : Z * Z =>
    IZR (fst p) ^ 2 + IZR (snd p) ^ 2 <= x ^ 2 + y ^ 2.

Definition putnam_1982_b2_series_value
    (f : nat -> R) : R :=
  epsilon (inhabits (0 : R))
    (fun value : R => infinite_sum f value).

Definition putnam_1982_b2_finite_integral
    (f : R -> R) (a b : R) : R :=
  epsilon (inhabits (0 : R))
    (fun value : R =>
      exists h : Riemann_integrable f a b,
        value = RiemannInt h).

Definition putnam_1982_b2_whole_line_integral
    (f : R -> R) : R :=
  epsilon (inhabits (0 : R))
    (fun value : R =>
      Un_cv
        (fun n : nat =>
          putnam_1982_b2_finite_integral
            f (- INR n) (INR n))
        value).

Definition putnam_1982_b2_real_polynomial := list R.

Fixpoint putnam_1982_b2_polynomial_eval
    (p : putnam_1982_b2_real_polynomial) (x : R) : R :=
  match p with
  | nil => 0
  | coefficient :: rest =>
      coefficient + x * putnam_1982_b2_polynomial_eval rest x
  end.

Definition putnam_1982_b2_solution
    : putnam_1982_b2_real_polynomial :=
  PI :: (-4 * PI) :: (4 * PI) :: nil.

Theorem putnam_1982_b2
    (A : R * R -> nat)
    (g I : R)
    (hA : forall x y : R,
      cardinal (Z * Z)
        (putnam_1982_b2_lattice_points x y)
        (A (x, y)))
    (hg : g =
      putnam_1982_b2_series_value
        (fun k : nat => exp (- (INR k) ^ 2)))
    (hI : I =
      putnam_1982_b2_whole_line_integral
        (fun y : R =>
          putnam_1982_b2_whole_line_integral
            (fun x : R =>
              INR (A (x, y)) * exp (- x ^ 2 - y ^ 2)))) :
  I = putnam_1982_b2_polynomial_eval putnam_1982_b2_solution g.
Admitted.
