Require Import Reals Coquelicot.Coquelicot.

Definition putnam_2014_a4_solution : R := 1 / 3.

Open Scope R_scope.

Definition putnam_2014_a4_admissible (mass : nat -> R) : Prop :=
  (forall n : nat, 0 <= mass n) /\
  is_series mass 1 /\
  is_series (fun n => INR n * mass n) 1 /\
  is_series (fun n => (INR n) ^ 2 * mass n) 2 /\
  is_series (fun n => (INR n) ^ 3 * mass n) 5.

Theorem putnam_2014_a4
    : (forall mass : nat -> R,
        putnam_2014_a4_admissible mass ->
        putnam_2014_a4_solution <= mass 0%nat) /\
      (exists mass : nat -> R,
        putnam_2014_a4_admissible mass /\
        mass 0%nat = putnam_2014_a4_solution).
Proof. Admitted.
