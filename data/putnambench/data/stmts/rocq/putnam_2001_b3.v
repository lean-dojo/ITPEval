Require Import Reals Coquelicot.Coquelicot.
Definition putnam_2001_b3_solution : R := 3.
Theorem putnam_2001_b3
    (closest : nat -> R := (fun n : nat => IZR (floor (sqrt (INR n) + 0.5))))
    : Series (fun n : nat =>
        (Rpower 2 (closest (S n)) + Rpower 2 (- closest (S n))) /
        (2 ^ (S n))) =
      putnam_2001_b3_solution.
Proof. Admitted.
