Require Import Reals Coquelicot.Coquelicot.
Definition putnam_1987_b1_solution := 1.
Theorem putnam_1987_b1
    : RInt
        (fun x =>
          sqrt (ln (9 - x)) /
          (sqrt (ln (9 - x)) + sqrt (ln (x + 3))))
        2 4 = putnam_1987_b1_solution.
Proof. Admitted.
