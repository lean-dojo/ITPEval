Require Import Reals Coquelicot.Coquelicot.
Open Scope R.
Definition putnam_1982_a2_solution := True.
Theorem putnam_1982_a2
    (B : nat -> R -> R := fun n x => sum_n_m (fun m => Rpower (INR m) x) 1 n)
    (f : nat -> R := fun n =>
      B n (ln 2 / ln (INR n)) /
      pow (INR n * (ln (INR n) / ln 2)) 2)
    : ex_series (fun n => if (lt_dec n 2) then 0 else f n) <-> putnam_1982_a2_solution.
Proof. Admitted.
