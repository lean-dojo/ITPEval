Require Import Reals Coquelicot.Coquelicot.
Definition putnam_2021_a4_solution := (sqrt 2 / 2) * PI * ln 2.
Theorem putnam_2021_a4 
    (I : R -> R := fun r =>
      RInt
        (fun x =>
          RInt
            (fun y =>
              (1 + 2 * x ^ 2) /
                (1 + x ^ 4 + 6 * x ^ 2 * y ^ 2 + y ^ 4) -
              (1 + y ^ 2) / (2 + x ^ 4 + y ^ 4))
            (- sqrt (r ^ 2 - x ^ 2))
            (sqrt (r ^ 2 - x ^ 2)))
        (-r)
        r)
    : is_lim I p_infty putnam_2021_a4_solution.
Proof. Admitted.
