Require Import Reals Coquelicot.Coquelicot.
Definition putnam_1981_a3_solution := False.
Theorem putnam_1981_a3
    : ex_finite_lim
        (fun k => exp (-k) * (RInt (fun x => (RInt (fun y => (exp x - exp y) / (x - y)) 0 k)) 0 k))
        p_infty <-> putnam_1981_a3_solution.
Proof. Admitted.
