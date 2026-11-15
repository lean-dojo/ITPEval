Require Import Nat Reals Coquelicot.Coquelicot.
Theorem putnam_1971_a4
    (epsilon : R)
    (hepsilon : 0 < epsilon < 1)
    (P : nat -> (R * R) -> R := fun n '(x, y) => (x + y)^n * (x^2 - (2 - epsilon)*x*y + y^2))
    : exists N : nat, forall n : nat, ge n N ->
        exists coeff : (nat * nat) -> R,
          (forall i j : nat, (i + j = n + 2)%nat -> coeff (i, j) > 0) /\
          (forall x y : R,
            P n (x, y) =
              sum_n
                (fun i => coeff (i, (n + 2 - i)%nat) * x^i * y^((n + 2 - i)%nat))
                (n + 2)).
Proof. Admitted.
