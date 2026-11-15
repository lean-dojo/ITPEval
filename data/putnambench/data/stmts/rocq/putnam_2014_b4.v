Require Import Reals Coquelicot.Coquelicot.
Open Scope C.
Theorem putnam_2014_b4
    (n : nat)
    (npos : gt n 0)
    (P : C -> C := fun r =>
      sum_n (fun k => RtoC (pow 2 (k * (n - k))) * r ^ k) n)
    : forall r : C, P r = 0 -> (exists (t : R), r = RtoC t). 
Proof. Admitted.
