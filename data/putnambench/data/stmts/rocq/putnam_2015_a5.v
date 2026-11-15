Require Import Nat Reals Arith Znumtheory Ensembles Finite_sets.
Open Scope nat_scope.
Theorem putnam_2015_a5
    (q : nat)
    (Nq : nat)
    (qodd : odd q = true )
    (qpos : q > 0)
    (hNq : cardinal nat
      (fun a : nat =>
        (0 < a)%nat /\
        Rlt (INR a) (Rdiv (INR q) (INR 4)) /\
        gcd a q = 1)
      Nq)
    : odd Nq = true <-> (exists (p k : nat), q = p^k /\ k > 0 /\ prime (Z.of_nat p) /\ (p mod 8 = 5 \/ p mod 8 = 7)).
Proof. Admitted.
