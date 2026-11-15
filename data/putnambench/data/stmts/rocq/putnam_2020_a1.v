Require Import Ensembles Finite_sets Rdefinitions Reals Rpower. From mathcomp Require Import  bigop div fintype ssralg ssrnat ssrnum. 
Definition putnam_2020_a1_solution := 508536.
Theorem putnam_2020_a1
    (A: Ensemble nat := fun n => (2020 %| n = true /\ 
        Nat.lt n (Nat.pow 10 2020) /\
        exists (k l: nat), k >= l = true /\ n = \sum_(i < k-l+1) 10^(i+l)))
    : cardinal nat A putnam_2020_a1_solution.
Proof. Admitted. 
