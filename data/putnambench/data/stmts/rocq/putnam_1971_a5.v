(* Statement-only formalization of PutnamBench artifact putnam_1971_a5:
   the two positive integer scores whose nonnegative combinations omit exactly
   35 scores, including 58, are 11 and 8. This file contains no proof. *)

From Stdlib Require Import ZArith Ensembles Finite_sets.

Open Scope Z_scope.

Definition putnam_1971_a5_solution : (Z * Z)%type := (11, 8).

Definition putnam_1971_a5_unattainable
    (x y : Z) (s : nat) : Prop :=
  ~ exists m n : nat,
      Z.of_nat m * x + Z.of_nat n * y = Z.of_nat s.

Definition putnam_1971_a5_pab (x y : Z) : Prop :=
  cardinal nat (putnam_1971_a5_unattainable x y) 35%nat /\
  putnam_1971_a5_unattainable x y 58%nat.

Theorem putnam_1971_a5
    (a b : Z)
    (hab : 0 < a /\ 0 < b /\ b < a) :
  putnam_1971_a5_pab a b <->
  a = fst putnam_1971_a5_solution /\
  b = snd putnam_1971_a5_solution.
Admitted.
