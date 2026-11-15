From mathcomp Require Import all_algebra all_ssreflect.
From mathcomp Require Import reals normedtype sequences topology.
From mathcomp Require Import classical_sets.
Import numFieldNormedType.Exports.
Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Variable R : realType.
Definition putnam_2015_b4_solution : int * int := (17%Z, 21%Z).
Definition putnam_2015_b4_value : rat := 17%:Q / 21%:Q.

Theorem putnam_2015_b4
    (tri_fun : nat -> nat -> nat -> R := fun i j k : nat => 
        if (ltn i (Nat.add j k)) && (ltn j (Nat.add i k)) && (ltn k (Nat.add i j)) then (2 ^+ i) / ((3 ^+ j * 5 ^+ k)) else 0)
    (f : nat -> R := fun n : nat => 
        \sum_(1 <= i < n)
        (\sum_(1 <= j < n) 
        (\sum_(1 <= k < n) 
        (tri_fun i j k))))
    : ((fun n : nat => f n) @ \oo --> (ratr putnam_2015_b4_value : R)) /\
      (numq putnam_2015_b4_value, denq putnam_2015_b4_value) =
        putnam_2015_b4_solution.
Proof. Admitted.
