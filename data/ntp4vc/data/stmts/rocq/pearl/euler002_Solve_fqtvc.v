From Stdlib Require Import Strings.String.
From Stdlib Require Import String Ascii.
From Stdlib Require Arith.
From stdpp Require Import base.
From stdpp Require Import fin_maps.
From stdpp Require Import gmap.
From stdpp Require Import base gmultiset.
From Stdlib Require Classical.
From Stdlib Require Import ZArith.
From stdpp.bitvector Require Import definitions tactics.
From Stdlib Require Import Sorting.Sorted.
From Stdlib Require Import Reals.Rbasic_fun.
From Stdlib Require Import Reals.Abstract.ConstructiveAbs.
From Stdlib Require Import Reals.Rdefinitions.
From stdpp Require Import list_relations.
From stdpp Require Import list_numbers.
From stdpp Require Import functions.
From Stdlib Require Import ClassicalEpsilon.
From stdpp Require Import base decidable.
From Stdlib Require Import ZArith.Zeuclid.
From Stdlib Require Import ZArith.Znumtheory.
From stdpp Require Import propset.
From Stdlib Require Import Reals.
Require Import Why3.Base.
Require Import Why3.why3.Ref.Ref.
Require Import Why3.int.Fibonacci.
Require Import euler002_vcg.euler002.FibSumEven.
Require Import euler002_vcg.euler002.FibOnlyEven.
Open Scope Z_scope.
Theorem f'vc (m : Z) (fact0 : 0%Z ≤ m) : 0%Z ≤ 0%Z ∧ 0%Z ≤ 0%Z ∧ 0%Z = fib_even 0%Z ∧ 0%Z = fib 0%Z ∧ 2%Z = fib_even (0%Z + 1%Z) ∧ 2%Z = fib (0%Z + 3%Z) ∧ 0%Z = fib_sum_even m 0%Z ∧ 0%Z ≤ 0%Z ∧ 0%Z < 2%Z ∧ (∀(k : Z) (n : Z), 0%Z ≤ n ∧ 0%Z ≤ k ∧ fib_even n = fib k ∧ fib_even (n + 1%Z) = fib (k + 3%Z) ∧ 0%Z ≤ fib_even n ∧ fib_even n < fib_even (n + 1%Z) -> (if decide (fib_even n ≤ m) then (0%Z ≤ m - fib_even n ∧ m - fib_even (n + 1%Z) < m - fib_even n) ∧ 0%Z ≤ n + 1%Z ∧ 0%Z ≤ k + 3%Z ∧ fib_even (n + 1%Z) = fib (k + 3%Z) ∧ 4%Z * fib_even (n + 1%Z) + fib_even n = fib_even (n + 1%Z + 1%Z) ∧ 4%Z * fib_even (n + 1%Z) + fib_even n = fib (k + 3%Z + 3%Z) ∧ fib_sum_even m k + fib_even n = fib_sum_even m (k + 3%Z) ∧ 0%Z ≤ fib_even (n + 1%Z) ∧ fib_even (n + 1%Z) < 4%Z * fib_even (n + 1%Z) + fib_even n else ∃(n1 : Z), fib_sum_even m k = fib_sum_even m n1 ∧ m < fib n1)).
Admitted.
