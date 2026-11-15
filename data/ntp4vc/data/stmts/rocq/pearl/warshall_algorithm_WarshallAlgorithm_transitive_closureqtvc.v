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
Require Import Why3.matrix.Matrix.
Open Scope Z_scope.
Inductive path : matrix bool -> Z -> Z -> Z -> Prop :=
 | Path_empty (m : matrix bool) (i : Z) (j : Z) (k : Z) : elts m i j = true -> path m i j k
 | Path_cons (x : Z) (k : Z) (m : matrix bool) (i : Z) (j : Z) : 0%Z ≤ x -> x < k -> path m i x k -> path m x j k -> path m i j k.
Theorem transitive_closure'vc (m : matrix bool) (t : matrix bool) (fact0 : rows m = columns m) (fact1 : rows t = rows m) (fact2 : columns t = columns m) (fact3 : ∀(r : Z), 0%Z ≤ r ∧ r < rows t -> (∀(c : Z), 0%Z ≤ c ∧ c < columns t -> elts t r c = elts m r c)) : let n : Z := rows m in let o1 : Z := n - 1%Z in (0%Z ≤ o1 + 1%Z -> (∀(x : Z) (y : Z), 0%Z ≤ x ∧ x < n -> 0%Z ≤ y ∧ y < n -> (elts t x y = true) = path m x y 0%Z) ∧ (∀(t1 : matrix bool), rows t1 = rows t ∧ columns t1 = columns t -> (∀(k : Z), (0%Z ≤ k ∧ k ≤ o1) ∧ (∀(x : Z) (y : Z), 0%Z ≤ x ∧ x < n -> 0%Z ≤ y ∧ y < n -> (elts t1 x y = true) = path m x y k) -> (let o2 : Z := n - 1%Z in (0%Z ≤ o2 + 1%Z -> (∀(x : Z) (y : Z), 0%Z ≤ x ∧ x < n -> 0%Z ≤ y ∧ y < n -> (elts t1 x y = true) = (if decide (x < 0%Z) then path m x y (k + 1%Z) else path m x y k)) ∧ (∀(t2 : matrix bool), rows t2 = rows t1 ∧ columns t2 = columns t1 -> (∀(i : Z), (0%Z ≤ i ∧ i ≤ o2) ∧ (∀(x : Z) (y : Z), 0%Z ≤ x ∧ x < n -> 0%Z ≤ y ∧ y < n -> (elts t2 x y = true) = (if decide (x < i) then path m x y (k + 1%Z) else path m x y k)) -> (let o3 : Z := n - 1%Z in (0%Z ≤ o3 + 1%Z -> (∀(x : Z) (y : Z), 0%Z ≤ x ∧ x < n -> 0%Z ≤ y ∧ y < n -> (elts t2 x y = true) = (if decide (x < i ∨ x = i ∧ y < 0%Z) then path m x y (k + 1%Z) else path m x y k)) ∧ (∀(t3 : matrix bool), rows t3 = rows t2 ∧ columns t3 = columns t2 -> (∀(j : Z), (0%Z ≤ j ∧ j ≤ o3) ∧ (∀(x : Z) (y : Z), 0%Z ≤ x ∧ x < n -> 0%Z ≤ y ∧ y < n -> (elts t3 x y = true) = (if decide (x < i ∨ x = i ∧ y < j) then path m x y (k + 1%Z) else path m x y k)) -> valid_index t3 i j ∧ (let o4 : bool := elts t3 i j in (¬ o4 = true -> valid_index t3 i k ∧ (elts t3 i k = true -> valid_index t3 k j)) ∧ (∀(o5 : bool), (if decide (o4 = true) then o5 = true else if decide (elts t3 i k = true) then o5 = elts t3 k j else o5 = false) -> valid_index t3 i j ∧ (∀(t4 : matrix bool), rows t4 = rows t3 ∧ columns t4 = columns t3 -> elts t4 = fun_updt (elts t3) i (fun_updt (elts t3 i) j o5) -> (∀(x : Z) (y : Z), 0%Z ≤ x ∧ x < n -> 0%Z ≤ y ∧ y < n -> (elts t4 x y = true) = (if decide (x < i ∨ x = i ∧ y < j + 1%Z) then path m x y (k + 1%Z) else path m x y k)))))) ∧ ((∀(x : Z) (y : Z), 0%Z ≤ x ∧ x < n -> 0%Z ≤ y ∧ y < n -> (elts t3 x y = true) = (if decide (x < i ∨ x = i ∧ y < o3 + 1%Z) then path m x y (k + 1%Z) else path m x y k)) -> (∀(x : Z) (y : Z), 0%Z ≤ x ∧ x < n -> 0%Z ≤ y ∧ y < n -> (elts t3 x y = true) = (if decide (x < i + 1%Z) then path m x y (k + 1%Z) else path m x y k))))) ∧ (o3 + 1%Z < 0%Z -> (∀(x : Z) (y : Z), 0%Z ≤ x ∧ x < n -> 0%Z ≤ y ∧ y < n -> (elts t2 x y = true) = (if decide (x < i + 1%Z) then path m x y (k + 1%Z) else path m x y k))))) ∧ ((∀(x : Z) (y : Z), 0%Z ≤ x ∧ x < n -> 0%Z ≤ y ∧ y < n -> (elts t2 x y = true) = (if decide (x < o2 + 1%Z) then path m x y (k + 1%Z) else path m x y k)) -> (∀(x : Z) (y : Z), 0%Z ≤ x ∧ x < n -> 0%Z ≤ y ∧ y < n -> (elts t2 x y = true) = path m x y (k + 1%Z))))) ∧ (o2 + 1%Z < 0%Z -> (∀(x : Z) (y : Z), 0%Z ≤ x ∧ x < n -> 0%Z ≤ y ∧ y < n -> (elts t1 x y = true) = path m x y (k + 1%Z))))) ∧ ((∀(x : Z) (y : Z), 0%Z ≤ x ∧ x < n -> 0%Z ≤ y ∧ y < n -> (elts t1 x y = true) = path m x y (o1 + 1%Z)) -> (let n1 : Z := rows m in ∀(x : Z) (y : Z), 0%Z ≤ x ∧ x < n1 -> 0%Z ≤ y ∧ y < n1 -> (elts t1 x y = true) = path m x y n1)))) ∧ (o1 + 1%Z < 0%Z -> (let n1 : Z := rows m in ∀(x : Z) (y : Z), 0%Z ≤ x ∧ x < n1 -> 0%Z ≤ y ∧ y < n1 -> (elts t x y = true) = path m x y n1)).
Admitted.
