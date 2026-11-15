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
Require Import Why3.int.NumOf.
Require Import Why3.int.Sum.
Require Import Why3.map.MapExt.
Require Import Why3.map.MapPermut.
Require Import Why3.matrix.Matrix.
Open Scope Z_scope.
Axiom column : forall {α : Type} `{Inhabited α}, matrix α -> Z -> Z -> α.
Axiom column'def : forall  {α : Type} `{Inhabited α} (m : matrix α) (j : Z) (i : Z), column m j i = elts m i j.
Axiom moccf : forall {α : Type} `{Inhabited α}, α -> (Z -> Z -> α) -> Z -> Z -> Z.
Axiom moccf'def : forall  {α : Type} `{Inhabited α} (x : α) (e : Z -> Z -> α) (c : Z) (i : Z), moccf x e c i = Z.of_nat (map_occ_list x (e i) 0%Z c).
Definition mocc {α : Type} `{Inhabited α} (x : α) (e : Z -> Z -> α) (r : Z) (c : Z) : Z := sum (moccf x e c) 0%Z r.
Axiom compose : forall {β : Type} `{Inhabited β} {γ : Type} `{Inhabited γ} {α : Type} `{Inhabited α}, (β -> γ) -> (α -> β) -> α -> γ.
Axiom compose'def : forall  {β : Type} {γ : Type} {α : Type} `{Inhabited β} `{Inhabited γ} `{Inhabited α} (g : β -> γ) (f : α -> β) (x : α), compose g f x = g (f x).
Theorem sort_column'vc (j : Z) (m : matrix Z) (fact0 : 0%Z ≤ j) (fact1 : j < columns m) : let o1 : Z := rows m in 0%Z ≤ o1 ∧ (∀(a : list Z), (∀(i : Z), 0%Z ≤ i ∧ i < o1 -> nth (Z.to_nat i) a inhabitant = 0%Z) ∧ Z.of_nat (length a) = o1 -> (let o2 : Z := rows m - 1%Z in (0%Z ≤ o2 + 1%Z -> (∀(k : Z), 0%Z ≤ k ∧ k < 0%Z -> nth_i a k = elts m k j) ∧ (∀(a1 : list Z), length a1 = length a -> (∀(i : Z), (0%Z ≤ i ∧ i ≤ o2) ∧ (∀(k : Z), 0%Z ≤ k ∧ k < i -> nth_i a1 k = elts m k j) -> valid_index m i j ∧ (let o3 : Z := elts m i j in (0%Z ≤ i ∧ i < Z.of_nat (length a1)) ∧ (length (set_list a1 (Z.to_nat i) o3) = length a1 -> nth_i (set_list a1 (Z.to_nat i) o3) = fun_updt (nth_i a1) i o3 -> (∀(k : Z), 0%Z ≤ k ∧ k < i + 1%Z -> nth_i (set_list a1 (Z.to_nat i) o3) k = elts m k j)))) ∧ ((∀(k : Z), 0%Z ≤ k ∧ k < o2 + 1%Z -> nth_i a1 k = elts m k j) -> (∀(a2 : list Z), length a2 = length a1 -> (∀(i : Z) (j1 : Z), 0%Z ≤ i ∧ i ≤ j1 ∧ j1 < Z.of_nat (length a2) -> nth (Z.to_nat i) a2 inhabitant ≤ nth (Z.to_nat j1) a2 inhabitant) ∧ permut (nth_i a2) (nth_i a1) 0%Z (Z.of_nat (length a2)) -> (let o3 : Z := rows m - 1%Z in (0%Z ≤ o3 + 1%Z -> (∀(k : Z), 0%Z ≤ k ∧ k < 0%Z -> nth_i a2 k = elts m k j) ∧ (∀(m1 : matrix Z), rows m1 = rows m ∧ columns m1 = columns m -> (∀(i : Z), (0%Z ≤ i ∧ i ≤ o3) ∧ (∀(k : Z), 0%Z ≤ k ∧ k < i -> nth_i a2 k = elts m1 k j) ∧ (∀(k : Z) (l : Z), (0%Z ≤ k ∧ k < rows m1) ∧ (0%Z ≤ l ∧ l < columns m1) ∧ ¬ l = j -> elts m1 k l = elts m k l) -> (0%Z ≤ i ∧ i < Z.of_nat (length a2)) ∧ valid_index m1 i j ∧ (∀(m2 : matrix Z), rows m2 = rows m1 ∧ columns m2 = columns m1 -> elts m2 = fun_updt (elts m1) i (fun_updt (elts m1 i) j (nth (Z.to_nat i) a2 inhabitant)) -> (∀(k : Z), 0%Z ≤ k ∧ k < i + 1%Z -> nth_i a2 k = elts m2 k j) ∧ (∀(k : Z) (l : Z), (0%Z ≤ k ∧ k < rows m2) ∧ (0%Z ≤ l ∧ l < columns m2) ∧ ¬ l = j -> elts m2 k l = elts m k l))) ∧ ((∀(k : Z), 0%Z ≤ k ∧ k < o3 + 1%Z -> nth_i a2 k = elts m1 k j) ∧ (∀(k : Z) (l : Z), (0%Z ≤ k ∧ k < rows m1) ∧ (0%Z ≤ l ∧ l < columns m1) ∧ ¬ l = j -> elts m1 k l = elts m k l) -> (∀(i : Z) (k : Z), 0%Z ≤ i ∧ i < rows m1 ∧ (0%Z ≤ k ∧ k < columns m1) ∧ ¬ k = j -> elts m1 i k = elts m i k) ∧ (∀(i : Z) (k : Z), 0%Z ≤ i ∧ i ≤ k ∧ k < rows m1 -> elts m1 i j ≤ elts m1 k j) ∧ permut (column m1 j) (column m j) 0%Z (rows m1)))) ∧ (o3 + 1%Z < 0%Z -> (∀(i : Z) (k : Z), 0%Z ≤ i ∧ i ≤ k ∧ k < rows m -> elts m i j ≤ elts m k j) ∧ permut (column m j) (column m j) 0%Z (rows m))))))) ∧ (o2 + 1%Z < 0%Z -> (∀(a1 : list Z), length a1 = length a -> (∀(i : Z) (j1 : Z), 0%Z ≤ i ∧ i ≤ j1 ∧ j1 < Z.of_nat (length a1) -> nth (Z.to_nat i) a1 inhabitant ≤ nth (Z.to_nat j1) a1 inhabitant) ∧ permut (nth_i a1) (nth_i a) 0%Z (Z.of_nat (length a1)) -> (let o3 : Z := rows m - 1%Z in (0%Z ≤ o3 + 1%Z -> (∀(k : Z), 0%Z ≤ k ∧ k < 0%Z -> nth_i a1 k = elts m k j) ∧ (∀(m1 : matrix Z), rows m1 = rows m ∧ columns m1 = columns m -> (∀(i : Z), (0%Z ≤ i ∧ i ≤ o3) ∧ (∀(k : Z), 0%Z ≤ k ∧ k < i -> nth_i a1 k = elts m1 k j) ∧ (∀(k : Z) (l : Z), (0%Z ≤ k ∧ k < rows m1) ∧ (0%Z ≤ l ∧ l < columns m1) ∧ ¬ l = j -> elts m1 k l = elts m k l) -> (0%Z ≤ i ∧ i < Z.of_nat (length a1)) ∧ valid_index m1 i j ∧ (∀(m2 : matrix Z), rows m2 = rows m1 ∧ columns m2 = columns m1 -> elts m2 = fun_updt (elts m1) i (fun_updt (elts m1 i) j (nth (Z.to_nat i) a1 inhabitant)) -> (∀(k : Z), 0%Z ≤ k ∧ k < i + 1%Z -> nth_i a1 k = elts m2 k j) ∧ (∀(k : Z) (l : Z), (0%Z ≤ k ∧ k < rows m2) ∧ (0%Z ≤ l ∧ l < columns m2) ∧ ¬ l = j -> elts m2 k l = elts m k l))) ∧ ((∀(k : Z), 0%Z ≤ k ∧ k < o3 + 1%Z -> nth_i a1 k = elts m1 k j) ∧ (∀(k : Z) (l : Z), (0%Z ≤ k ∧ k < rows m1) ∧ (0%Z ≤ l ∧ l < columns m1) ∧ ¬ l = j -> elts m1 k l = elts m k l) -> (∀(i : Z) (k : Z), 0%Z ≤ i ∧ i < rows m1 ∧ (0%Z ≤ k ∧ k < columns m1) ∧ ¬ k = j -> elts m1 i k = elts m i k) ∧ (∀(i : Z) (k : Z), 0%Z ≤ i ∧ i ≤ k ∧ k < rows m1 -> elts m1 i j ≤ elts m1 k j) ∧ permut (column m1 j) (column m j) 0%Z (rows m1)))) ∧ (o3 + 1%Z < 0%Z -> (∀(i : Z) (k : Z), 0%Z ≤ i ∧ i ≤ k ∧ k < rows m -> elts m i j ≤ elts m k j) ∧ permut (column m j) (column m j) 0%Z (rows m))))))).
Admitted.
