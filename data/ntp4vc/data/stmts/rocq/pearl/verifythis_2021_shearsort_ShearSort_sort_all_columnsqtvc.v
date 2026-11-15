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
Theorem sort_all_columns'vc (m : matrix Z) : (∃(result : bool), result = true ∨ rows m = columns m) ∧ (∀(o1 : bool), o1 = true ∨ rows m = columns m -> (if decide (o1 = true) then let o2 : Z := columns m - 1%Z in (0%Z ≤ o2 + 1%Z -> ((∀(j : Z), 0%Z ≤ j ∧ j < columns m -> permut (column m j) (column m j) 0%Z (rows m)) ∧ (∀(i : Z) (j : Z) (k : Z), (0%Z ≤ i ∧ i ≤ k ∧ k < rows m) ∧ 0%Z ≤ j ∧ j < 0%Z -> elts m i j ≤ elts m k j)) ∧ (∀(m1 : matrix Z), rows m1 = rows m ∧ columns m1 = columns m -> (∀(tid : Z), (0%Z ≤ tid ∧ tid ≤ o2) ∧ (∀(j : Z), 0%Z ≤ j ∧ j < columns m1 -> permut (column m1 j) (column m j) 0%Z (rows m1)) ∧ (∀(i : Z) (j : Z) (k : Z), (0%Z ≤ i ∧ i ≤ k ∧ k < rows m1) ∧ 0%Z ≤ j ∧ j < tid -> elts m1 i j ≤ elts m1 k j) -> (0%Z ≤ tid ∧ tid < columns m1) ∧ (∀(m2 : matrix Z), rows m2 = rows m1 ∧ columns m2 = columns m1 -> (∀(i : Z) (k : Z), 0%Z ≤ i ∧ i < rows m2 ∧ (0%Z ≤ k ∧ k < columns m2) ∧ ¬ k = tid -> elts m2 i k = elts m1 i k) ∧ (∀(i : Z) (k : Z), 0%Z ≤ i ∧ i ≤ k ∧ k < rows m2 -> elts m2 i tid ≤ elts m2 k tid) ∧ permut (column m2 tid) (column m1 tid) 0%Z (rows m2) -> (∀(j : Z), 0%Z ≤ j ∧ j < columns m2 -> permut (column m2 j) (column m j) 0%Z (rows m2)) ∧ (∀(i : Z) (j : Z) (k : Z), (0%Z ≤ i ∧ i ≤ k ∧ k < rows m2) ∧ 0%Z ≤ j ∧ j < tid + 1%Z -> elts m2 i j ≤ elts m2 k j))) ∧ ((∀(j : Z), 0%Z ≤ j ∧ j < columns m1 -> permut (column m1 j) (column m j) 0%Z (rows m1)) ∧ (∀(i : Z) (j : Z) (k : Z), (0%Z ≤ i ∧ i ≤ k ∧ k < rows m1) ∧ 0%Z ≤ j ∧ j < o2 + 1%Z -> elts m1 i j ≤ elts m1 k j) -> (∀(j : Z), 0%Z ≤ j ∧ j < columns m1 -> permut (column m1 j) (column m j) 0%Z (rows m1)) ∧ (∀(i : Z) (j : Z) (k : Z), (0%Z ≤ i ∧ i ≤ k ∧ k < rows m1) ∧ 0%Z ≤ j ∧ j < columns m1 -> elts m1 i j ≤ elts m1 k j)))) ∧ (o2 + 1%Z < 0%Z -> (∀(j : Z), 0%Z ≤ j ∧ j < columns m -> permut (column m j) (column m j) 0%Z (rows m)) ∧ (∀(i : Z) (j : Z) (k : Z), (0%Z ≤ i ∧ i ≤ k ∧ k < rows m) ∧ 0%Z ≤ j ∧ j < columns m -> elts m i j ≤ elts m k j)) else let n : Z := rows m in rows m = columns m ∧ (∀(m1 : matrix Z), rows m1 = rows m ∧ columns m1 = columns m -> (∀(i : Z) (j : Z), (0%Z ≤ i ∧ i < rows m1) ∧ 0%Z ≤ j ∧ j < columns m1 -> elts m i j = elts m1 j i) -> (let o2 : Z := columns m1 - 1%Z in (0%Z ≤ o2 + 1%Z -> ((∀(j : Z), 0%Z ≤ j ∧ j < n -> permut (elts m1 j) (column m j) 0%Z n) ∧ (∀(i : Z) (j : Z) (k : Z), (0%Z ≤ i ∧ i ≤ k ∧ k < n) ∧ 0%Z ≤ j ∧ j < 0%Z -> elts m1 j i ≤ elts m1 j k)) ∧ (∀(m2 : matrix Z), rows m2 = rows m1 ∧ columns m2 = columns m1 -> (∀(tid : Z), (0%Z ≤ tid ∧ tid ≤ o2) ∧ (∀(j : Z), 0%Z ≤ j ∧ j < n -> permut (elts m2 j) (column m j) 0%Z n) ∧ (∀(i : Z) (j : Z) (k : Z), (0%Z ≤ i ∧ i ≤ k ∧ k < n) ∧ 0%Z ≤ j ∧ j < tid -> elts m2 j i ≤ elts m2 j k) -> (0%Z ≤ tid ∧ tid < rows m2) ∧ (∀(m3 : matrix Z), rows m3 = rows m2 ∧ columns m3 = columns m2 -> (∀(j : Z) (k : Z), 0%Z ≤ j ∧ j < rows m3 ∧ (0%Z ≤ k ∧ k < columns m3) ∧ ¬ j = tid -> elts m3 j k = elts m2 j k) ∧ (∀(j : Z) (k : Z), 0%Z ≤ j ∧ j ≤ k ∧ k < columns m3 -> elts m3 tid j ≤ elts m3 tid k) ∧ permut (elts m3 tid) (elts m2 tid) 0%Z (columns m3) -> (∀(j : Z), 0%Z ≤ j ∧ j < n -> permut (elts m3 j) (column m j) 0%Z n) ∧ (∀(i : Z) (j : Z) (k : Z), (0%Z ≤ i ∧ i ≤ k ∧ k < n) ∧ 0%Z ≤ j ∧ j < tid + 1%Z -> elts m3 j i ≤ elts m3 j k))) ∧ ((∀(j : Z), 0%Z ≤ j ∧ j < n -> permut (elts m2 j) (column m j) 0%Z n) ∧ (∀(i : Z) (j : Z) (k : Z), (0%Z ≤ i ∧ i ≤ k ∧ k < n) ∧ 0%Z ≤ j ∧ j < o2 + 1%Z -> elts m2 j i ≤ elts m2 j k) -> rows m2 = columns m2 ∧ (∀(m3 : matrix Z), rows m3 = rows m2 ∧ columns m3 = columns m2 -> (∀(i : Z) (j : Z), (0%Z ≤ i ∧ i < rows m3) ∧ 0%Z ≤ j ∧ j < columns m3 -> elts m2 i j = elts m3 j i) -> (∀(j : Z), 0%Z ≤ j ∧ j < columns m3 -> permut (column m3 j) (column m j) 0%Z (rows m3)) ∧ (∀(i : Z) (j : Z) (k : Z), (0%Z ≤ i ∧ i ≤ k ∧ k < rows m3) ∧ 0%Z ≤ j ∧ j < columns m3 -> elts m3 i j ≤ elts m3 k j))))) ∧ (o2 + 1%Z < 0%Z -> rows m1 = columns m1 ∧ (∀(m2 : matrix Z), rows m2 = rows m1 ∧ columns m2 = columns m1 -> (∀(i : Z) (j : Z), (0%Z ≤ i ∧ i < rows m2) ∧ 0%Z ≤ j ∧ j < columns m2 -> elts m1 i j = elts m2 j i) -> (∀(j : Z), 0%Z ≤ j ∧ j < columns m2 -> permut (column m2 j) (column m j) 0%Z (rows m2)) ∧ (∀(i : Z) (j : Z) (k : Z), (0%Z ≤ i ∧ i ≤ k ∧ k < rows m2) ∧ 0%Z ≤ j ∧ j < columns m2 -> elts m2 i j ≤ elts m2 k j))))))).
Admitted.
