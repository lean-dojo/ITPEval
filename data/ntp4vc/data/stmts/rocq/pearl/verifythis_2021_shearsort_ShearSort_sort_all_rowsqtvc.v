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
Theorem sort_all_rows'vc (m : matrix Z) : let o1 : Z := rows m - 1%Z in (0%Z ≤ o1 + 1%Z -> ((∀(i : Z), 0%Z ≤ i ∧ i < rows m -> permut (elts m i) (elts m i) 0%Z (columns m)) ∧ (∀(i : Z) (j : Z) (k : Z), (0%Z ≤ i ∧ i < 0%Z) ∧ 0%Z ≤ j ∧ j ≤ k ∧ k < columns m -> (let a : Z := elts m i j in let b : Z := elts m i k in if decide (Z.quot i 2%Z = 0%Z) then a ≤ b else b ≤ a))) ∧ (∀(m1 : matrix Z), rows m1 = rows m ∧ columns m1 = columns m -> (∀(tid : Z), (0%Z ≤ tid ∧ tid ≤ o1) ∧ (∀(i : Z), 0%Z ≤ i ∧ i < rows m1 -> permut (elts m1 i) (elts m i) 0%Z (columns m1)) ∧ (∀(i : Z) (j : Z) (k : Z), (0%Z ≤ i ∧ i < tid) ∧ 0%Z ≤ j ∧ j ≤ k ∧ k < columns m1 -> (let a : Z := elts m1 i j in let b : Z := elts m1 i k in if decide (Z.quot i 2%Z = 0%Z) then a ≤ b else b ≤ a)) -> ¬ 2%Z = 0%Z ∧ (0%Z ≤ tid ∧ tid < rows m1) ∧ (∀(m2 : matrix Z), rows m2 = rows m1 ∧ columns m2 = columns m1 -> (∀(j : Z) (k : Z), 0%Z ≤ j ∧ j < rows m2 ∧ (0%Z ≤ k ∧ k < columns m2) ∧ ¬ j = tid -> elts m2 j k = elts m1 j k) ∧ (∀(j : Z) (k : Z), 0%Z ≤ j ∧ j ≤ k ∧ k < columns m2 -> (let a : Z := elts m2 tid j in let b : Z := elts m2 tid k in if decide (Z.quot tid 2%Z = 0%Z) then a ≤ b else b ≤ a)) ∧ permut (elts m2 tid) (elts m1 tid) 0%Z (columns m2) -> (∀(i : Z), 0%Z ≤ i ∧ i < rows m2 -> permut (elts m2 i) (elts m i) 0%Z (columns m2)) ∧ (∀(i : Z) (j : Z) (k : Z), (0%Z ≤ i ∧ i < tid + 1%Z) ∧ 0%Z ≤ j ∧ j ≤ k ∧ k < columns m2 -> (let a : Z := elts m2 i j in let b : Z := elts m2 i k in if decide (Z.quot i 2%Z = 0%Z) then a ≤ b else b ≤ a)))) ∧ ((∀(i : Z), 0%Z ≤ i ∧ i < rows m1 -> permut (elts m1 i) (elts m i) 0%Z (columns m1)) ∧ (∀(i : Z) (j : Z) (k : Z), (0%Z ≤ i ∧ i < o1 + 1%Z) ∧ 0%Z ≤ j ∧ j ≤ k ∧ k < columns m1 -> (let a : Z := elts m1 i j in let b : Z := elts m1 i k in if decide (Z.quot i 2%Z = 0%Z) then a ≤ b else b ≤ a)) -> (∀(i : Z), 0%Z ≤ i ∧ i < rows m1 -> permut (elts m1 i) (elts m i) 0%Z (columns m1)) ∧ (∀(i : Z) (j : Z) (k : Z), (0%Z ≤ i ∧ i < rows m1) ∧ 0%Z ≤ j ∧ j ≤ k ∧ k < columns m1 -> (let a : Z := elts m1 i j in let b : Z := elts m1 i k in if decide (Z.quot i 2%Z = 0%Z) then a ≤ b else b ≤ a))))) ∧ (o1 + 1%Z < 0%Z -> (∀(i : Z), 0%Z ≤ i ∧ i < rows m -> permut (elts m i) (elts m i) 0%Z (columns m)) ∧ (∀(i : Z) (j : Z) (k : Z), (0%Z ≤ i ∧ i < rows m) ∧ 0%Z ≤ j ∧ j ≤ k ∧ k < columns m -> (let a : Z := elts m i j in let b : Z := elts m i k in if decide (Z.quot i 2%Z = 0%Z) then a ≤ b else b ≤ a))).
Admitted.
