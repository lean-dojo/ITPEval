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
Require Import Why3.map.MapEq.
Require Import Why3.map.MapExchange.
Require Import Why3.map.MapPermut.
Require Import skew_heaps_vcg.skew_heaps.SkewHeaps.
Require Import Why3.bintree.Tree.
Require Import Why3.bintree.Size.
Require Import Why3.bintree.Occ.
Open Scope Z_scope.
Definition sorted_sub (a : list elt) (l : Z) (u : Z) := ∀(i1 : Z) (i2 : Z), l ≤ i1 ∧ i1 < i2 ∧ i2 < u -> le (nth (Z.to_nat i1) a inhabitant) (nth (Z.to_nat i2) a inhabitant).
Definition sorted (a : list elt) := ∀(i1 : Z) (i2 : Z), 0%Z ≤ i1 ∧ i1 < i2 ∧ i2 < Z.of_nat (length a) -> le (nth (Z.to_nat i1) a inhabitant) (nth (Z.to_nat i2) a inhabitant).
Theorem heapsort'vc (a : list elt) : let n : Z := Z.of_nat (length a) in let o1 : Z := n - 1%Z in (0%Z ≤ o1 + 1%Z -> ((heap empty ∧ Size.size empty = 0%Z) ∧ (∀(e : elt), Z.of_nat (map_occ_list e (nth_i a) 0%Z n) + occ e empty = Z.of_nat (map_occ_list e (nth_i a) 0%Z n))) ∧ (∀(t : tree elt), ((0%Z ≤ Size.size t ∧ Size.size t ≤ o1) ∧ heap t ∧ (∀(e : elt), Z.of_nat (map_occ_list e (nth_i a) (Size.size t) n) + occ e t = Z.of_nat (map_occ_list e (nth_i a) 0%Z n)) -> (0%Z ≤ Size.size t ∧ Size.size t < Z.of_nat (length a)) ∧ (let o2 : elt := nth (Z.to_nat (Size.size t)) a inhabitant in heap t ∧ (∀(o3 : tree elt), heap o3 ∧ occ o2 o3 = occ o2 t + 1%Z ∧ (∀(e : elt), ¬ e = o2 -> occ e o3 = occ e t) ∧ Size.size o3 = Size.size t + 1%Z -> (heap o3 ∧ Size.size o3 = Size.size t + 1%Z) ∧ (∀(e : elt), Z.of_nat (map_occ_list e (nth_i a) (Size.size t + 1%Z) n) + occ e o3 = Z.of_nat (map_occ_list e (nth_i a) 0%Z n))))) ∧ ((heap t ∧ Size.size t = o1 + 1%Z) ∧ (∀(e : elt), Z.of_nat (map_occ_list e (nth_i a) (o1 + 1%Z) n) + occ e t = Z.of_nat (map_occ_list e (nth_i a) 0%Z n)) -> (let o2 : Z := n - 1%Z in (0%Z ≤ o2 + 1%Z -> (sorted_sub a 0%Z 0%Z ∧ (heap t ∧ Size.size t = n - 0%Z) ∧ (∀(j : Z), 0%Z ≤ j ∧ j < 0%Z -> (∀(e : elt), mem e t -> le (nth (Z.to_nat j) a inhabitant) e)) ∧ (∀(e : elt), Z.of_nat (map_occ_list e (nth_i a) 0%Z 0%Z) + occ e t = Z.of_nat (map_occ_list e (nth_i a) 0%Z n))) ∧ (∀(t1 : tree elt) (a1 : list elt), length a1 = length a -> (∀(i : Z), (0%Z ≤ i ∧ i ≤ o2) ∧ sorted_sub a1 0%Z i ∧ (heap t1 ∧ Size.size t1 = n - i) ∧ (∀(j : Z), 0%Z ≤ j ∧ j < i -> (∀(e : elt), mem e t1 -> le (nth (Z.to_nat j) a1 inhabitant) e)) ∧ (∀(e : elt), Z.of_nat (map_occ_list e (nth_i a1) 0%Z i) + occ e t1 = Z.of_nat (map_occ_list e (nth_i a) 0%Z n)) -> (heap t1 ∧ 0%Z < Size.size t1) ∧ (let o3 : elt := minimum t1 in (0%Z ≤ i ∧ i < Z.of_nat (length a1)) ∧ (length (set_list a1 (Z.to_nat i) o3) = length a1 -> nth_i (set_list a1 (Z.to_nat i) o3) = fun_updt (nth_i a1) i o3 -> (heap t1 ∧ 0%Z < Size.size t1) ∧ (∀(o4 : tree elt), heap o4 ∧ occ (minimum t1) o4 = occ (minimum t1) t1 - 1%Z ∧ (∀(e : elt), ¬ e = minimum t1 -> occ e o4 = occ e t1) ∧ Size.size o4 = Size.size t1 - 1%Z -> sorted_sub (set_list a1 (Z.to_nat i) o3) 0%Z (i + 1%Z) ∧ (heap o4 ∧ Size.size o4 = n - (i + 1%Z)) ∧ (∀(j : Z), 0%Z ≤ j ∧ j < i + 1%Z -> (∀(e : elt), mem e o4 -> le (nth (Z.to_nat j) (set_list a1 (Z.to_nat i) o3) inhabitant) e)) ∧ (∀(e : elt), Z.of_nat (map_occ_list e (nth_i (set_list a1 (Z.to_nat i) o3)) 0%Z (i + 1%Z)) + occ e o4 = Z.of_nat (map_occ_list e (nth_i a) 0%Z n)))))) ∧ (sorted_sub a1 0%Z (o2 + 1%Z) ∧ (heap t1 ∧ Size.size t1 = n - (o2 + 1%Z)) ∧ (∀(j : Z), 0%Z ≤ j ∧ j < o2 + 1%Z -> (∀(e : elt), mem e t1 -> le (nth (Z.to_nat j) a1 inhabitant) e)) ∧ (∀(e : elt), Z.of_nat (map_occ_list e (nth_i a1) 0%Z (o2 + 1%Z)) + occ e t1 = Z.of_nat (map_occ_list e (nth_i a) 0%Z n)) -> sorted a1 ∧ a ≡ₚ a1))) ∧ (o2 + 1%Z < 0%Z -> sorted a ∧ a ≡ₚ a))))) ∧ (o1 + 1%Z < 0%Z -> (let o2 : Z := n - 1%Z in (0%Z ≤ o2 + 1%Z -> (sorted_sub a 0%Z 0%Z ∧ (heap empty ∧ Size.size empty = n - 0%Z) ∧ (∀(j : Z), 0%Z ≤ j ∧ j < 0%Z -> (∀(e : elt), mem e empty -> le (nth (Z.to_nat j) a inhabitant) e)) ∧ (∀(e : elt), Z.of_nat (map_occ_list e (nth_i a) 0%Z 0%Z) + occ e empty = Z.of_nat (map_occ_list e (nth_i a) 0%Z n))) ∧ (∀(t : tree elt) (a1 : list elt), length a1 = length a -> (∀(i : Z), (0%Z ≤ i ∧ i ≤ o2) ∧ sorted_sub a1 0%Z i ∧ (heap t ∧ Size.size t = n - i) ∧ (∀(j : Z), 0%Z ≤ j ∧ j < i -> (∀(e : elt), mem e t -> le (nth (Z.to_nat j) a1 inhabitant) e)) ∧ (∀(e : elt), Z.of_nat (map_occ_list e (nth_i a1) 0%Z i) + occ e t = Z.of_nat (map_occ_list e (nth_i a) 0%Z n)) -> (heap t ∧ 0%Z < Size.size t) ∧ (let o3 : elt := minimum t in (0%Z ≤ i ∧ i < Z.of_nat (length a1)) ∧ (length (set_list a1 (Z.to_nat i) o3) = length a1 -> nth_i (set_list a1 (Z.to_nat i) o3) = fun_updt (nth_i a1) i o3 -> (heap t ∧ 0%Z < Size.size t) ∧ (∀(o4 : tree elt), heap o4 ∧ occ (minimum t) o4 = occ (minimum t) t - 1%Z ∧ (∀(e : elt), ¬ e = minimum t -> occ e o4 = occ e t) ∧ Size.size o4 = Size.size t - 1%Z -> sorted_sub (set_list a1 (Z.to_nat i) o3) 0%Z (i + 1%Z) ∧ (heap o4 ∧ Size.size o4 = n - (i + 1%Z)) ∧ (∀(j : Z), 0%Z ≤ j ∧ j < i + 1%Z -> (∀(e : elt), mem e o4 -> le (nth (Z.to_nat j) (set_list a1 (Z.to_nat i) o3) inhabitant) e)) ∧ (∀(e : elt), Z.of_nat (map_occ_list e (nth_i (set_list a1 (Z.to_nat i) o3)) 0%Z (i + 1%Z)) + occ e o4 = Z.of_nat (map_occ_list e (nth_i a) 0%Z n)))))) ∧ (sorted_sub a1 0%Z (o2 + 1%Z) ∧ (heap t ∧ Size.size t = n - (o2 + 1%Z)) ∧ (∀(j : Z), 0%Z ≤ j ∧ j < o2 + 1%Z -> (∀(e : elt), mem e t -> le (nth (Z.to_nat j) a1 inhabitant) e)) ∧ (∀(e : elt), Z.of_nat (map_occ_list e (nth_i a1) 0%Z (o2 + 1%Z)) + occ e t = Z.of_nat (map_occ_list e (nth_i a) 0%Z n)) -> sorted a1 ∧ a ≡ₚ a1))) ∧ (o2 + 1%Z < 0%Z -> sorted a ∧ a ≡ₚ a))).
Admitted.
