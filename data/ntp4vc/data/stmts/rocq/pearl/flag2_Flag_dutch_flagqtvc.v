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
Open Scope Z_scope.
Inductive color :=
  | Blue : color
  | White : color
  | Red : color.
Axiom color_inhabited : Inhabited color.
Global Existing Instance color_inhabited.
Axiom color_countable : Countable color.
Global Existing Instance color_countable.
Definition monochrome (a : Z -> color) (i : Z) (j : Z) (c : color) := ∀(k : Z), i ≤ k ∧ k < j -> a k = c.
Axiom nb_occ : (Z -> color) -> Z -> Z -> color -> Z.
Axiom nb_occ'def : forall  (j : Z) (i : Z) (a : Z -> color) (c : color), if decide (j ≤ i) then nb_occ a i j c = 0%Z else if decide (a (j - 1%Z) = c) then nb_occ a i j c = 1%Z + nb_occ a i (j - 1%Z) c else nb_occ a i j c = nb_occ a i (j - 1%Z) c.
Theorem dutch_flag'vc (a : list color) : let o1 : Z := Z.of_nat (length a) in ((0%Z ≤ 0%Z ∧ 0%Z ≤ 0%Z ∧ 0%Z ≤ o1 ∧ o1 ≤ Z.of_nat (length a)) ∧ monochrome (nth_i a) 0%Z 0%Z Blue ∧ monochrome (nth_i a) 0%Z 0%Z White ∧ monochrome (nth_i a) o1 (Z.of_nat (length a)) Red) ∧ (∀(r : Z) (i : Z) (b : Z) (a1 : list color), length a1 = length a -> (0%Z ≤ b ∧ b ≤ i ∧ i ≤ r ∧ r ≤ Z.of_nat (length a1)) ∧ monochrome (nth_i a1) 0%Z b Blue ∧ monochrome (nth_i a1) b i White ∧ monochrome (nth_i a1) r (Z.of_nat (length a1)) Red ∧ (∀(c : color), nb_occ (nth_i a1) 0%Z (Z.of_nat (length a1)) c = nb_occ (nth_i a) 0%Z (Z.of_nat (length a1)) c) -> (if decide (i < r) then (0%Z ≤ i ∧ i < Z.of_nat (length a1)) ∧ (match nth (Z.to_nat i) a1 inhabitant with | Blue => ((0%Z ≤ b ∧ b < Z.of_nat (length a1)) ∧ 0%Z ≤ i ∧ i < Z.of_nat (length a1)) ∧ (∀(a2 : list color), length a2 = length a1 -> nth (Z.to_nat b) a2 inhabitant = nth (Z.to_nat i) a1 inhabitant ∧ nth (Z.to_nat i) a2 inhabitant = nth (Z.to_nat b) a1 inhabitant ∧ (∀(k : Z), ¬ k = b ∧ ¬ k = i -> nth (Z.to_nat k) a2 inhabitant = nth (Z.to_nat k) a1 inhabitant) ∧ (∀(k1 : Z) (k2 : Z) (c : color), (k1 ≤ b ∧ b < k2) ∧ k1 ≤ i ∧ i < k2 -> nb_occ (nth_i a2) k1 k2 c = nb_occ (nth_i a1) k1 k2 c) -> (0%Z ≤ r - i ∧ r - (i + 1%Z) < r - i) ∧ (0%Z ≤ b + 1%Z ∧ b + 1%Z ≤ i + 1%Z ∧ i + 1%Z ≤ r ∧ r ≤ Z.of_nat (length a2)) ∧ monochrome (nth_i a2) 0%Z (b + 1%Z) Blue ∧ monochrome (nth_i a2) (b + 1%Z) (i + 1%Z) White ∧ monochrome (nth_i a2) r (Z.of_nat (length a2)) Red ∧ (∀(c : color), nb_occ (nth_i a2) 0%Z (Z.of_nat (length a2)) c = nb_occ (nth_i a) 0%Z (Z.of_nat (length a2)) c)) | White => (0%Z ≤ r - i ∧ r - (i + 1%Z) < r - i) ∧ (0%Z ≤ b ∧ b ≤ i + 1%Z ∧ i + 1%Z ≤ r ∧ r ≤ Z.of_nat (length a1)) ∧ monochrome (nth_i a1) 0%Z b Blue ∧ monochrome (nth_i a1) b (i + 1%Z) White ∧ monochrome (nth_i a1) r (Z.of_nat (length a1)) Red ∧ (∀(c : color), nb_occ (nth_i a1) 0%Z (Z.of_nat (length a1)) c = nb_occ (nth_i a) 0%Z (Z.of_nat (length a1)) c) | Red => ((0%Z ≤ r - 1%Z ∧ r - 1%Z < Z.of_nat (length a1)) ∧ 0%Z ≤ i ∧ i < Z.of_nat (length a1)) ∧ (∀(a2 : list color), length a2 = length a1 -> nth (Z.to_nat (r - 1%Z)) a2 inhabitant = nth (Z.to_nat i) a1 inhabitant ∧ nth (Z.to_nat i) a2 inhabitant = nth (Z.to_nat (r - 1%Z)) a1 inhabitant ∧ (∀(k : Z), ¬ k = r - 1%Z ∧ ¬ k = i -> nth (Z.to_nat k) a2 inhabitant = nth (Z.to_nat k) a1 inhabitant) ∧ (∀(k1 : Z) (k2 : Z) (c : color), (k1 ≤ r - 1%Z ∧ r - 1%Z < k2) ∧ k1 ≤ i ∧ i < k2 -> nb_occ (nth_i a2) k1 k2 c = nb_occ (nth_i a1) k1 k2 c) -> (0%Z ≤ r - i ∧ r - 1%Z - i < r - i) ∧ (0%Z ≤ b ∧ b ≤ i ∧ i ≤ r - 1%Z ∧ r - 1%Z ≤ Z.of_nat (length a2)) ∧ monochrome (nth_i a2) 0%Z b Blue ∧ monochrome (nth_i a2) b i White ∧ monochrome (nth_i a2) (r - 1%Z) (Z.of_nat (length a2)) Red ∧ (∀(c : color), nb_occ (nth_i a2) 0%Z (Z.of_nat (length a2)) c = nb_occ (nth_i a) 0%Z (Z.of_nat (length a2)) c)) end) else (∃(b1 : Z) (r1 : Z), monochrome (nth_i a1) 0%Z b1 Blue ∧ monochrome (nth_i a1) b1 r1 White ∧ monochrome (nth_i a1) r1 (Z.of_nat (length a1)) Red) ∧ (∀(c : color), nb_occ (nth_i a1) 0%Z (Z.of_nat (length a1)) c = nb_occ (nth_i a) 0%Z (Z.of_nat (length a1)) c))).
Admitted.
