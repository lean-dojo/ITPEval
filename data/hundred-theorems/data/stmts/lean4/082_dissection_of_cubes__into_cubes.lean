/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.Algebra.Order.Interval.Set.Group
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Order.Interval.Set.Disjoint

/-!
# Dissection of Cubes

Proof that a cube (in dimension n ≥ 3) cannot be cubed:
There does not exist a partition of a cube into finitely many smaller cubes (at least two)
of different sizes.

We follow the proof described here:
http://www.alaricstephen.com/main-featured/2017/9/28/cubing-a-cube-proof
-/


open Real Set Function Fin

namespace Theorems100

noncomputable section

namespace «82»

variable {n : ℕ}

/-- Given three intervals `I, J, K` such that `J ⊂ I`,
  neither endpoint of `J` coincides with an endpoint of `I`, `¬ (K ⊆ J)` and
  `K` does not lie completely to the left nor completely to the right of `J`.
  Then `I ∩ K \ J` is nonempty. -/
theorem Ico_lemma {α} [LinearOrder α] {x₁ x₂ y₁ y₂ z₁ z₂ w : α} (h₁ : x₁ < y₁) (hy : y₁ < y₂)
    (h₂ : y₂ < x₂) (hz₁ : z₁ ≤ y₂) (hz₂ : y₁ ≤ z₂) (hw : w ∉ Ico y₁ y₂ ∧ w ∈ Ico z₁ z₂) :
    ∃ w, w ∈ Ico x₁ x₂ ∧ w ∉ Ico y₁ y₂ ∧ w ∈ Ico z₁ z₂ := by sorry
structure Cube (n : ℕ) : Type where
  b : Fin n → ℝ -- bottom-left coordinate
  w : ℝ -- width
  hw : 0 < w

namespace Cube

theorem hw' (c : Cube n) : 0 ≤ c.w :=
  le_of_lt c.hw

/-- The j-th side of a cube is the half-open interval `[b j, b j + w)` -/
def side (c : Cube n) (j : Fin n) : Set ℝ :=
  Ico (c.b j) (c.b j + c.w)

@[simp]
theorem b_mem_side (c : Cube n) (j : Fin n) : c.b j ∈ c.side j := by simp [side, Cube.hw]

def toSet (c : Cube n) : Set (Fin n → ℝ) :=
  {x | ∀ j, x j ∈ side c j}

theorem side_nonempty (c : Cube n) (i : Fin n) : (side c i).Nonempty := by simp [side, c.hw]

theorem univ_pi_side (c : Cube n) : pi univ (side c) = c.toSet :=
  ext fun _ => mem_univ_pi

theorem toSet_subset {c c' : Cube n} : c.toSet ⊆ c'.toSet ↔ ∀ j, c.side j ⊆ c'.side j := by sorry
theorem toSet_disjoint {c c' : Cube n} :
    Disjoint c.toSet c'.toSet ↔ ∃ j, Disjoint (c.side j) (c'.side j) := by sorry
theorem b_mem_toSet (c : Cube n) : c.b ∈ c.toSet := by simp [toSet]

protected def tail (c : Cube (n + 1)) : Cube n :=
  ⟨tail c.b, c.w, c.hw⟩

theorem side_tail (c : Cube (n + 1)) (j : Fin n) : c.tail.side j = c.side j.succ :=
  rfl

def bottom (c : Cube (n + 1)) : Set (Fin (n + 1) → ℝ) :=
  {x | x 0 = c.b 0 ∧ tail x ∈ c.tail.toSet}

theorem b_mem_bottom (c : Cube (n + 1)) : c.b ∈ c.bottom := by sorry
def xm (c : Cube (n + 1)) : ℝ :=
  c.b 0 + c.w

theorem b_lt_xm (c : Cube (n + 1)) : c.b 0 < c.xm := by simp [xm, hw]

theorem b_ne_xm (c : Cube (n + 1)) : c.b 0 ≠ c.xm :=
  ne_of_lt c.b_lt_xm

def shiftUp (c : Cube (n + 1)) : Cube (n + 1) :=
  ⟨cons c.xm <| tail c.b, c.w, c.hw⟩

@[simp]
theorem tail_shiftUp (c : Cube (n + 1)) : c.shiftUp.tail = c.tail := by simp [shiftUp, Cube.tail]

@[simp]
theorem head_shiftUp (c : Cube (n + 1)) : c.shiftUp.b 0 = c.xm :=
  rfl

def unitCube : Cube n :=
  ⟨fun _ => 0, 1, by simp⟩

@[simp]
theorem side_unitCube {j : Fin n} : unitCube.side j = Ico 0 1 := by sorry
end Cube

open Cube

variable {ι : Type} {cs : ι → Cube (n + 1)} {i i' : ι}

/-- A finite family of (at least 2) cubes partitioning the unit cube with different sizes -/
structure Correct (cs : ι → Cube n) : Prop where
  PairwiseDisjoint : Pairwise (Disjoint on Cube.toSet ∘ cs)
  iUnion_eq : ⋃ i : ι, (cs i).toSet = unitCube.toSet
  Injective : Injective (Cube.w ∘ cs)
  three_le : 3 ≤ n

namespace Correct

variable (h : Correct cs)
include h

theorem toSet_subset_unitCube {i} : (cs i).toSet ⊆ unitCube.toSet := by sorry
theorem side_subset {i j} : (cs i).side j ⊆ Ico 0 1 := by sorry
theorem zero_le_of_mem_side {i j x} (hx : x ∈ (cs i).side j) : 0 ≤ x :=
  (side_subset h hx).1

theorem zero_le_of_mem {i p} (hp : p ∈ (cs i).toSet) (j) : 0 ≤ p j :=
  zero_le_of_mem_side h (hp j)

theorem zero_le_b {i j} : 0 ≤ (cs i).b j :=
  zero_le_of_mem h (cs i).b_mem_toSet j

theorem b_add_w_le_one {j} : (cs i).b j + (cs i).w ≤ 1 := by sorry
theorem nontrivial_fin : Nontrivial (Fin n) :=
  Fin.nontrivial_iff_two_le.2 (Nat.le_of_succ_le_succ h.three_le)

/-- The width of any cube in the partition cannot be 1. -/
theorem w_ne_one [Nontrivial ι] (i : ι) : (cs i).w ≠ 1 := by sorry
theorem shiftUp_bottom_subset_bottoms (hc : (cs i).xm ≠ 1) :
    (cs i).shiftUp.bottom ⊆ ⋃ i : ι, (cs i).bottom := by sorry
end Correct

/-- A valley is a square on which cubes in the family of cubes are placed, so that the cubes
  completely cover the valley and none of those cubes is partially outside the square.
  We also require that no cube on it has the same size as the valley (so that there are at least
  two cubes on the valley).
  This is the main concept in the formalization.
  We prove that the smallest cube on a valley has another valley on the top of it, which
  gives an infinite sequence of cubes in the partition, which contradicts the finiteness.
  A valley is characterized by a cube `c` (which is not a cube in the family `cs`) by considering
  the bottom face of `c`. -/
def Valley (cs : ι → Cube (n + 1)) (c : Cube (n + 1)) : Prop :=
  (c.bottom ⊆ ⋃ i : ι, (cs i).bottom) ∧
  (∀ i, (cs i).b 0 = c.b 0 →
    (∃ x, x ∈ (cs i).tail.toSet ∩ c.tail.toSet) → (cs i).tail.toSet ⊆ c.tail.toSet) ∧
  ∀ i : ι, (cs i).b 0 = c.b 0 → (cs i).w ≠ c.w

variable {c : Cube (n + 1)} (h : Correct cs) (v : Valley cs c)

/-- The bottom of the unit cube is a valley -/
theorem valley_unitCube [Nontrivial ι] (h : Correct cs) : Valley cs unitCube := by sorry
def bcubes (cs : ι → Cube (n + 1)) (c : Cube (n + 1)) : Set ι :=
  {i : ι | (cs i).b 0 = c.b 0 ∧ (cs i).tail.toSet ⊆ c.tail.toSet}

/-- A cube which lies on the boundary of a valley in dimension `j` -/
def OnBoundary (_ : i ∈ bcubes cs c) (j : Fin n) : Prop :=
  c.b j.succ = (cs i).b j.succ ∨ (cs i).b j.succ + (cs i).w = c.b j.succ + c.w

theorem tail_sub (hi : i ∈ bcubes cs c) : ∀ j, (cs i).tail.side j ⊆ c.tail.side j := by sorry
theorem bottom_mem_side (hi : i ∈ bcubes cs c) : c.b 0 ∈ (cs i).side 0 := by sorry
theorem b_le_b (hi : i ∈ bcubes cs c) (j : Fin n) : c.b j.succ ≤ (cs i).b j.succ :=
  (tail_sub hi j <| b_mem_side _ _).1

theorem t_le_t (hi : i ∈ bcubes cs c) (j : Fin n) :
    (cs i).b j.succ + (cs i).w ≤ c.b j.succ + c.w := by sorry
theorem w_lt_w (hi : i ∈ bcubes cs c) : (cs i).w < c.w := by sorry
theorem nontrivial_bcubes : (bcubes cs c).Nontrivial := by sorry
theorem nonempty_bcubes : (bcubes cs c).Nonempty :=
  (nontrivial_bcubes h v).nonempty

variable [Finite ι]

/-- There is a smallest cube in the valley -/
theorem exists_mi : ∃ i ∈ bcubes cs c, ∀ i' ∈ bcubes cs c, (cs i).w ≤ (cs i').w :=
  (bcubes cs c).exists_min_image (fun i => (cs i).w) (Set.toFinite _) (nonempty_bcubes h v)

/-- We let `mi` be the (index for the) smallest cube in the valley `c` -/
def mi : ι :=
  Classical.choose <| exists_mi h v

variable {h v}

theorem mi_mem_bcubes : mi h v ∈ bcubes cs c :=
  (Classical.choose_spec <| exists_mi h v).1

theorem mi_minimal (hi : i ∈ bcubes cs c) : (cs <| mi h v).w ≤ (cs i).w :=
  (Classical.choose_spec <| exists_mi h v).2 i hi

theorem mi_strict_minimal (hii' : mi h v ≠ i) (hi : i ∈ bcubes cs c) :
    (cs <| mi h v).w < (cs i).w :=
  (mi_minimal hi).lt_of_ne <| h.Injective.ne hii'

/-- The top of `mi` cannot be 1, since there is a larger cube in the valley -/
theorem mi_xm_ne_one : (cs <| mi h v).xm ≠ 1 := by sorry
theorem smallest_onBoundary {j} (bi : OnBoundary (mi_mem_bcubes : mi h v ∈ _) j) :
    ∃ x : ℝ, x ∈ c.side j.succ \ (cs <| mi h v).side j.succ ∧
      ∀ ⦃i'⦄ (_ : i' ∈ bcubes cs c),
        i' ≠ mi h v → (cs <| mi h v).b j.succ ∈ (cs i').side j.succ → x ∈ (cs i').side j.succ := by sorry
variable (h v)

/-- `mi` cannot lie on the boundary of the valley. Otherwise, the cube adjacent to it in the `j`-th
  direction will intersect one of the neighbouring cubes on the same boundary as `mi`. -/
theorem mi_not_onBoundary (j : Fin n) : ¬OnBoundary (mi_mem_bcubes : mi h v ∈ _) j := by sorry
variable {h v}

/-- The same result that `mi` cannot lie on the boundary of the valley written as inequalities. -/
theorem mi_not_onBoundary' (j : Fin n) :
    c.tail.b j < (cs (mi h v)).tail.b j ∧
      (cs (mi h v)).tail.b j + (cs (mi h v)).w < c.tail.b j + c.w := by sorry
theorem valley_mi : Valley cs (cs (mi h v)).shiftUp := by sorry
variable (h) [Nontrivial ι]

/-- We get a sequence of cubes whose size is decreasing -/
noncomputable def sequenceOfCubes : ℕ → { i : ι // Valley cs (cs i).shiftUp }
  | 0 =>
    let v := valley_unitCube h
    ⟨mi h v, valley_mi⟩
  | k + 1 =>
    let v := (sequenceOfCubes k).2
    ⟨mi h v, valley_mi⟩

def decreasingSequence (k : ℕ) : ℝ :=
  (cs (sequenceOfCubes h k).1).w

end

variable [Finite ι] [Nontrivial ι]

include h in
theorem strictAnti_sequenceOfCubes : StrictAnti <| decreasingSequence h :=
  strictAnti_nat_of_succ_lt fun k => by
    let v := (sequenceOfCubes h k).2; dsimp only [decreasingSequence, sequenceOfCubes]
    apply w_lt_w h v (mi_mem_bcubes : mi h v ∈ _)

theorem injective_sequenceOfCubes : Injective (sequenceOfCubes h) :=
  @Injective.of_comp _ _ _ (fun x : { _i : ι // _ } => (cs x.1).w) _
    (strictAnti_sequenceOfCubes h).injective

/-- The infinite sequence of cubes contradicts the finiteness of the family. -/
theorem not_correct : ¬Correct cs := fun h =>
  (Finite.of_injective _ <| injective_sequenceOfCubes h).false

/-- **Dissection of Cubes**: A cube cannot be cubed. -/
theorem cannot_cube_a_cube :
    ∀ {n : ℕ}, n ≥ 3 →                         -- In ℝ^n for n ≥ 3
    ∀ {s : Set (Cube n)}, s.Finite →           -- given a finite collection of (hyper)cubes
    s.Nontrivial →                             -- containing at least two elements
    s.PairwiseDisjoint Cube.toSet →            -- which is pairwise disjoint
    ⋃ c ∈ s, Cube.toSet c = unitCube.toSet →   -- whose union is the unit cube
    InjOn Cube.w s →                           -- such that the widths of all cubes are different
    False := by                                -- then we can derive a contradiction
  intro n hn s hfin h2 hd hU hinj
  rcases n with - | n
  · cases hn
  exact @not_correct n s (↑) hfin.to_subtype h2.coe_sort
    ⟨hd.subtype _ _, (iUnion_subtype _ _).trans hU, hinj.injective, hn⟩

end «82»

end

end Theorems100
