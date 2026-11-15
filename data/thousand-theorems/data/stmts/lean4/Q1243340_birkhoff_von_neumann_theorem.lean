-- Statement-only formalization of Thousand Theorems artifact Q1243340
-- (thousand-theorems__lean4__Q1243340), "Birkhoff–Von Neumann theorem": the set
-- of doubly stochastic matrices over a strictly ordered field is the convex hull
-- of the permutation matrices. This file contains no proof.

namespace Q1243340Support

universe u v

/-- An explicit presentation of a strictly ordered field. -/
class StrictOrderedField (R : Type u) where
  zero : R
  one : R
  add : R → R → R
  neg : R → R
  mul : R → R → R
  inv : R → R
  le : R → R → Prop
  decidableLE : DecidableRel le
  add_assoc : ∀ a b c : R, add (add a b) c = add a (add b c)
  add_comm : ∀ a b : R, add a b = add b a
  zero_add : ∀ a : R, add zero a = a
  add_left_neg : ∀ a : R, add (neg a) a = zero
  mul_assoc : ∀ a b c : R, mul (mul a b) c = mul a (mul b c)
  mul_comm : ∀ a b : R, mul a b = mul b a
  one_mul : ∀ a : R, mul one a = a
  left_distrib : ∀ a b c : R, mul a (add b c) = add (mul a b) (mul a c)
  inv_zero : inv zero = zero
  mul_inv_cancel : ∀ a : R, a ≠ zero → mul a (inv a) = one
  le_refl : ∀ a : R, le a a
  le_trans : ∀ a b c : R, le a b → le b c → le a c
  le_antisymm : ∀ a b : R, le a b → le b a → a = b
  le_total : ∀ a b : R, le a b ∨ le b a
  add_le_add_left : ∀ a b c : R, le a b → le (add c a) (add c b)
  zero_lt_one : le zero one ∧ zero ≠ one
  mul_pos : ∀ a b : R,
    le zero a → a ≠ zero → le zero b → b ≠ zero →
      le zero (mul a b) ∧ mul a b ≠ zero

def ListMem {α : Type u} (x : α) : List α → Prop
  | [] => False
  | y :: ys => x = y ∨ ListMem x ys

def ListNodup {α : Type u} : List α → Prop
  | [] => True
  | x :: xs => ¬ListMem x xs ∧ ListNodup xs

/-- A duplicate-free enumeration of a finite type. -/
class FiniteType (n : Type u) where
  elements : List n
  nodup : ListNodup elements
  complete : ∀ i : n, ListMem i elements

abbrev Matrix (n : Type u) (R : Type v) := n → n → R

/-- A permutation presented together with a two-sided inverse. -/
structure Permutation (n : Type u) where
  toFun : n → n
  invFun : n → n
  left_inv : ∀ i, invFun (toFun i) = i
  right_inv : ∀ i, toFun (invFun i) = i

def sumOnList {R : Type u} {α : Type v} (K : StrictOrderedField R) (f : α → R) :
    List α → R
  | [] => K.zero
  | x :: xs => K.add (f x) (sumOnList K f xs)

def finiteSum {R : Type u} {n : Type v} (K : StrictOrderedField R) (F : FiniteType n)
    (f : n → R) : R :=
  sumOnList K f F.elements

def matrixZero {R : Type u} {n : Type v} (K : StrictOrderedField R) : Matrix n R :=
  fun _ _ => K.zero

def matrixAdd {R : Type u} {n : Type v} (K : StrictOrderedField R)
    (A B : Matrix n R) : Matrix n R :=
  fun i j => K.add (A i j) (B i j)

def matrixSmul {R : Type u} {n : Type v} (K : StrictOrderedField R) (a : R)
    (A : Matrix n R) : Matrix n R :=
  fun i j => K.mul a (A i j)

def permMatrix {R : Type u} {n : Type v} (K : StrictOrderedField R) [DecidableEq n]
    (σ : Permutation n) : Matrix n R :=
  fun i j => if σ.toFun i = j then K.one else K.zero

/-- Entrywise nonnegative matrices whose rows and columns each sum to one. -/
def doublyStochastic {R : Type u} {n : Type v} (K : StrictOrderedField R)
    (F : FiniteType n) : Matrix n R → Prop :=
  fun M =>
    (∀ i j, K.le K.zero (M i j)) ∧
      (∀ i, finiteSum K F (fun j => M i j) = K.one) ∧
      ∀ j, finiteSum K F (fun i => M i j) = K.one

def SameLength {α : Type u} {β : Type v} : List α → List β → Prop
  | [], [] => True
  | _ :: xs, _ :: ys => SameLength xs ys
  | _, _ => False

def AllNonnegative {R : Type u} (K : StrictOrderedField R) : List R → Prop
  | [] => True
  | w :: ws => K.le K.zero w ∧ AllNonnegative K ws

def weightedPermSum {R : Type u} {n : Type v} (K : StrictOrderedField R) [DecidableEq n] :
    List R → List (Permutation n) → Matrix n R
  | w :: ws, σ :: σs =>
      matrixAdd K (matrixSmul K w (permMatrix K σ)) (weightedPermSum K ws σs)
  | _, _ => matrixZero K

/-- Membership in the convex hull of the permutation matrices. -/
def convexHullPermutationMatrices {R : Type u} {n : Type v} (K : StrictOrderedField R)
    [DecidableEq n] : Matrix n R → Prop :=
  fun M =>
    ∃ weights : List R, ∃ permutations : List (Permutation n),
      SameLength weights permutations ∧
        AllNonnegative K weights ∧
        sumOnList K (fun w => w) weights = K.one ∧
        weightedPermSum K weights permutations = M

end Q1243340Support

open Q1243340Support

universe u v

variable {R : Type u} {n : Type v}
variable [K : StrictOrderedField R] [F : FiniteType n] [DecidableEq n]

/-- The Birkhoff–Von Neumann characterization of doubly stochastic matrices. -/
theorem doublyStochastic_eq_convexHull_permMatrix :
    doublyStochastic K F = convexHullPermutationMatrices K := sorry
