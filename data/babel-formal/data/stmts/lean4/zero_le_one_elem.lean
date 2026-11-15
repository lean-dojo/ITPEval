universe u

class DecidableEqAlt (A : Type u) where
  decEq : (x y : A) → Bool

class ZeroAlt (A : Type u) where
  zero : A

class OneAlt (A : Type u) where
  one : A

class Preorder (A : Type u) where
  le    : A → A → Prop
  refl  : ∀ x, le x x
  trans : ∀ {x y z}, le x y → le y z → le x z

infix:50 " ≤ " => Preorder.le

class ZeroLEOneClass (A : Type u) [ZeroAlt A] [OneAlt A] [Preorder A] : Prop where
  zero_le_one  : (ZeroAlt.zero : A) ≤ (OneAlt.one : A)
  zero_le_zero : (ZeroAlt.zero : A) ≤ (ZeroAlt.zero : A)

namespace Matrix
  variable (m : Type u) [DecidableEqAlt m]
  variable (α : Type u) [ZeroAlt α] [OneAlt α] [Preorder α] [ZeroLEOneClass α]
  abbrev matrix := m → m → α


  def One_matrix : matrix m α :=
      fun i j => if DecidableEqAlt.decEq i j then OneAlt.one else ZeroAlt.zero

  theorem zero_le_one_elem
    (i j : m) : (ZeroAlt.zero : α) ≤ One_matrix m α i j := by sorry
  def Zero_matrix : matrix m α := fun _ _ => ZeroAlt.zero

  def matrix_le (A B : matrix m α) : Prop := ∀ i j, A i j ≤ B i j

  theorem Zero_le_One_matrix : matrix_le m α (Zero_matrix m α) (One_matrix m α) := by sorry
  theorem matrix_le_refl (A : matrix m α) : matrix_le m α A A := by sorry
  theorem matrix_le_trans (A B C : matrix m α) :
      matrix_le m α A B → matrix_le m α B C → matrix_le m α A C := by sorry
  def matrix_eq (A B : matrix m α) : Prop := ∀ i j, A i j = B i j

  theorem matrix_eq_refl (A : matrix m α) : matrix_eq m α A A := by sorry
  theorem matrix_eq_sym (A B : matrix m α) : matrix_eq m α A B → matrix_eq m α B A := by sorry
  theorem matrix_eq_trans (A B C : matrix m α) :
      matrix_eq m α A B → matrix_eq m α B C → matrix_eq m α A C := by sorry
  theorem matrix_eq_le (A B : matrix m α) :
      matrix_eq m α A B → matrix_le m α A B ∧ matrix_le m α B A := by sorry
  class PartialOrder (A : Type u) [Preorder A] : Prop where
    le_antisym : ∀ {x y : A}, x ≤ y → y ≤ x → x = y

  variable [PartialOrder α]

  theorem matrix_le_antisymm (A B : matrix m α) :
      matrix_le m α A B → matrix_le m α B A → matrix_eq m α A B := by sorry
end Matrix
