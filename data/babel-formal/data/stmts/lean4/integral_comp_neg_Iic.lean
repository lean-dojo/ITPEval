class RField (R : Type) where
  zero   : R
  one    : R
  add    : R → R → R
  opp    : R → R
  mul    : R → R → R
  le     : R → R → Prop
  lt     : R → R → Prop
  abs    : R → R

  add_comm      : ∀ x y, add x y = add y x
  add_assoc     : ∀ x y z, add (add x y) z = add x (add y z)
  add_zero      : ∀ x, add x zero = x
  add_opp       : ∀ x, add (opp x) x = zero
  add_right_cancel : ∀ x y z, add x z = add y z → x = y

  mul_comm      : ∀ x y, mul x y = mul y x
  mul_assoc     : ∀ x y z, mul (mul x y) z = mul x (mul y z)
  mul_one       : ∀ x, mul x one = x
  dist_l        : ∀ x y z, mul x (add y z) = add (mul x y) (mul x z)
  opp_involutive : ∀ x, opp (opp x) = x

  add_le_compat : ∀ x y z, le x y → le (add x z) (add y z)
  mul_le_compat : ∀ x y z, le zero z → le x y → le (mul x z) (mul y z)
  zero_le_one   : le zero one
  le_total      : ∀ x y, le x y ∨ le y x

  le_dec : ∀ x y, (le x y) ∨ ¬ (le x y)

  le_opp        : ∀ x y, le x y → le (opp y) (opp x)
  le_antisymm   : ∀ x y, le x y → le y x → x = y
  lt_opp        : ∀ x y, lt x y → lt (opp y) (opp x)
  le_refl       : ∀ x, le x x
  le_trans      : ∀ x y z, le x y → le y z → le x z
  lt_def        : ∀ x y, lt x y ↔ (le x y ∧ x ≠ y)

  abs_pos       : ∀ x, le zero x → abs x = x
  abs_neg       : ∀ x, le x zero → abs x = opp x
  abs_nonneg    : ∀ x, le zero (abs x)
  abs_opp       : ∀ x, abs (opp x) = abs x
  abs_triangle  : ∀ x y, le (abs (add x y)) (add (abs x) (abs y))

class Integral (R : Type) [RField R] where
  sigma       : (R → Prop) → (R → R) → R
  sigma_mul_const : ∀ (D : R → Prop) (f : R → R) (c : R),
    sigma D (fun x => RField.mul c (f x)) = RField.mul c (sigma D f)
  sigma_congr : ∀ D f g, (∀ x, D x → f x = g x) → sigma D f = sigma D g
  sigma_zero  : ∀ D, sigma D (fun _ => RField.zero) = RField.zero
  sigma_add   : ∀ D f g, sigma D (fun x => RField.add (f x) (g x)) = RField.add (sigma D f) (sigma D g)

  sigma_union_disjoint : ∀ (D E : R → Prop) (f : R → R),
    (∀ x, D x → E x → False) →
    sigma (fun x => D x ∨ E x) f = RField.add (sigma D f) (sigma E f)
  sigma_le : ∀ D f g, (∀ x, D x → RField.le (f x) (g x)) → RField.le (sigma D f) (sigma D g)
  sigma_dom_congr : ∀ D E f, (∀ x, D x ↔ E x) → sigma D f = sigma E f

namespace Integrals

variable {R : Type} [RF : RField R] [I : Integral R]
open RField
open Integral

-- Notations
prefix:100 "-" => opp
infixl:65 " + " => add
infixl:70 " * " => mul
infixl:70 " <= " => le
infixl:70 " < " => lt

-- Domains
def Iic (c : R) : R → Prop := fun x => x <= c
def Ioi (c : R) : R → Prop := fun x => c < x
def Iio (c : R) : R → Prop := fun x => x < c
def union (D E : R → Prop) : R → Prop := fun x => D x ∨ E x
def inter (D E : R → Prop) : R → Prop := fun x => D x ∧ E x

-- Lemma lt_irrefl
theorem lt_irrefl (x : R) : ¬ (x < x) := by sorry
theorem lt_trans_strict (x y z : R) (Hxy : x < y) (Hyz : y < z) : x < z := by sorry
def preimage (g : R → R) (D : R → Prop) : R → Prop :=
  fun x => D (g x)

theorem preimage_union (D E : R → Prop) (g : R → R) (x : R) :
  preimage g (union D E) x ↔ preimage g D x ∨ preimage g E x := by sorry
theorem preimage_inter (D E : R → Prop) (g : R → R) (x : R) :
  preimage g (inter D E) x ↔ preimage g D x ∧ preimage g E x := by sorry
theorem preimage_neg_Ioi (c x : R) :
  preimage opp (Ioi c) x ↔ x < opp c := by sorry
theorem preimage_neg_Iic (c x : R) :
  preimage opp (Iic c) x ↔ Iic x (opp c) := by sorry
theorem preimage_comp (D : R → Prop) (g h : R → R) (x : R) :
  preimage g (preimage h D) x ↔ preimage (fun x => h (g x)) D x := by sorry
theorem integral_neg (D : R → Prop) (f : R → R) :
  sigma D (fun x => opp (f x)) = opp (sigma D f) := by sorry
theorem integral_sub (D : R → Prop) (f g : R → R) :
  sigma D (fun x => add (f x) (opp (g x))) = add (sigma D f) (opp (sigma D g)) := by sorry
theorem sigma_empty (f : R → R) :
  sigma (fun _ => False) f = zero := by sorry
theorem sigma_bilinear (D : R → Prop) (f g : R → R) (c d : R) :
  sigma D (fun x => add (mul c (f x)) (mul d (g x))) =
    add (mul c (sigma D f)) (mul d (sigma D g)) := by sorry
theorem sigma_le_monotone (D : R → Prop) (f g : R → R) :
  (∀ x, D x → le (f x) (g x)) → le (sigma D f) (sigma D g) := by sorry
theorem sigma_nonneg (D : R → Prop) (f : R → R) :
  (∀ x, D x → le zero (f x)) → le zero (sigma D f) := by sorry
theorem sigma_split (D : R → Prop) (P : R → Prop) (f : R → R)
  (P_dec : ∀ x, D x → P x ∨ ¬ P x) :
  sigma D f =
    add (sigma (fun x => D x ∧ P x) f)
        (sigma (fun x => D x ∧ ¬ P x) f) := by sorry
theorem sigma_preimage_neg_Ioi (f : R → R) (c : R) :
  sigma (preimage opp (Ioi c)) f = sigma (Iio (opp c)) f := by sorry
theorem sigma_abs_bound (D : R → Prop) (f : R → R) :
  le (abs (sigma D f)) (sigma D (fun x => abs (f x))) := by sorry
end Integrals
