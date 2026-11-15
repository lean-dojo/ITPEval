-- Statement-only formalization of Thousand Theorems artifact Q203565
-- (thousand-theorems__lean4__Q203565), "Solutions of a general cubic equation":
-- over a field with invertible 2 and 3 and a primitive cube root of unity, Cardano's
-- auxiliary quantities characterize exactly the three roots of a cubic.
-- This file contains no proof.

module

public section

namespace Theorems100

universe u

/-- A commutative field, presented by its operations and defining laws. -/
class Field (K : Type u) where
  zero : K
  one : K
  add : K → K → K
  mul : K → K → K
  neg : K → K
  inv : K → K
  zero_ne_one : zero ≠ one
  add_assoc : ∀ x y z, add (add x y) z = add x (add y z)
  add_comm : ∀ x y, add x y = add y x
  zero_add : ∀ x, add zero x = x
  add_left_neg : ∀ x, add (neg x) x = zero
  mul_assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z)
  mul_comm : ∀ x y, mul x y = mul y x
  one_mul : ∀ x, mul one x = x
  left_distrib : ∀ x y z, mul x (add y z) = add (mul x y) (mul x z)
  inv_zero : inv zero = zero
  mul_inv_cancel : ∀ x, x ≠ zero → mul x (inv x) = one

/-- Subtraction in the explicitly presented field. -/
def fieldSub {K : Type u} [Field K] (x y : K) : K :=
  Field.add x (Field.neg y)

/-- Division in the explicitly presented field. -/
def fieldDiv {K : Type u} [Field K] (x y : K) : K :=
  Field.mul x (Field.inv y)

/-- Natural powers in the explicitly presented field. -/
def fieldPow {K : Type u} [Field K] (x : K) : Nat → K
  | 0 => Field.one
  | n + 1 => Field.mul (fieldPow x n) x

/-- The canonical image of a natural number in the explicitly presented field. -/
def fieldNat {K : Type u} [Field K] : Nat → K
  | 0 => Field.zero
  | n + 1 => Field.add (fieldNat n) Field.one

/-- An element whose multiplicative inverse is explicitly available. -/
class Invertible {K : Type u} [Field K] (x : K) where
  inverse : K
  inverse_mul_self : Field.mul inverse x = Field.one
  self_mul_inverse : Field.mul x inverse = Field.one

/-- An element is a primitive `n`th root when its powers equal one exactly at multiples of `n`. -/
def IsPrimitiveRoot {K : Type u} [Field K] (ω : K) (n : Nat) : Prop :=
  fieldPow ω n = Field.one ∧
    ∀ m, fieldPow ω m = Field.one ↔ ∃ k, m = n * k

variable {K : Type u} [Field K] (a b c d : K) {ω p q r s t : K}
variable [Invertible (fieldNat (K := K) 2)] [Invertible (fieldNat (K := K) 3)]

/-- The roots of a cubic polynomial whose Cardano parameter `p` is nonzero. -/
theorem cubic_eq_zero_iff (ha : a ≠ Field.zero) (hω : IsPrimitiveRoot ω 3)
    (hp : p =
      fieldDiv
        (fieldSub
          (Field.mul (Field.mul (fieldNat 3) a) c)
          (fieldPow b 2))
        (Field.mul (fieldNat 9) (fieldPow a 2)))
    (hp_nonzero : p ≠ Field.zero)
    (hq : q =
      fieldDiv
        (fieldSub
          (fieldSub
            (Field.mul (Field.mul (Field.mul (fieldNat 9) a) b) c)
            (Field.mul (fieldNat 2) (fieldPow b 3)))
          (Field.mul (Field.mul (fieldNat 27) (fieldPow a 2)) d))
        (Field.mul (fieldNat 54) (fieldPow a 3)))
    (hr : fieldPow r 2 = Field.add (fieldPow q 2) (fieldPow p 3))
    (hs3 : fieldPow s 3 = Field.add q r)
    (ht : Field.mul t s = p)
    (x : K) :
    Field.add
          (Field.add
            (Field.add
              (Field.mul a (fieldPow x 3))
              (Field.mul b (fieldPow x 2)))
            (Field.mul c x))
          d =
        Field.zero ↔
      x =
          fieldSub
            (fieldSub s t)
            (fieldDiv b (Field.mul (fieldNat 3) a)) ∨
        x =
            fieldSub
              (fieldSub
                (Field.mul s ω)
                (Field.mul t (fieldPow ω 2)))
              (fieldDiv b (Field.mul (fieldNat 3) a)) ∨
          x =
            fieldSub
              (fieldSub
                (Field.mul s (fieldPow ω 2))
                (Field.mul t ω))
              (fieldDiv b (Field.mul (fieldNat 3) a)) := sorry

end Theorems100
