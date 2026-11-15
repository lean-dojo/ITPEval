-- Statement-only formalization of "Feuerbach's Theorem" from Hundred Theorems item 029.
-- For a nondegenerate triangle, the nine-point circle is tangent to each inscribed or
-- escribed circle, expressed by equality of circles or a unique common point.
-- This file contains no proof.

namespace Theorems100.Feuerbach

universe u

/-- A Dedekind-complete linearly ordered field, used as a presentation of the real numbers. -/
structure RealScalar where
  Carrier : Type u
  zero : Carrier
  one : Carrier
  add : Carrier → Carrier → Carrier
  mul : Carrier → Carrier → Carrier
  neg : Carrier → Carrier
  inv : Carrier → Carrier
  le : Carrier → Carrier → Prop
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  add_comm : ∀ a b, add a b = add b a
  zero_add : ∀ a, add zero a = a
  add_neg : ∀ a, add (neg a) a = zero
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  mul_comm : ∀ a b, mul a b = mul b a
  one_mul : ∀ a, mul one a = a
  left_distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)
  zero_ne_one : zero ≠ one
  mul_inv : ∀ a, a ≠ zero → mul (inv a) a = one
  le_refl : ∀ a, le a a
  le_trans : ∀ a b c, le a b → le b c → le a c
  le_antisymm : ∀ a b, le a b → le b a → a = b
  le_total : ∀ a b, le a b ∨ le b a
  add_le_add_right : ∀ a b c, le a b → le (add a c) (add b c)
  mul_nonneg : ∀ a b, le zero a → le zero b → le zero (mul a b)
  complete :
    ∀ s : Carrier → Prop,
      (∃ x, s x) →
      (∃ upper, ∀ x, s x → le x upper) →
      ∃ leastUpper,
        (∀ x, s x → le x leastUpper) ∧
          ∀ upper, (∀ x, s x → le x upper) → le leastUpper upper

abbrev Real (K : RealScalar) := K.Carrier
abbrev Point (K : RealScalar) := Fin 2 → Real K

def sub (K : RealScalar) (x y : Real K) : Real K :=
  K.add x (K.neg y)

def sq (K : RealScalar) (x : Real K) : Real K :=
  K.mul x x

/-- Squared Euclidean distance between two points. -/
def distanceSq (K : RealScalar) (p q : Point K) : Real K :=
  K.add (sq K (sub K (q 0) (p 0))) (sq K (sub K (q 1) (p 1)))

/-- The point `m` is the midpoint of `a` and `b`. -/
def IsMidpoint (K : RealScalar) (a b m : Point K) : Prop :=
  K.mul (K.add K.one K.one) (m 0) = K.add (a 0) (b 0) ∧
    K.mul (K.add K.one K.one) (m 1) = K.add (a 1) (b 1)

/-- Three affine-plane points are collinear when their signed-area determinant vanishes. -/
def Collinear3 (K : RealScalar) (a b c : Point K) : Prop :=
  K.mul (sub K (a 0) (b 0)) (sub K (c 1) (b 1)) =
    K.mul (sub K (a 1) (b 1)) (sub K (c 0) (b 0))

/-- The directed lines `ab` and `cd` have perpendicular direction vectors. -/
def Perpendicular (K : RealScalar) (a b c d : Point K) : Prop :=
  K.add
      (K.mul (sub K (a 0) (b 0)) (sub K (c 0) (d 0)))
      (K.mul (sub K (a 1) (b 1)) (sub K (c 1) (d 1))) =
    K.zero

/-- A point lies on the circle with the given center and nonnegative radius. -/
def OnCircle (K : RealScalar) (center : Point K) (radius : Real K) (p : Point K) : Prop :=
  K.le K.zero radius ∧ distanceSq K center p = sq K radius

/-- Two circles are equal or meet at exactly one point. -/
def CirclesTangent (K : RealScalar)
    (center₁ : Point K) (radius₁ : Real K)
    (center₂ : Point K) (radius₂ : Real K) : Prop :=
  (center₁ = center₂ ∧ radius₁ = radius₂) ∨
    ∃ p : Point K,
      OnCircle K center₁ radius₁ p ∧
        OnCircle K center₂ radius₂ p ∧
          ∀ q : Point K,
            OnCircle K center₁ radius₁ q ∧ OnCircle K center₂ radius₂ q → q = p

/--
Feuerbach's theorem: the circle through the three side midpoints of a nondegenerate
triangle is tangent to any circle tangent to all three side lines.
-/
theorem feuerbach
    (K : RealScalar)
    (a b c mbc mac mab pbc pac pab ncenter icenter : Point K)
    (nradius iradius : Real K)
    (h_noncollinear : ¬Collinear3 K a b c)
    (h_mab : IsMidpoint K a b mab)
    (h_mbc : IsMidpoint K b c mbc)
    (h_mac : IsMidpoint K c a mac)
    (h_n_mbc : OnCircle K ncenter nradius mbc)
    (h_n_mac : OnCircle K ncenter nradius mac)
    (h_n_mab : OnCircle K ncenter nradius mab)
    (h_i_pbc : OnCircle K icenter iradius pbc)
    (h_i_pac : OnCircle K icenter iradius pac)
    (h_i_pab : OnCircle K icenter iradius pab)
    (h_pab_on_ab : Collinear3 K a b pab)
    (h_pab_perp : Perpendicular K a b icenter pab)
    (h_pbc_on_bc : Collinear3 K b c pbc)
    (h_pbc_perp : Perpendicular K b c icenter pbc)
    (h_pac_on_ac : Collinear3 K a c pac)
    (h_pac_perp : Perpendicular K a c icenter pac) :
    CirclesTangent K ncenter nradius icenter iradius := sorry

end Theorems100.Feuerbach
