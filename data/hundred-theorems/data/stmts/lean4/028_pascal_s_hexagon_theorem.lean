-- Statement-only formalization of "Pascal's Hexagon Theorem" from Hundred Theorems item 028.
-- For a nondegenerate hexagon on an affine conic, its three opposite-side intersections are
-- collinear. This file contains no proof.

/-!
# Pascal's Hexagon Theorem

An affine form of Pascal's theorem over an abstract Dedekind-complete ordered field, hence
over a presentation of the real numbers. The six vertices are ordered around the hexagon,
and `P`, `Q`, and `R` lie on the three pairs of opposite sides.
-/

namespace Theorems100.PascalHexagon

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
abbrev Set (α : Type u) := α → Prop

def sub (K : RealScalar) (x y : Real K) : Real K :=
  K.add x (K.neg y)

def sq (K : RealScalar) (x : Real K) : Real K :=
  K.mul x x

/-- Three affine-plane points are collinear when their signed-area determinant vanishes. -/
def Collinear3 (K : RealScalar) (p q r : Point K) : Prop :=
  K.mul (sub K (q 0) (p 0)) (sub K (r 1) (p 1)) =
    K.mul (sub K (q 1) (p 1)) (sub K (r 0) (p 0))

/-- Evaluation of a general affine quadratic polynomial in two variables. -/
def quadraticValue (K : RealScalar)
    (a b c d e f : Real K) (x : Point K) : Real K :=
  K.add
    (K.add
      (K.add
        (K.mul a (sq K (x 0)))
        (K.mul b (sq K (x 1))))
      (K.mul c (K.mul (x 0) (x 1))))
    (K.add (K.mul d (x 0)) (K.add (K.mul e (x 1)) f))

/-- A nonzero quadratic equation defining a conic in the affine plane. -/
def AffineConic (K : RealScalar) (con : Set (Point K)) : Prop :=
  ∃ a b c d e f : Real K,
    ¬(a = K.zero ∧ b = K.zero ∧ c = K.zero ∧
      d = K.zero ∧ e = K.zero ∧ f = K.zero) ∧
      ∀ x, con x ↔ quadraticValue K a b c d e f x = K.zero

/-- The six vertices are pairwise distinct. -/
def PairwiseDistinct6 (A B C D E F : Point K) : Prop :=
  A ≠ B ∧ A ≠ C ∧ A ≠ D ∧ A ≠ E ∧ A ≠ F ∧
    B ≠ C ∧ B ≠ D ∧ B ≠ E ∧ B ≠ F ∧
    C ≠ D ∧ C ≠ E ∧ C ≠ F ∧
    D ≠ E ∧ D ≠ F ∧ E ≠ F

/--
The vertices are distinct, and no triple containing vertices from both alternating classes
`{A, C, E}` and `{B, D, F}` is collinear.
-/
def PascalNondegenerate (K : RealScalar) (A B C D E F : Point K) : Prop :=
  PairwiseDistinct6 A B C D E F ∧
    ¬Collinear3 K A C B ∧
    ¬Collinear3 K A C D ∧
    ¬Collinear3 K A C F ∧
    ¬Collinear3 K A E B ∧
    ¬Collinear3 K A E D ∧
    ¬Collinear3 K A E F ∧
    ¬Collinear3 K C E B ∧
    ¬Collinear3 K C E D ∧
    ¬Collinear3 K C E F ∧
    ¬Collinear3 K B D A ∧
    ¬Collinear3 K B D C ∧
    ¬Collinear3 K B D E ∧
    ¬Collinear3 K B F A ∧
    ¬Collinear3 K B F C ∧
    ¬Collinear3 K B F E ∧
    ¬Collinear3 K D F A ∧
    ¬Collinear3 K D F C ∧
    ¬Collinear3 K D F E

/-- `P`, `Q`, and `R` lie on the three pairs of opposite sides of the hexagon. -/
def PascalIntersections (K : RealScalar)
    (A B C D E F P Q R : Point K) : Prop :=
  Collinear3 K P A B ∧
    Collinear3 K P D E ∧
    Collinear3 K Q B C ∧
    Collinear3 K Q E F ∧
    Collinear3 K R C D ∧
    Collinear3 K R F A

/-- **Pascal's hexagon theorem** for an affine conic. -/
theorem pascal_hexagon_theorem
    (K : RealScalar)
    {con : Set (Point K)} {A B C D E F P Q R : Point K}
    (hnondegenerate : PascalNondegenerate K A B C D E F)
    (hconic : AffineConic K con)
    (honConic : con A ∧ con B ∧ con C ∧ con D ∧ con E ∧ con F)
    (hintersections : PascalIntersections K A B C D E F P Q R) :
    Collinear3 K P Q R := sorry

end Theorems100.PascalHexagon
