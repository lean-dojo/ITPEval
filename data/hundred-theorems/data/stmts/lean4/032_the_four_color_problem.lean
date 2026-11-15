-- Statement-only formalization of "The Four Color Problem" from Hundred Theorems item 032. This
-- file contains no proof.

/-!
# The Four Color Problem

This is the high-level real-plane formulation used by the Rocq Four Color Theorem.
Maps are partial equivalence relations on points. Their classes are open connected
regions, and adjacent regions must receive different colors.
-/

namespace Theorems100.FourColorProblem

universe u

/-- The operations carried by the source formalization's axiomatized real line. -/
structure RealStructure where
  Val : Type u
  le : Val → Val → Prop
  sup : (Val → Prop) → Val
  add : Val → Val → Val
  zero : Val
  neg : Val → Val
  mul : Val → Val → Val
  one : Val
  inv : Val → Val

def RealEq (R : RealStructure) (x y : R.Val) : Prop :=
  R.le x y ∧ R.le y x

def UpperBounds (R : RealStructure) (s : R.Val → Prop) : R.Val → Prop :=
  fun z => ∀ y, s y → R.le y z

def DownwardClosure (R : RealStructure) (s : R.Val → Prop) : R.Val → Prop :=
  fun x => ∃ y, s y ∧ R.le x y

def NonemptySet {α : Type u} (s : α → Prop) : Prop :=
  ∃ x, s x

def HasUpperBound (R : RealStructure) (s : R.Val → Prop) : Prop :=
  NonemptySet (UpperBounds R s)

def HasSupremum (R : RealStructure) (s : R.Val → Prop) : Prop :=
  NonemptySet s ∧ HasUpperBound R s

/-- The complete ordered-field axioms used by the source theorem. -/
structure RealAxioms (R : RealStructure) : Prop where
  le_refl : ∀ x, R.le x x
  le_trans : ∀ x y z, R.le x y → R.le y z → R.le x z
  sup_upper_bound : ∀ s, HasSupremum R s → UpperBounds R s (R.sup s)
  sup_total : ∀ s x, HasSupremum R s → DownwardClosure R s x ∨ R.le (R.sup s) x
  add_mono : ∀ x y z, R.le y z → R.le (R.add x y) (R.add x z)
  add_comm : ∀ x y, RealEq R (R.add x y) (R.add y x)
  add_assoc : ∀ x y z, RealEq R (R.add x (R.add y z)) (R.add (R.add x y) z)
  zero_add : ∀ x, RealEq R (R.add R.zero x) x
  add_neg : ∀ x, RealEq R (R.add x (R.neg x)) R.zero
  mul_mono : ∀ x y z, R.le R.zero x → R.le y z → R.le (R.mul x y) (R.mul x z)
  mul_comm : ∀ x y, RealEq R (R.mul x y) (R.mul y x)
  mul_assoc : ∀ x y z, RealEq R (R.mul x (R.mul y z)) (R.mul (R.mul x y) z)
  mul_add : ∀ x y z, RealEq R (R.mul x (R.add y z)) (R.add (R.mul x y) (R.mul x z))
  one_mul : ∀ x, RealEq R (R.mul R.one x) x
  mul_inv : ∀ x, ¬RealEq R x R.zero → RealEq R (R.mul x (R.inv x)) R.one
  one_ne_zero : ¬RealEq R R.one R.zero

structure RealModel where
  toStructure : RealStructure
  axioms : RealAxioms toStructure

structure Point (R : RealStructure) where
  x : R.Val
  y : R.Val

abbrev Region (R : RealStructure) := Point R → Prop

/-- A map is a relation on points; its equivalence classes are its regions. -/
abbrev PlaneMap (R : RealStructure) := Point R → Point R → Prop

structure Interval (R : RealStructure) where
  left : R.Val
  right : R.Val

structure Rectangle (R : RealStructure) where
  horizontal : Interval R
  vertical : Interval R

def InInterval {R : RealStructure} (s : Interval R) (t : R.Val) : Prop :=
  ¬R.le t s.left ∧ ¬R.le s.right t

def InRectangle {R : RealStructure} (rect : Rectangle R) : Region R :=
  fun p => InInterval rect.horizontal p.x ∧ InInterval rect.vertical p.y

def RegionUnion {R : RealStructure} (r1 r2 : Region R) : Region R :=
  fun p => r1 p ∨ r2 p

def RegionInter {R : RealStructure} (r1 r2 : Region R) : Region R :=
  fun p => r1 p ∧ r2 p

def RegionNonempty {R : RealStructure} (r : Region R) : Prop :=
  ∃ p, r p

def Subregion {R : RealStructure} (r1 r2 : Region R) : Prop :=
  ∀ p, r1 p → r2 p

def Meet {R : RealStructure} (r1 r2 : Region R) : Prop :=
  RegionNonempty (RegionInter r1 r2)

/-- A plain map is a partial equivalence relation on points. -/
structure PlainMap {R : RealStructure} (m : PlaneMap R) : Prop where
  symm : ∀ p q, m p q → m q p
  trans : ∀ p q, m p q → Subregion (m q) (m p)

def Cover {R : RealStructure} (m : PlaneMap R) : Region R :=
  fun p => m p p

def Submap {R : RealStructure} (m1 m2 : PlaneMap R) : Prop :=
  ∀ p, Subregion (m1 p) (m2 p)

def AtMostRegions {R : RealStructure} (n : Nat) (m : PlaneMap R) : Prop :=
  ∃ representatives : Nat → Point R,
    ∀ p, Cover m p → ∃ i, i < n ∧ m (representatives i) p

/-- Openness in the rectangle-basis topology of the modeled real plane. -/
def OpenRegion {R : RealStructure} (r : Region R) : Prop :=
  ∀ p, r p → ∃ rect, InRectangle rect p ∧ Subregion (InRectangle rect) r

def Closure {R : RealStructure} (r : Region R) : Region R :=
  fun p => ∀ u, OpenRegion u → u p → Meet r u

/-- Connectedness expressed through separation by two open regions. -/
def Connected {R : RealStructure} (r : Region R) : Prop :=
  ∀ u v,
    OpenRegion u →
      OpenRegion v →
        Subregion r (RegionUnion u v) →
          Meet u r → Meet v r → Meet u v

structure SimpleMap {R : RealStructure} (m : PlaneMap R) : Prop where
  plain : PlainMap m
  open_region : ∀ p, OpenRegion (m p)
  connected_region : ∀ p, Connected (m p)

structure FiniteSimpleMap {R : RealStructure} (m : PlaneMap R) : Prop where
  simple : SimpleMap m
  finite : ∃ n, AtMostRegions n m

def Border {R : RealStructure} (m : PlaneMap R) (p q : Point R) : Region R :=
  RegionInter (Closure (m p)) (Closure (m q))

def CornerMap {R : RealStructure} (m : PlaneMap R) (p : Point R) : PlaneMap R :=
  fun q r => m q r ∧ Closure (m q) p

def NotCorner {R : RealStructure} (m : PlaneMap R) : Region R :=
  fun p => AtMostRegions 2 (CornerMap m p)

/-- Two distinct regions are adjacent when their border contains a non-corner point. -/
def Adjacent {R : RealStructure} (m : PlaneMap R) (p q : Point R) : Prop :=
  ¬m p q ∧ Meet (NotCorner m) (Border m p q)

/-- A coloring is a coarser partial equivalence relation separating adjacent regions. -/
structure Coloring {R : RealStructure} (m k : PlaneMap R) : Prop where
  plain : PlainMap k
  cover : Subregion (Cover k) (Cover m)
  consistent : Submap m k
  separates_adjacent : ∀ p q, Adjacent m p q → ¬k p q

def ColorableWith {R : RealStructure} (n : Nat) (m : PlaneMap R) : Prop :=
  ∃ k, Coloring m k ∧ AtMostRegions n k

/-- Every finite simple map over an arbitrary model of the real line is four-colorable. -/
theorem four_color_finite (Rmodel : RealModel)
    (m : PlaneMap Rmodel.toStructure) :
    FiniteSimpleMap m → ColorableWith 4 m := sorry

/-- Every simple map over an arbitrary model of the real line is four-colorable. -/
theorem four_color (Rmodel : RealModel)
    (m : PlaneMap Rmodel.toStructure) :
    SimpleMap m → ColorableWith 4 m := sorry

end Theorems100.FourColorProblem
