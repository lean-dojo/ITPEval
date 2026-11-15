-- Statement-only formalization of "The Independence of the Parallel Postulate" from Hundred
-- Theorems item 012. This file contains no proof.

/-!
# The Independence of the Parallel Postulate

This statement-only file presents the two-dimensional Klein-disc model over an abstract
Dedekind-complete ordered field. Such a field is a presentation of the real numbers. Points are
pairs of scalars in the open unit disc, betweenness is ordinary affine betweenness, and segment
congruence is equality for the Klein semimetric.
-/

namespace Theorems100
namespace ParallelPostulateIndependence

/-- The scalar structure used below: a Dedekind-complete linearly ordered field with square root. -/
structure RealScalar where
  Carrier : Type
  zero : Carrier
  one : Carrier
  add : Carrier → Carrier → Carrier
  mul : Carrier → Carrier → Carrier
  neg : Carrier → Carrier
  inv : Carrier → Carrier
  sqrt : Carrier → Carrier
  le : Carrier → Carrier → Prop
  lt : Carrier → Carrier → Prop
  decLt : (a b : Carrier) → Decidable (lt a b)
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  add_comm : ∀ a b, add a b = add b a
  zero_add : ∀ a, add zero a = a
  add_neg : ∀ a, add (neg a) a = zero
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  mul_comm : ∀ a b, mul a b = mul b a
  one_mul : ∀ a, mul one a = a
  left_distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)
  zero_ne_one : zero ≠ one
  inv_zero : inv zero = zero
  mul_inv : ∀ a, a ≠ zero → mul (inv a) a = one
  le_refl : ∀ a, le a a
  le_trans : ∀ a b c, le a b → le b c → le a c
  le_antisymm : ∀ a b, le a b → le b a → a = b
  le_total : ∀ a b, le a b ∨ le b a
  lt_iff_le_not_le : ∀ a b, lt a b ↔ le a b ∧ ¬le b a
  add_le_add_right : ∀ a b c, le a b → le (add a c) (add b c)
  mul_pos : ∀ a b, lt zero a → lt zero b → lt zero (mul a b)
  sqrt_nonneg : ∀ a, le zero (sqrt a)
  sqrt_sq : ∀ a, le zero a → mul (sqrt a) (sqrt a) = a
  complete :
    ∀ S : Carrier → Prop,
      (∃ x, S x) →
      (∃ u, ∀ x, S x → le x u) →
      ∃ s, (∀ x, S x → le x s) ∧ ∀ u, (∀ x, S x → le x u) → le s u

abbrev Real (R : RealScalar) := R.Carrier
abbrev EuclideanPoint (R : RealScalar) (n : Nat) := Fin n → Real R
abbrev Complex (R : RealScalar) := EuclideanPoint R 2
abbrev Set (α : Type) := α → Prop

def sub (R : RealScalar) (a b : Real R) : Real R :=
  R.add a (R.neg b)

def div (R : RealScalar) (a b : Real R) : Real R :=
  R.mul a (R.inv b)

def sq (R : RealScalar) (a : Real R) : Real R :=
  R.mul a a

def two (R : RealScalar) : Real R :=
  R.add R.one R.one

def four (R : RealScalar) : Real R :=
  R.mul (two R) (two R)

def half (R : RealScalar) : Real R :=
  div R R.one (two R)

def pointZero (R : RealScalar) {n : Nat} : EuclideanPoint R n :=
  fun _ => R.zero

def pointOne (R : RealScalar) : Complex R :=
  fun i => if i = 0 then R.one else R.zero

def pointAdd (R : RealScalar) {n : Nat}
    (a b : EuclideanPoint R n) : EuclideanPoint R n :=
  fun i => R.add (a i) (b i)

def pointSub (R : RealScalar) {n : Nat}
    (a b : EuclideanPoint R n) : EuclideanPoint R n :=
  fun i => sub R (a i) (b i)

def smul (R : RealScalar) {n : Nat}
    (a : Real R) (x : EuclideanPoint R n) : EuclideanPoint R n :=
  fun i => R.mul a (x i)

def dot (R : RealScalar) {n : Nat}
    (x y : EuclideanPoint R n) : Real R :=
  (Vector.ofFn (fun i => R.mul (x i) (y i))).toArray.foldl R.add R.zero

def normSq (R : RealScalar) {n : Nat} (x : EuclideanPoint R n) : Real R :=
  dot R x x

def norm (R : RealScalar) {n : Nat} (x : EuclideanPoint R n) : Real R :=
  R.sqrt (normSq R x)

def dist (R : RealScalar) {n : Nat}
    (x y : EuclideanPoint R n) : Real R :=
  norm R (pointSub R x y)

def abs (R : RealScalar) (x : Real R) : Real R :=
  match R.decLt x R.zero with
  | isTrue _ => R.neg x
  | isFalse _ => x

/-- Affine betweenness, with the middle point given first. -/
def between (R : RealScalar) {n : Nat}
    (x a b : EuclideanPoint R n) : Prop :=
  ∃ t : Real R,
    R.le R.zero t ∧
      R.le t R.one ∧
      x = pointAdd R (smul R (sub R R.one t) a) (smul R t b)

def collinear (R : RealScalar) {n : Nat}
    (a b c : EuclideanPoint R n) : Prop :=
  ∃ p v : EuclideanPoint R n, ∃ sa sb sc : Real R,
    a = pointAdd R p (smul R sa v) ∧
      b = pointAdd R p (smul R sb v) ∧
      c = pointAdd R p (smul R sc v)

def continuousAt (R : RealScalar) {n : Nat}
    (f : EuclideanPoint R n → Real R) (x : EuclideanPoint R n) : Prop :=
  ∀ epsilon,
    R.lt R.zero epsilon →
      ∃ delta,
        R.lt R.zero delta ∧
          ∀ y,
            R.lt (dist R y x) delta →
              R.lt (abs R (sub R (f y) (f x))) epsilon

/-- The semimetric used by the Klein model, with Euclidean distance outside the unit ball. -/
def ddist (R : RealScalar) {n : Nat}
    (x y : EuclideanPoint R n) : Real R :=
  match R.decLt (norm R x) R.one with
  | isTrue _ =>
      match R.decLt (norm R y) R.one with
      | isTrue _ =>
          sub R
            (div R
              (sq R (sub R R.one (dot R x y)))
              (R.mul
                (sub R R.one (sq R (norm R x)))
                (sub R R.one (sq R (norm R y)))))
            R.one
      | isFalse _ => dist R x y
  | isFalse _ => dist R x y

theorem ddist_increases_online (R : RealScalar) (n : Nat)
    (a b x : EuclideanPoint R n)
    (ha : R.lt (norm R a) R.one)
    (hb : R.lt (norm R b) R.one)
    (hx : R.lt (norm R x) R.one)
    (hbetween : between R x a b)
    (hxb : x ≠ b) :
    R.lt (ddist R a x) (ddist R a b) := sorry

theorem ddist_refl (R : RealScalar) (n : Nat) (x : EuclideanPoint R n) :
    ddist R x x = R.zero := sorry

theorem ddist_symm (R : RealScalar) (n : Nat) (x y : EuclideanPoint R n) :
    ddist R x y = ddist R y x := sorry

theorem ddist_pos (R : RealScalar) (n : Nat)
    (x y : EuclideanPoint R n) (hxy : x ≠ y) :
    R.lt R.zero (ddist R x y) := sorry

theorem ddist_nonneg (R : RealScalar) (n : Nat) (x y : EuclideanPoint R n) :
    R.le R.zero (ddist R x y) := sorry

theorem ddist_eq_zero (R : RealScalar) (n : Nat) (x y : EuclideanPoint R n) :
    ddist R x y = R.zero ↔ x = y := sorry

theorem between_iff_collinear_ddist (R : RealScalar) (n : Nat)
    (a b x : EuclideanPoint R n)
    (ha : R.lt (norm R a) R.one)
    (hb : R.lt (norm R b) R.one)
    (hx : R.lt (norm R x) R.one) :
    between R x a b ↔
      collinear R a x b ∧
        R.le (ddist R x a) (ddist R a b) ∧
        R.le (ddist R x b) (ddist R a b) := sorry

theorem continuousAt_ddist (R : RealScalar) (n : Nat)
    (a x : EuclideanPoint R n)
    (ha : R.lt (norm R a) R.one)
    (hx : R.lt (norm R x) R.one) :
    continuousAt R (fun y => ddist R a y) x := sorry

theorem hyperbolic_midpoint (R : RealScalar) (n : Nat)
    (a b : EuclideanPoint R n)
    (ha : R.lt (norm R a) R.one)
    (hb : R.lt (norm R b) R.one) :
    ∃ x, between R x a b ∧ ddist R x a = ddist R x b := sorry

theorem ddist_eq_origin (R : RealScalar) (n : Nat)
    (x y : EuclideanPoint R n)
    (hx : R.lt (norm R x) R.one)
    (hy : R.lt (norm R y) R.one) :
    ddist R (pointZero R) x = ddist R (pointZero R) y ↔
      norm R x = norm R y := sorry

theorem ddist_congruent_triples_zero (R : RealScalar) (n : Nat)
    (a b a' b' : EuclideanPoint R n)
    (ha : R.lt (norm R a) R.one)
    (hb : R.lt (norm R b) R.one)
    (ha' : R.lt (norm R a') R.one)
    (hb' : R.lt (norm R b') R.one) :
    (ddist R (pointZero R) a = ddist R (pointZero R) a' ∧
        ddist R a b = ddist R a' b' ∧
        ddist R b (pointZero R) = ddist R b' (pointZero R)) ↔
      (dist R (pointZero R) a = dist R (pointZero R) a' ∧
        dist R a b = dist R a' b' ∧
        dist R b (pointZero R) = dist R b' (pointZero R)) := sorry

def complexMk (R : RealScalar) (re im : Real R) : Complex R :=
  fun i => if i = 0 then re else im

def complexRe (R : RealScalar) (z : Complex R) : Real R :=
  z 0

def complexIm (R : RealScalar) (z : Complex R) : Real R :=
  z 1

def complexConj (R : RealScalar) (z : Complex R) : Complex R :=
  complexMk R (complexRe R z) (R.neg (complexIm R z))

def complexMul (R : RealScalar) (z w : Complex R) : Complex R :=
  complexMk R
    (sub R
      (R.mul (complexRe R z) (complexRe R w))
      (R.mul (complexIm R z) (complexIm R w)))
    (R.add
      (R.mul (complexRe R z) (complexIm R w))
      (R.mul (complexIm R z) (complexRe R w)))

def complexDiv (R : RealScalar) (z w : Complex R) : Complex R :=
  let denominator := normSq R w
  complexMk R
    (div R
      (R.add
        (R.mul (complexRe R z) (complexRe R w))
        (R.mul (complexIm R z) (complexIm R w)))
      denominator)
    (div R
      (sub R
        (R.mul (complexIm R z) (complexRe R w))
        (R.mul (complexRe R z) (complexIm R w)))
      denominator)

/-- Orthogonal projection from the Poincare disc to the Klein disc. -/
def kleinify (R : RealScalar) (z : Complex R) : Complex R :=
  smul R (div R (two R) (R.add R.one (sq R (norm R z)))) z

/-- The inverse radial map from the Klein disc to the Poincare disc. -/
def poincarify (R : RealScalar) (x : Complex R) : Complex R :=
  smul R
    (div R
      (sub R R.one (R.sqrt (sub R R.one (sq R (norm R x)))))
      (sq R (norm R x)))
    x

/-- The disc automorphism taking `w` to the origin. -/
def mobius (R : RealScalar) (w x : Complex R) : Complex R :=
  complexDiv R
    (pointSub R x w)
    (pointSub R (pointOne R) (complexMul R (complexConj R w) x))

theorem kleinify_zero_and_poincarify_zero (R : RealScalar) :
    kleinify R (pointZero R) = pointZero R ∧
      poincarify R (pointZero R) = pointZero R := sorry

theorem norm_kleinify (R : RealScalar) (z : Complex R) :
    norm R (kleinify R z) =
      div R (R.mul (two R) (norm R z)) (R.add R.one (sq R (norm R z))) := sorry

theorem norm_kleinify_lt_one_iff (R : RealScalar) (z : Complex R) :
    R.lt (norm R (kleinify R z)) R.one ↔ norm R z ≠ R.one := sorry

theorem norm_poincarify_lt_one (R : RealScalar) (x : Complex R)
    (hx : R.lt (norm R x) R.one) :
    R.lt (norm R (poincarify R x)) R.one := sorry

theorem kleinify_poincarify (R : RealScalar) (x : Complex R)
    (hx : R.lt (norm R x) R.one) :
    kleinify R (poincarify R x) = x := sorry

theorem poincarify_kleinify (R : RealScalar) (x : Complex R)
    (hx : R.lt (norm R x) R.one) :
    poincarify R (kleinify R x) = x := sorry

theorem ddist_kleinify (R : RealScalar) (w z : Complex R)
    (hw : norm R w ≠ R.one) (hz : norm R z ≠ R.one) :
    ddist R (kleinify R w) (kleinify R z) =
      sub R
        (R.mul (four R)
          (sq R
            (R.add (half R)
              (div R
                (sq R (norm R (pointSub R w z)))
                (R.mul
                  (sub R R.one (sq R (norm R w)))
                  (sub R R.one (sq R (norm R z))))))))
        R.one := sorry

theorem ddist_kleinify_eq (R : RealScalar) (w z w' z' : Complex R)
    (hw : norm R w ≠ R.one)
    (hz : norm R z ≠ R.one)
    (hw' : norm R w' ≠ R.one)
    (hz' : norm R z' ≠ R.one)
    (hcross :
      R.mul
          (R.mul
            (sq R (norm R (pointSub R w z)))
            (sub R R.one (sq R (norm R w'))))
          (sub R R.one (sq R (norm R z'))) =
        R.mul
          (R.mul
            (sq R (norm R (pointSub R w' z')))
            (sub R R.one (sq R (norm R w))))
          (sub R R.one (sq R (norm R z)))) :
    ddist R (kleinify R w) (kleinify R z) =
      ddist R (kleinify R w') (kleinify R z') := sorry

theorem norm_kleinify_mobius_lt_one (R : RealScalar) (w x : Complex R)
    (hw : R.lt (norm R w) R.one)
    (hx : R.lt (norm R x) R.one) :
    R.lt (norm R (kleinify R (mobius R w x))) R.one := sorry

theorem ddist_kleinify_mobius (R : RealScalar) (w x y : Complex R)
    (hw : R.lt (norm R w) R.one)
    (hx : R.lt (norm R x) R.one)
    (hy : R.lt (norm R y) R.one) :
    ddist R (kleinify R (mobius R w x)) (kleinify R (mobius R w y)) =
      ddist R (kleinify R x) (kleinify R y) := sorry

theorem collinear_kleinify_mobius (R : RealScalar) (w x y z : Complex R)
    (hw : R.lt (norm R w) R.one)
    (hx : R.lt (norm R x) R.one)
    (hy : R.lt (norm R y) R.one)
    (hz : R.lt (norm R z) R.one) :
    collinear R
        (kleinify R (mobius R w x))
        (kleinify R (mobius R w y))
        (kleinify R (mobius R w z)) ↔
      collinear R (kleinify R x) (kleinify R y) (kleinify R z) := sorry

theorem between_kleinify_mobius (R : RealScalar) (w x y z : Complex R)
    (hw : R.lt (norm R w) R.one)
    (hx : R.lt (norm R x) R.one)
    (hy : R.lt (norm R y) R.one)
    (hz : R.lt (norm R z) R.one) :
    between R
        (kleinify R (mobius R w x))
        (kleinify R (mobius R w y))
        (kleinify R (mobius R w z)) ↔
      between R (kleinify R x) (kleinify R y) (kleinify R z) := sorry

def HyperbolicIsometry (R : RealScalar) (f : Complex R → Complex R) : Prop :=
  (∀ x, R.lt (norm R x) R.one → R.lt (norm R (f x)) R.one) ∧
    (∀ x y,
      R.lt (norm R x) R.one →
      R.lt (norm R y) R.one →
      ddist R (f x) (f y) = ddist R x y) ∧
    (∀ x y z,
      R.lt (norm R x) R.one →
      R.lt (norm R y) R.one →
      R.lt (norm R z) R.one →
      (between R (f x) (f y) (f z) ↔ between R x y z))

theorem hyperbolic_translation (R : RealScalar) (w : Complex R)
    (hw : R.lt (norm R w) R.one) :
    ∃ f g : Complex R → Complex R,
      HyperbolicIsometry R f ∧
        HyperbolicIsometry R g ∧
        f w = pointZero R ∧
        g (pointZero R) = w ∧
        (∀ x, R.lt (norm R x) R.one → f (g x) = x) ∧
        (∀ x, R.lt (norm R x) R.one → g (f x) = x) := sorry

/-- The Klein model: the open unit disc in the real plane. -/
def Plane (R : RealScalar) :=
  {z : Complex R // R.lt (norm R z) R.one}

/-- Hyperbolic betweenness inherited from affine betweenness in the Klein disc. -/
def pbetween (R : RealScalar) (y x z : Plane R) : Prop :=
  between R y.val x.val z.val

/-- Hyperbolic segment length in the Klein model. -/
def pdist (R : RealScalar) (x y : Plane R) : Real R :=
  ddist R x.val y.val

theorem plane_norm_lt (R : RealScalar) (x : Plane R) :
    R.lt (norm R x.val) R.one := sorry

theorem plane_coe_eq (R : RealScalar) (x y : Plane R) :
    (x.val = y.val ↔ x = y) := sorry

theorem forall_plane_coe (R : RealScalar) (P : Complex R → Prop) :
    (∀ x : Plane R, P x.val) ↔
      ∀ x : Complex R, R.lt (norm R x) R.one → P x := sorry

theorem exists_plane_coe (R : RealScalar) (P : Complex R → Prop) :
    (∃ x : Plane R, P x.val) ↔
      ∃ x : Complex R, R.lt (norm R x) R.one ∧ P x := sorry

/-- Tarski axiom 1: symmetry of segment congruence. -/
theorem tarski_axiom_1_noneuclidean (R : RealScalar) (a b : Plane R) :
    pdist R a b = pdist R b a := sorry

/-- Tarski axiom 2: transitivity of segment congruence. -/
theorem tarski_axiom_2_noneuclidean (R : RealScalar) (a b p q r s : Plane R)
    (hpq : pdist R a b = pdist R p q)
    (hrs : pdist R a b = pdist R r s) :
    pdist R p q = pdist R r s := sorry

/-- Tarski axiom 3: identity for segment congruence. -/
theorem tarski_axiom_3_noneuclidean (R : RealScalar) (a b c : Plane R)
    (h : pdist R a b = pdist R c c) :
    a = b := sorry

/-- Tarski axiom 4: segment construction. -/
theorem tarski_axiom_4_noneuclidean (R : RealScalar) (a q b c : Plane R) :
    ∃ x, pbetween R a q x ∧ pdist R a x = pdist R b c := sorry

/-- Tarski axiom 5: the five-segments axiom. -/
theorem tarski_axiom_5_noneuclidean (R : RealScalar)
    (a b c x a' b' c' x' : Plane R)
    (hab : a ≠ b)
    (hab' : pdist R a b = pdist R a' b')
    (hac' : pdist R a c = pdist R a' c')
    (hbc' : pdist R b c = pdist R b' c')
    (hbetween : pbetween R b a x)
    (hbetween' : pbetween R b' a' x')
    (hbx' : pdist R b x = pdist R b' x') :
    pdist R c x = pdist R c' x' := sorry

/-- Tarski axiom 6: identity for betweenness. -/
theorem tarski_axiom_6_noneuclidean (R : RealScalar) (a b : Plane R)
    (h : pbetween R b a a) :
    a = b := sorry

/-- Tarski axiom 7: Pasch's axiom. -/
theorem tarski_axiom_7_noneuclidean (R : RealScalar) (a b c p q : Plane R)
    (hp : pbetween R p a c)
    (hq : pbetween R q b c) :
    ∃ x, pbetween R x p b ∧ pbetween R x q a := sorry

/-- Tarski axiom 8: the lower two-dimensional axiom. -/
theorem tarski_axiom_8_noneuclidean (R : RealScalar) :
    ∃ a b c : Plane R,
      ¬pbetween R b a c ∧
        ¬pbetween R c b a ∧
        ¬pbetween R a c b := sorry

/-- Tarski axiom 9: the upper two-dimensional axiom. -/
theorem tarski_axiom_9_noneuclidean (R : RealScalar) (p q a b c : Plane R)
    (hpq : p ≠ q)
    (ha : pdist R a p = pdist R a q)
    (hb : pdist R b p = pdist R b q)
    (hc : pdist R c p = pdist R c q) :
    pbetween R b a c ∨ pbetween R c b a ∨ pbetween R a c b := sorry

/-- The Klein model satisfies the negation of Tarski's Euclidean axiom 10. -/
theorem not_tarski_axiom_10_noneuclidean (R : RealScalar) :
    ¬(∀ a b c d t : Plane R,
      pbetween R d a t ∧ pbetween R d b c ∧ a ≠ d →
        ∃ x y,
          pbetween R b a x ∧
            pbetween R c a y ∧
            pbetween R t x y) := sorry

/-- Tarski axiom 11: continuity. -/
theorem tarski_axiom_11_noneuclidean (R : RealScalar) (X Y : Set (Plane R)) :
    (∃ a, ∀ x y, X x ∧ Y y → pbetween R x a y) →
      ∃ b, ∀ x y, X x ∧ Y y → pbetween R b x y := sorry

/-- The complete statement supplied by the Klein model: axioms 1-9 and 11 hold, while 10 fails. -/
def KleinModelIndependence (R : RealScalar) : Prop :=
  (∀ a b : Plane R, pdist R a b = pdist R b a) ∧
  (∀ a b p q r s : Plane R,
    pdist R a b = pdist R p q →
    pdist R a b = pdist R r s →
    pdist R p q = pdist R r s) ∧
  (∀ a b c : Plane R, pdist R a b = pdist R c c → a = b) ∧
  (∀ a q b c : Plane R,
    ∃ x, pbetween R a q x ∧ pdist R a x = pdist R b c) ∧
  (∀ a b c x a' b' c' x' : Plane R,
    a ≠ b →
    pdist R a b = pdist R a' b' →
    pdist R a c = pdist R a' c' →
    pdist R b c = pdist R b' c' →
    pbetween R b a x →
    pbetween R b' a' x' →
    pdist R b x = pdist R b' x' →
    pdist R c x = pdist R c' x') ∧
  (∀ a b : Plane R, pbetween R b a a → a = b) ∧
  (∀ a b c p q : Plane R,
    pbetween R p a c →
    pbetween R q b c →
    ∃ x, pbetween R x p b ∧ pbetween R x q a) ∧
  (∃ a b c : Plane R,
    ¬pbetween R b a c ∧
      ¬pbetween R c b a ∧
      ¬pbetween R a c b) ∧
  (∀ p q a b c : Plane R,
    p ≠ q →
    pdist R a p = pdist R a q →
    pdist R b p = pdist R b q →
    pdist R c p = pdist R c q →
    pbetween R b a c ∨ pbetween R c b a ∨ pbetween R a c b) ∧
  ¬(∀ a b c d t : Plane R,
    pbetween R d a t ∧ pbetween R d b c ∧ a ≠ d →
      ∃ x y,
        pbetween R b a x ∧
          pbetween R c a y ∧
          pbetween R t x y) ∧
  (∀ X Y : Set (Plane R),
    (∃ a, ∀ x y, X x ∧ Y y → pbetween R x a y) →
      ∃ b, ∀ x y, X x ∧ Y y → pbetween R b x y)

/-- Existence of the two-dimensional Klein model witnessing failure of the parallel postulate. -/
theorem independence_of_parallel_postulate :
    ∃ R : RealScalar, KleinModelIndependence R := sorry

end ParallelPostulateIndependence
end Theorems100
