-- Statement-only formalization of "Puiseux's Theorem" from Hundred Theorems item 041.
-- It states that formal Puiseux series over an algebraically closed field of characteristic zero
-- are algebraically closed. This file contains no proof.

namespace Theorems100.Puiseux

/-- A commutative field, presented explicitly so that the statement needs no external imports. -/
structure Field where
  Carrier : Type
  zero : Carrier
  one : Carrier
  add : Carrier → Carrier → Carrier
  mul : Carrier → Carrier → Carrier
  neg : Carrier → Carrier
  inv : Carrier → Carrier
  add_assoc : ∀ a b c : Carrier, add (add a b) c = add a (add b c)
  add_comm : ∀ a b : Carrier, add a b = add b a
  zero_add : ∀ a : Carrier, add zero a = a
  add_neg : ∀ a : Carrier, add a (neg a) = zero
  mul_assoc : ∀ a b c : Carrier, mul (mul a b) c = mul a (mul b c)
  mul_comm : ∀ a b : Carrier, mul a b = mul b a
  one_mul : ∀ a : Carrier, mul one a = a
  left_distrib : ∀ a b c : Carrier, mul a (add b c) = add (mul a b) (mul a c)
  zero_ne_one : zero ≠ one
  inv_zero : inv zero = zero
  mul_inv : ∀ a : Carrier, a ≠ zero → mul (inv a) a = one

/-- The natural-number embedding determined by a field's zero, one, and addition. -/
def natCast (K : Field) : Nat → K.Carrier
  | 0 => K.zero
  | n + 1 => K.add (natCast K n) K.one

/-- Characteristic zero, expressed as injectivity of the natural-number embedding. -/
def HasCharacteristicZero (K : Field) : Prop :=
  ∀ m n : Nat, natCast K m = natCast K n → m = n

/-- A positive-degree polynomial, with coefficients ordered from constant to leading term. -/
structure PositiveDegreePolynomial (K : Field) where
  constant : K.Carrier
  intermediate : List K.Carrier
  leading : K.Carrier
  leading_ne_zero : leading ≠ K.zero

/-- Horner evaluation of the nonconstant tail of a positive-degree polynomial. -/
def evalTail (K : Field) (coefficients : List K.Carrier)
    (leading x : K.Carrier) : K.Carrier :=
  coefficients.foldr (fun coefficient value => K.add coefficient (K.mul x value)) leading

/-- Evaluation of a positive-degree polynomial. -/
def evalPositiveDegreePolynomial (K : Field)
    (p : PositiveDegreePolynomial K) (x : K.Carrier) : K.Carrier :=
  K.add p.constant (K.mul x (evalTail K p.intermediate p.leading x))

/-- Every positive-degree polynomial over the field has a root. -/
def IsAlgebraicallyClosed (K : Field) : Prop :=
  ∀ p : PositiveDegreePolynomial K,
    ∃ x : K.Carrier, evalPositiveDegreePolynomial K p x = K.zero

/-- A raw formal series whose exponents are rational numbers. -/
abbrev Series (K : Field) := Rat → K.Carrier

/-- The support is bounded below and all support denominators divide one positive integer. -/
def IsPuiseuxSeries (K : Field) (f : Series K) : Prop :=
  (∃ lower : Rat, ∀ q : Rat, q < lower → f q = K.zero) ∧
    ∃ denominator : Nat,
      0 < denominator ∧
        ∀ q : Rat, f q ≠ K.zero →
          ∃ multiplier : Nat, denominator = q.den * multiplier

/-- Extensional equality of formal series. -/
def SeriesEq (K : Field) (f g : Series K) : Prop :=
  ∀ q : Rat, f q = g q

/-- The zero formal series. -/
def zeroSeries (K : Field) : Series K :=
  fun _ => K.zero

/-- Membership in a list of rational-exponent pairs. -/
def PairMem (pair : Rat × Rat) : List (Rat × Rat) → Prop
  | [] => False
  | first :: rest => pair = first ∨ PairMem pair rest

/-- A list of rational-exponent pairs has no repetitions. -/
def PairwiseDistinct : List (Rat × Rat) → Prop
  | [] => True
  | first :: rest => ¬PairMem first rest ∧ PairwiseDistinct rest

/-- The field-valued sum of products indexed by exponent pairs. -/
def convolutionSum (K : Field) (f g : Series K) :
    List (Rat × Rat) → K.Carrier
  | [] => K.zero
  | pair :: rest =>
      K.add (K.mul (f pair.1) (g pair.2)) (convolutionSum K f g rest)

/-- A list enumerates exactly the nonzero pairs contributing to one Cauchy-product coefficient. -/
def EnumeratesConvolutionSupport (K : Field) (f g : Series K)
    (q : Rat) (pairs : List (Rat × Rat)) : Prop :=
  PairwiseDistinct pairs ∧
    ∀ r s : Rat,
      PairMem (r, s) pairs ↔
        r + s = q ∧ f r ≠ K.zero ∧ g s ≠ K.zero

/-- `product` is the formal Cauchy product of `f` and `g`. -/
def IsSeriesProduct (K : Field) (f g product : Series K) : Prop :=
  ∀ q : Rat,
    ∃ pairs : List (Rat × Rat),
      EnumeratesConvolutionSupport K f g q pairs ∧
        product q = convolutionSum K f g pairs

/-- `sum` is the coefficientwise sum of `f` and `g`. -/
def IsSeriesSum (K : Field) (f g sum : Series K) : Prop :=
  ∀ q : Rat, sum q = K.add (f q) (g q)

/-- Every coefficient of a list is a formal Puiseux series. -/
def AllPuiseux (K : Field) : List (Series K) → Prop
  | [] => True
  | first :: rest => IsPuiseuxSeries K first ∧ AllPuiseux K rest

/-- A positive-degree polynomial whose coefficients are formal Puiseux series. -/
structure PuiseuxPolynomial (K : Field) where
  constant : Series K
  intermediate : List (Series K)
  leading : Series K
  constant_is_puiseux : IsPuiseuxSeries K constant
  intermediate_are_puiseux : AllPuiseux K intermediate
  leading_is_puiseux : IsPuiseuxSeries K leading
  leading_ne_zero : ∃ q : Rat, leading q ≠ K.zero

/-- The coefficient list of a positive-degree Puiseux polynomial, in ascending degree order. -/
def PuiseuxPolynomial.coefficients {K : Field}
    (p : PuiseuxPolynomial K) : List (Series K) :=
  p.constant :: p.intermediate.append (p.leading :: [])

/-- Relational Horner evaluation using formal-series addition and Cauchy multiplication. -/
inductive PolynomialEvaluatesAt (K : Field) (x : Series K) :
    List (Series K) → Series K → Prop where
  | nil : PolynomialEvaluatesAt K x [] (zeroSeries K)
  | cons {coefficient : Series K} {coefficients : List (Series K)}
      {tail product value : Series K} :
      PolynomialEvaluatesAt K x coefficients tail →
      IsSeriesProduct K x tail product →
      IsSeriesSum K coefficient product value →
      PolynomialEvaluatesAt K x (coefficient :: coefficients) value

/-- Puiseux's theorem: over an algebraically closed field of characteristic zero, every
positive-degree polynomial over the formal Puiseux series has a formal Puiseux-series root. -/
theorem puiseux_theorem
    (K : Field)
    (_characteristic_zero : HasCharacteristicZero K)
    (_algebraically_closed : IsAlgebraicallyClosed K)
    (p : PuiseuxPolynomial K) :
    ∃ root value : Series K,
      IsPuiseuxSeries K root ∧
        PolynomialEvaluatesAt K root p.coefficients value ∧
          SeriesEq K value (zeroSeries K) := by
  sorry

end Theorems100.Puiseux
