-- Statement-only formalization of miniF2F valid problem aimeI_2000_p7 using exact
-- Dedekind-cut real numbers: reciprocal equations for positive reals determine the
-- numerator-plus-denominator sum of a reduced positive rational. This file contains no proof.

module aimeI-2000-p7 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Sigma using (Σ)

infix 4 ¬_
infixr 4 _∧_
infixr 3 _∨_
infixr 2 _↔_
infixl 6 _+z_
infixl 7 _*z_

data ⊥ : Set where

record ⊤ : Set where
  constructor tt

¬_ : Set → Set
¬ A = A → ⊥

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

record _↔_ (A B : Set) : Set where
  constructor iff
  field
    forward  : A → B
    backward : B → A

Exists : (A : Set) → (A → Set) → Set
Exists A P = Σ A P

data NatLess : Nat → Nat → Set where
  zero-less-successor :
    {n : Nat} →
    NatLess zero (suc n)
  successor-less-successor :
    {m n : Nat} →
    NatLess m n →
    NatLess (suc m) (suc n)

natPred : Nat → Nat
natPred zero = zero
natPred (suc n) = n

difference : Nat → Nat → Int
difference zero zero = pos zero
difference (suc m) zero = pos (suc m)
difference zero (suc n) = negsuc n
difference (suc m) (suc n) = difference m n

negative : Nat → Int
negative zero = pos zero
negative (suc n) = negsuc n

_+z_ : Int → Int → Int
pos m +z pos n = pos (m + n)
pos m +z negsuc n = difference m (suc n)
negsuc m +z pos n = difference n (suc m)
negsuc m +z negsuc n = negsuc (suc (m + n))

_*z_ : Int → Int → Int
pos m *z pos n = pos (m * n)
pos m *z negsuc n = negative (m * suc n)
negsuc m *z pos n = negative (suc m * n)
negsuc m *z negsuc n = pos (suc m * suc n)

IntLess : Int → Int → Set
IntLess (pos m) (pos n) = NatLess m n
IntLess (pos m) (negsuc n) = ⊥
IntLess (negsuc m) (pos n) = ⊤
IntLess (negsuc m) (negsuc n) = NatLess n m

record Rational : Set where
  constructor fraction
  field
    numerator             : Int
    denominator-minus-one : Nat

rationalDenominator : Rational → Nat
rationalDenominator q =
  suc (Rational.denominator-minus-one q)

scaleInt : Int → Nat → Int
scaleInt z n = z *z pos n

rationalEquivalent : Rational → Rational → Set
rationalEquivalent p q =
  scaleInt
    (Rational.numerator p)
    (rationalDenominator q)
  ≡
  scaleInt
    (Rational.numerator q)
    (rationalDenominator p)

rationalLess : Rational → Rational → Set
rationalLess p q =
  IntLess
    (scaleInt
      (Rational.numerator p)
      (rationalDenominator q))
    (scaleInt
      (Rational.numerator q)
      (rationalDenominator p))

rationalAdd : Rational → Rational → Rational
rationalAdd p q =
  fraction
    ((scaleInt
        (Rational.numerator p)
        (rationalDenominator q))
      +z
      (scaleInt
        (Rational.numerator q)
        (rationalDenominator p)))
    (natPred
      (rationalDenominator p *
       rationalDenominator q))

rationalMultiply : Rational → Rational → Rational
rationalMultiply p q =
  fraction
    (Rational.numerator p *z Rational.numerator q)
    (natPred
      (rationalDenominator p *
       rationalDenominator q))

rationalFromNat : Nat → Rational
rationalFromNat n = fraction (pos n) zero

rationalZero rationalOne rationalFive rationalTwentyNine : Rational
rationalZero = rationalFromNat 0
rationalOne = rationalFromNat 1
rationalFive = rationalFromNat 5
rationalTwentyNine = rationalFromNat 29

PositiveRational : Rational → Set
PositiveRational q = rationalLess rationalZero q

record Coprime (a : Int) (b : Nat) : Set where
  constructor bezout
  field
    left-coefficient right-coefficient : Int
    combination :
      (left-coefficient *z a) +z
      (right-coefficient *z pos b) ≡ pos 1

record Rat : Set where
  constructor reducedFraction
  field
    numerator             : Int
    denominator-minus-one : Nat
    reduced :
      Coprime numerator (suc denominator-minus-one)

ratDenominator : Rat → Nat
ratDenominator q = suc (Rat.denominator-minus-one q)

ratAsRational : Rat → Rational
ratAsRational q =
  fraction
    (Rat.numerator q)
    (Rat.denominator-minus-one q)

PositiveRat : Rat → Set
PositiveRat q = PositiveRational (ratAsRational q)

numeratorPlusDenominator : Rat → Int
numeratorPlusDenominator q =
  Rat.numerator q +z pos (ratDenominator q)

record Real : Set₁ where
  constructor dedekindCut
  field
    lower : Rational → Set
    respects-equivalence :
      (p q : Rational) →
      rationalEquivalent p q →
      lower p ↔ lower q
    inhabited :
      Exists Rational lower
    proper :
      Exists Rational (λ q → ¬ lower q)
    downward-closed :
      (p q : Rational) →
      rationalLess q p →
      lower p →
      lower q
    rounded :
      (q : Rational) →
      lower q ↔
      Exists Rational
        (λ r →
          rationalLess q r ∧
          lower r)
    located :
      (p q : Rational) →
      rationalLess p q →
      lower p ∨ ¬ lower q

PositiveReal : Real → Set
PositiveReal x = Real.lower x rationalZero

RealSumLower : Real → Real → Rational → Set
RealSumLower x y q =
  Exists Rational
    (λ a →
      Exists Rational
        (λ b →
          Real.lower x a ∧
          Real.lower y b ∧
          rationalLess q (rationalAdd a b)))

RealSumEqualsRational :
  Real →
  Real →
  Rational →
  Set
RealSumEqualsRational x y result =
  (q : Rational) →
  rationalLess q result ↔ RealSumLower x y q

PositiveProductLower : Real → Real → Rational → Set
PositiveProductLower x y q =
  rationalLess q rationalZero ∨
  Exists Rational
    (λ a →
      Exists Rational
        (λ b →
          PositiveRational a ∧
          Real.lower x a ∧
          PositiveRational b ∧
          Real.lower y b ∧
          rationalLess q (rationalMultiply a b)))

PositiveRealMultiply :
  Real →
  Real →
  Real →
  Set
PositiveRealMultiply x y product =
  PositiveReal x ∧
  PositiveReal y ∧
  ((q : Rational) →
    Real.lower product q ↔
    PositiveProductLower x y q)

PositiveProductEqualsRational :
  Real →
  Real →
  Rational →
  Set
PositiveProductEqualsRational x y result =
  PositiveReal x ∧
  PositiveReal y ∧
  ((q : Rational) →
    rationalLess q result ↔
    PositiveProductLower x y q)

PositiveInverse : Real → Real → Set
PositiveInverse x reciprocal =
  PositiveReal x ∧
  PositiveReal reciprocal ∧
  PositiveProductEqualsRational
    x reciprocal rationalOne

PositiveTripleProductEqualsRational :
  Real →
  Real →
  Real →
  Rational →
  Set₁
PositiveTripleProductEqualsRational x y z result =
  Σ Real
    (λ xy →
      PositiveRealMultiply x y xy ∧
      PositiveProductEqualsRational xy z result)

ReciprocalSumEqualsRational :
  Real →
  Real →
  Rational →
  Set₁
ReciprocalSumEqualsRational summand divisor result =
  Σ Real
    (λ reciprocal →
      PositiveInverse divisor reciprocal ∧
      RealSumEqualsRational summand reciprocal result)

aimeI-2000-p7 : Set₁
aimeI-2000-p7 =
  (x y z : Real) →
  (m : Rat) →
  (PositiveReal x ∧
   PositiveReal y ∧
   PositiveReal z) →
  PositiveTripleProductEqualsRational
    x y z rationalOne →
  ReciprocalSumEqualsRational
    x z rationalFive →
  ReciprocalSumEqualsRational
    y x rationalTwentyNine →
  ReciprocalSumEqualsRational
    z y (ratAsRational m) →
  PositiveRat m →
  numeratorPlusDenominator m ≡ pos 5
