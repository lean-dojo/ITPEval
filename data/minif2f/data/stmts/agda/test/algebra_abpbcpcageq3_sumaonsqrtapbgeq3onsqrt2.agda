-- Statement-only formalization of miniF2F test problem
-- algebra_abpbcpcageq3_sumaonsqrtapbgeq3onsqrt2 using exact Dedekind-cut
-- real numbers: a cyclic square-root inequality for three positive reals
-- under a pairwise-product bound. This file contains no proof.

module algebra_abpbcpcageq3_sumaonsqrtapbgeq3onsqrt2 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Sigma using (Σ)
open import Agda.Primitive using (Level; _⊔_)

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

record _∧_ {a b : Level} (A : Set a) (B : Set b) : Set (a ⊔ b) where
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

rationalZero rationalTwo rationalThree : Rational
rationalZero = rationalFromNat 0
rationalTwo = rationalFromNat 2
rationalThree = rationalFromNat 3

PositiveRational : Rational → Set
PositiveRational q = rationalLess rationalZero q

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

Cut : Set₁
Cut = Rational → Set

realCut : Real → Cut
realCut = Real.lower

rationalCut : Rational → Cut
rationalCut q p = rationalLess p q

CutEquivalent : Cut → Cut → Set
CutEquivalent lower upper =
  (q : Rational) →
  lower q ↔ upper q

RealLessOrEqualCut : Real → Cut → Set
RealLessOrEqualCut x upper =
  (q : Rational) →
  Real.lower x q →
  upper q

RationalLessOrEqualCut : Rational → Cut → Set
RationalLessOrEqualCut q lower =
  (p : Rational) →
  rationalLess p q →
  lower p

sumCut : Cut → Cut → Cut
sumCut lower upper q =
  Exists Rational
    (λ a →
      Exists Rational
        (λ b →
          lower a ∧
          upper b ∧
          rationalLess q (rationalAdd a b)))

positiveProductCut : Cut → Cut → Cut
positiveProductCut lower upper q =
  rationalLess q rationalZero ∨
  Exists Rational
    (λ a →
      Exists Rational
        (λ b →
          PositiveRational a ∧
          lower a ∧
          PositiveRational b ∧
          upper b ∧
          rationalLess q (rationalMultiply a b)))

PositiveSquareRoot : Cut → Real → Set
PositiveSquareRoot radicand root =
  PositiveReal root ∧
  CutEquivalent
    (positiveProductCut (realCut root) (realCut root))
    radicand

PositiveQuotient : Cut → Real → Real → Set
PositiveQuotient numerator denominator quotient =
  PositiveReal denominator ∧
  PositiveReal quotient ∧
  CutEquivalent
    (positiveProductCut (realCut quotient) (realCut denominator))
    numerator

PairwiseProductSumAtLeastThree : Real → Real → Real → Set
PairwiseProductSumAtLeastThree a b c =
  RationalLessOrEqualCut
    rationalThree
    (sumCut
      (sumCut
        (positiveProductCut (realCut a) (realCut b))
        (positiveProductCut (realCut b) (realCut c)))
      (positiveProductCut (realCut c) (realCut a)))

PositiveSqrtQuotient : Real → Real → Real → Set₁
PositiveSqrtQuotient numerator other quotient =
  Σ Real
    (λ root →
      PositiveSquareRoot
        (sumCut (realCut numerator) (realCut other))
        root ∧
      PositiveQuotient
        (realCut numerator)
        root
        quotient)

LeftRadicalValue : Real → Set₁
LeftRadicalValue value =
  Σ Real
    (λ root-two →
      PositiveSquareRoot (rationalCut rationalTwo) root-two ∧
      PositiveQuotient (rationalCut rationalThree) root-two value)

CyclicRadicalInequality : Real → Real → Real → Set₁
CyclicRadicalInequality a b c =
  Σ Real
    (λ left-side →
      Σ Real
        (λ a-term →
          Σ Real
            (λ b-term →
              Σ Real
                (λ c-term →
                  LeftRadicalValue left-side ∧
                  PositiveSqrtQuotient a b a-term ∧
                  PositiveSqrtQuotient b c b-term ∧
                  PositiveSqrtQuotient c a c-term ∧
                  RealLessOrEqualCut
                    left-side
                    (sumCut
                      (sumCut (realCut a-term) (realCut b-term))
                      (realCut c-term))))))

algebra-abpbcpcageq3-sumaonsqrtapbgeq3onsqrt2 : Set₁
algebra-abpbcpcageq3-sumaonsqrtapbgeq3onsqrt2 =
  (a b c : Real) →
  PositiveReal a →
  PositiveReal b →
  PositiveReal c →
  PairwiseProductSumAtLeastThree a b c →
  CyclicRadicalInequality a b c
