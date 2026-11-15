-- Statement-only formalization of miniF2F valid problem aime_1991_p6 using exact
-- Dedekind-cut real numbers: a finite sum of floors at hundredth increments determines
-- the floor of one hundred times the real number. This file contains no proof.

module aime-1991-p6 where

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

negateInt : Int → Int
negateInt (pos zero) = pos zero
negateInt (pos (suc n)) = negsuc n
negateInt (negsuc n) = pos (suc n)

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

rationalNegate : Rational → Rational
rationalNegate q =
  fraction
    (negateInt (Rational.numerator q))
    (Rational.denominator-minus-one q)

rationalSubtract : Rational → Rational → Rational
rationalSubtract p q =
  rationalAdd p (rationalNegate q)

rationalDivideByPositive :
  Rational →
  Nat →
  Rational
rationalDivideByPositive q denominator-minus-one =
  fraction
    (Rational.numerator q)
    (natPred
      (rationalDenominator q *
       suc denominator-minus-one))

rationalFromInt : Int → Rational
rationalFromInt z = fraction z zero

rationalFromNat : Nat → Rational
rationalFromNat n = rationalFromInt (pos n)

rationalZero rationalOne : Rational
rationalZero = rationalFromNat 0
rationalOne = rationalFromNat 1

hundredth : Nat → Rational
hundredth n = fraction (pos n) 99

Cut : Set₁
Cut = Rational → Set

record IsDedekindReal (lower : Cut) : Set₁ where
  field
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

shiftCutByHundredth :
  Cut →
  Nat →
  Cut
shiftCutByHundredth lower k q =
  lower (rationalSubtract q (hundredth k))

timesHundredCut : Cut → Cut
timesHundredCut lower q =
  lower (rationalDivideByPositive q 99)

RationalLessOrEqualCut :
  Rational →
  Cut →
  Set
RationalLessOrEqualCut q lower =
  (p : Rational) →
  rationalLess p q →
  lower p

CutLessThanRational :
  Cut →
  Rational →
  Set
CutLessThanRational lower q =
  Exists Rational
    (λ p →
      ¬ lower p ∧
      rationalLess p q)

IsFloor : Cut → Int → Set
IsFloor lower z =
  RationalLessOrEqualCut
    (rationalFromInt z)
    lower
  ∧
  CutLessThanRational
    lower
    (rationalAdd
      (rationalFromInt z)
      rationalOne)

FloorRangeSum :
  Cut →
  Nat →
  Nat →
  Int →
  Set
FloorRangeSum lower start zero total =
  total ≡ pos zero
FloorRangeSum lower start (suc count) total =
  Exists Int
    (λ term →
      Exists Int
        (λ rest →
          IsFloor
            (shiftCutByHundredth lower start)
            term
          ∧
          FloorRangeSum
            lower
            (suc start)
            count
            rest
          ∧
          (total ≡ term +z rest)))

aime-1991-p6 : Set₁
aime-1991-p6 =
  (r : Cut) →
  IsDedekindReal r →
  FloorRangeSum r 19 73 (pos 546) →
  IsFloor (timesHundredCut r) (pos 743)
