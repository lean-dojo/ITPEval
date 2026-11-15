-- Statement-only formalization of thousand-theorems corpus artifact Q657482
-- (thousand-theorems__agda__Q657482), "Abel–Ruffini theorem": there exists a
-- complex number algebraic over the rationals that is not solvable by radicals.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Q657482_abel_ruffini_theorem where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Primitive using (Level; _⊔_)

infix 4 _≠_
infixr 3 _∧_
infixr 2 _∨_

data Bottom : Set where

Not : ∀ {ℓ} → Set ℓ → Set ℓ
Not proposition =
  proposition → Bottom

_≠_ : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ
x ≠ y =
  Not (x ≡ y)

record _∧_ {ℓ₁ ℓ₂ : Level}
  (A : Set ℓ₁) (B : Set ℓ₂) :
  Set (ℓ₁ ⊔ ℓ₂) where
  constructor both
  field
    first  : A
    second : B

data _∨_ {ℓ₁ ℓ₂ : Level}
  (A : Set ℓ₁) (B : Set ℓ₂) :
  Set (ℓ₁ ⊔ ℓ₂) where
  left  : A → A ∨ B
  right : B → A ∨ B

record CompleteOrderedField (R : Set) : Set₁ where
  field
    zeroR oneR : R
    addR multiplyR : R → R → R
    negateR inverseR : R → R
    lessOrEqualR : R → R → Set
    fromNatR : Nat → R

    one-not-zeroR :
      oneR ≠ zeroR

    add-commutativeR :
      (x y : R) →
      addR x y ≡ addR y x
    add-associativeR :
      (x y z : R) →
      addR (addR x y) z ≡ addR x (addR y z)
    add-zeroR :
      (x : R) →
      addR x zeroR ≡ x
    add-inverseR :
      (x : R) →
      addR x (negateR x) ≡ zeroR

    multiply-commutativeR :
      (x y : R) →
      multiplyR x y ≡ multiplyR y x
    multiply-associativeR :
      (x y z : R) →
      multiplyR (multiplyR x y) z ≡
      multiplyR x (multiplyR y z)
    multiply-oneR :
      (x : R) →
      multiplyR x oneR ≡ x
    multiply-zeroR :
      (x : R) →
      multiplyR x zeroR ≡ zeroR
    distributeR :
      (x y z : R) →
      multiplyR x (addR y z) ≡
      addR (multiplyR x y) (multiplyR x z)
    inverse-zeroR :
      inverseR zeroR ≡ zeroR
    multiply-inverseR :
      (x : R) →
      x ≠ zeroR →
      multiplyR x (inverseR x) ≡ oneR

    order-reflexiveR :
      (x : R) →
      lessOrEqualR x x
    order-transitiveR :
      (x y z : R) →
      lessOrEqualR x y →
      lessOrEqualR y z →
      lessOrEqualR x z
    order-antisymmetricR :
      (x y : R) →
      lessOrEqualR x y →
      lessOrEqualR y x →
      x ≡ y
    order-totalR :
      (x y : R) →
      lessOrEqualR x y ∨ lessOrEqualR y x
    add-orderR :
      (x y z : R) →
      lessOrEqualR x y →
      lessOrEqualR (addR z x) (addR z y)
    multiply-nonnegativeR :
      (x y : R) →
      lessOrEqualR zeroR x →
      lessOrEqualR zeroR y →
      lessOrEqualR zeroR (multiplyR x y)
    zero-less-than-oneR :
      lessOrEqualR zeroR oneR ∧ zeroR ≠ oneR

    fromNat-zeroR :
      fromNatR zero ≡ zeroR
    fromNat-successorR :
      (n : Nat) →
      fromNatR (suc n) ≡ addR (fromNatR n) oneR
    characteristic-zeroR :
      (m n : Nat) →
      fromNatR m ≡ fromNatR n →
      m ≡ n

    archimedeanR :
      (x : R) →
      Σ Nat (λ n → lessOrEqualR x (fromNatR n))
    least-upper-boundR :
      (P : R → Set) →
      Σ R P →
      Σ R
        (λ upper →
          (x : R) →
          P x →
          lessOrEqualR x upper) →
      Σ R
        (λ supremum →
          ((x : R) →
            P x →
            lessOrEqualR x supremum)
          ∧
          ((upper : R) →
            ((x : R) →
              P x →
              lessOrEqualR x upper) →
            lessOrEqualR supremum upper))

open CompleteOrderedField

record Complex (R : Set) : Set where
  constructor complex
  field
    realPart      : R
    imaginaryPart : R

zeroC :
  {R : Set} →
  CompleteOrderedField R →
  Complex R
zeroC reals =
  complex (zeroR reals) (zeroR reals)

oneC :
  {R : Set} →
  CompleteOrderedField R →
  Complex R
oneC reals =
  complex (oneR reals) (zeroR reals)

addC :
  {R : Set} →
  CompleteOrderedField R →
  Complex R →
  Complex R →
  Complex R
addC reals (complex a b) (complex c d) =
  complex
    (addR reals a c)
    (addR reals b d)

negateC :
  {R : Set} →
  CompleteOrderedField R →
  Complex R →
  Complex R
negateC reals (complex a b) =
  complex
    (negateR reals a)
    (negateR reals b)

subtractR :
  {R : Set} →
  CompleteOrderedField R →
  R →
  R →
  R
subtractR reals x y =
  addR reals x (negateR reals y)

multiplyC :
  {R : Set} →
  CompleteOrderedField R →
  Complex R →
  Complex R →
  Complex R
multiplyC reals (complex a b) (complex c d) =
  complex
    (subtractR reals
      (multiplyR reals a c)
      (multiplyR reals b d))
    (addR reals
      (multiplyR reals a d)
      (multiplyR reals b c))

inverseC :
  {R : Set} →
  CompleteOrderedField R →
  Complex R →
  Complex R
inverseC reals (complex a b) =
  complex
    (multiplyR reals a denominator-inverse)
    (negateR reals
      (multiplyR reals b denominator-inverse))
  where
    denominator =
      addR reals
        (multiplyR reals a a)
        (multiplyR reals b b)

    denominator-inverse =
      inverseR reals denominator

powerC :
  {R : Set} →
  CompleteOrderedField R →
  Complex R →
  Nat →
  Complex R
powerC reals x zero =
  oneC reals
powerC reals x (suc n) =
  multiplyC reals x (powerC reals x n)

fromIntR :
  {R : Set} →
  CompleteOrderedField R →
  Int →
  R
fromIntR reals (pos n) =
  fromNatR reals n
fromIntR reals (negsuc n) =
  negateR reals (fromNatR reals (suc n))

record Rational : Set where
  constructor fraction
  field
    numerator            : Int
    denominatorMinusOne : Nat

rationalToComplex :
  {R : Set} →
  CompleteOrderedField R →
  Rational →
  Complex R
rationalToComplex reals q =
  complex
    (multiplyR reals
      (fromIntR reals (Rational.numerator q))
      (inverseR reals
        (fromNatR reals
          (suc (Rational.denominatorMinusOne q)))))
    (zeroR reals)

data HasNonzeroRationalCoefficient :
  List Rational →
  Set where

  here :
    {coefficient : Rational}
    {coefficients : List Rational} →
    Rational.numerator coefficient ≠ pos zero →
    HasNonzeroRationalCoefficient
      (coefficient ∷ coefficients)

  there :
    {coefficient : Rational}
    {coefficients : List Rational} →
    HasNonzeroRationalCoefficient coefficients →
    HasNonzeroRationalCoefficient
      (coefficient ∷ coefficients)

evaluateRationalPolynomial :
  {R : Set} →
  CompleteOrderedField R →
  List Rational →
  Complex R →
  Complex R
evaluateRationalPolynomial reals [] x =
  zeroC reals
evaluateRationalPolynomial reals
  (coefficient ∷ coefficients) x =
  addC reals
    (rationalToComplex reals coefficient)
    (multiplyC reals x
      (evaluateRationalPolynomial reals coefficients x))

IsAlgebraic :
  {R : Set} →
  CompleteOrderedField R →
  Complex R →
  Set
IsAlgebraic reals x =
  Σ (List Rational)
    (λ coefficients →
      HasNonzeroRationalCoefficient coefficients ∧
      evaluateRationalPolynomial reals coefficients x ≡
      zeroC reals)

record RadicalClosedSubfield
  {R : Set}
  (reals : CompleteOrderedField R) :
  Set₁ where

  field
    contains :
      Complex R →
      Set

    contains-rational :
      (q : Rational) →
      contains (rationalToComplex reals q)

    contains-add :
      {x y : Complex R} →
      contains x →
      contains y →
      contains (addC reals x y)

    contains-negate :
      {x : Complex R} →
      contains x →
      contains (negateC reals x)

    contains-multiply :
      {x y : Complex R} →
      contains x →
      contains y →
      contains (multiplyC reals x y)

    contains-inverse :
      {x : Complex R} →
      contains x →
      contains (inverseC reals x)

    closed-under-roots :
      (x : Complex R) →
      (n : Nat) →
      n ≠ zero →
      contains (powerC reals x n) →
      contains x

open RadicalClosedSubfield

-- Membership in the intersection of all radical-closed intermediate fields.
SolvableByRadicals :
  {R : Set} →
  CompleteOrderedField R →
  Complex R →
  Set₁
SolvableByRadicals reals x =
  (subfield : RadicalClosedSubfield reals) →
  contains subfield x

abel-ruffini-theorem : Set₁
abel-ruffini-theorem =
  (R : Set) →
  (reals : CompleteOrderedField R) →
  Σ (Complex R)
    (λ x →
      IsAlgebraic reals x ∧
      Not (SolvableByRadicals reals x))
