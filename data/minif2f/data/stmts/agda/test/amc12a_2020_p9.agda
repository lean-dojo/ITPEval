-- Statement-only formalization of miniF2F test problem amc12a_2020_p9: the real
-- solutions on [0, 2*pi] of tan(2*x) = cos(x/2) have cardinality five. This file
-- contains no proof.

module amc12a-2020-p9 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≤ℕ_ _<ℕ_ _≤ℚ_ _<ℚ_ _∈ᴿ_
infixr 3 _∧_
infixr 2 _∨_
infix 2 _↔_

data ⊥ : Set where

record _∧_ (A B : Set) : Set where
  constructor conjunction
  field
    left  : A
    right : B

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

record _↔_ (A B : Set) : Set where
  field
    forward  : A → B
    backward : B → A

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _≤ℕ_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ℕ n
  suc≤  : {m n : Nat} → m ≤ℕ n → suc m ≤ℕ suc n

_<ℕ_ : Nat → Nat → Set
m <ℕ n = suc m ≤ℕ n

pred : Nat → Nat
pred zero = zero
pred (suc n) = n

record Integer : Set where
  constructor difference
  field
    positivePart : Nat
    negativePart : Nat

zeroℤ : Integer
zeroℤ = difference zero zero

oneℤ : Integer
oneℤ = difference (suc zero) zero

negateℤ : Integer → Integer
negateℤ (difference positive negative) =
  difference negative positive

addℤ : Integer → Integer → Integer
addℤ (difference positive₁ negative₁) (difference positive₂ negative₂) =
  difference
    (positive₁ + positive₂)
    (negative₁ + negative₂)

multiplyℤ : Integer → Integer → Integer
multiplyℤ
  (difference positive₁ negative₁)
  (difference positive₂ negative₂) =
  difference
    (positive₁ * positive₂ + negative₁ * negative₂)
    (positive₁ * negative₂ + negative₁ * positive₂)

scaleℤ : Integer → Nat → Integer
scaleℤ (difference positive negative) n =
  difference (positive * n) (negative * n)

_≤ℤ_ : Integer → Integer → Set
difference positive₁ negative₁ ≤ℤ difference positive₂ negative₂ =
  positive₁ + negative₂ ≤ℕ positive₂ + negative₁

_<ℤ_ : Integer → Integer → Set
difference positive₁ negative₁ <ℤ difference positive₂ negative₂ =
  positive₁ + negative₂ <ℕ positive₂ + negative₁

record Rational : Set where
  constructor fraction
  field
    numerator       : Integer
    denominatorBase : Nat

denominator : Rational → Nat
denominator q = suc (Rational.denominatorBase q)

zeroℚ : Rational
zeroℚ = fraction zeroℤ zero

oneℚ : Rational
oneℚ = fraction oneℤ zero

fromNatℚ : Nat → Rational
fromNatℚ n = fraction (difference n zero) zero

negateℚ : Rational → Rational
negateℚ q =
  fraction
    (negateℤ (Rational.numerator q))
    (Rational.denominatorBase q)

addℚ : Rational → Rational → Rational
addℚ q r =
  fraction
    (addℤ
      (scaleℤ (Rational.numerator q) (denominator r))
      (scaleℤ (Rational.numerator r) (denominator q)))
    (pred (denominator q * denominator r))

multiplyℚ : Rational → Rational → Rational
multiplyℚ q r =
  fraction
    (multiplyℤ (Rational.numerator q) (Rational.numerator r))
    (pred (denominator q * denominator r))

scaleℚ : Nat → Rational → Rational
scaleℚ n q =
  fraction
    (scaleℤ (Rational.numerator q) n)
    (Rational.denominatorBase q)

divideByPositiveNatℚ : Rational → Nat → Rational
divideByPositiveNatℚ q n =
  fraction
    (Rational.numerator q)
    (pred (denominator q * n))

_≤ℚ_ : Rational → Rational → Set
q ≤ℚ r =
  scaleℤ (Rational.numerator q) (denominator r)
  ≤ℤ
  scaleℤ (Rational.numerator r) (denominator q)

_<ℚ_ : Rational → Rational → Set
q <ℚ r =
  scaleℤ (Rational.numerator q) (denominator r)
  <ℤ
  scaleℤ (Rational.numerator r) (denominator q)

Positive : Rational → Set
Positive epsilon = zeroℚ <ℚ epsilon

Closeℚ : Rational → Rational → Rational → Set
Closeℚ q r epsilon =
  q <ℚ addℚ r epsilon ∧
  r <ℚ addℚ q epsilon

powerℚ : Rational → Nat → Rational
powerℚ q zero = oneℚ
powerℚ q (suc n) = multiplyℚ q (powerℚ q n)

factorial : Nat → Nat
factorial zero = suc zero
factorial (suc n) = suc n * factorial n

alternate : Rational → Nat → Rational
alternate q zero = q
alternate q (suc n) = negateℚ (alternate q n)

gregoryTerm : Nat → Rational
gregoryTerm n =
  fraction
    (Rational.numerator (alternate oneℚ n))
    (2 * n)

gregorySum : Nat → Rational
gregorySum zero = zeroℚ
gregorySum (suc n) = addℚ (gregorySum n) (gregoryTerm n)

piApproximation : Nat → Rational
piApproximation n = scaleℚ 4 (gregorySum n)

sineTerm : Rational → Nat → Rational
sineTerm x n =
  divideByPositiveNatℚ
    (alternate (powerℚ x (suc (2 * n))) n)
    (factorial (suc (2 * n)))

cosineTerm : Rational → Nat → Rational
cosineTerm x n =
  divideByPositiveNatℚ
    (alternate (powerℚ x (2 * n)) n)
    (factorial (2 * n))

sinePartialSum : Rational → Nat → Rational
sinePartialSum x zero = zeroℚ
sinePartialSum x (suc n) =
  addℚ (sinePartialSum x n) (sineTerm x n)

cosinePartialSum : Rational → Nat → Rational
cosinePartialSum x zero = zeroℚ
cosinePartialSum x (suc n) =
  addℚ (cosinePartialSum x n) (cosineTerm x n)

record Real : Set where
  constructor cauchyReal
  field
    approximation : Nat → Rational
    cauchyProperty :
      (epsilon : Rational) →
      Positive epsilon →
      Exists Nat λ N →
        (m n : Nat) →
        N ≤ℕ m →
        N ≤ℕ n →
        Closeℚ (approximation m) (approximation n) epsilon

EventuallyClose :
  (Nat → Rational) →
  (Nat → Rational) →
  Set
EventuallyClose first second =
  (epsilon : Rational) →
  Positive epsilon →
  Exists Nat λ N →
    (n : Nat) →
    N ≤ℕ n →
    Closeℚ (first n) (second n) epsilon

_≃ᴿ_ : Real → Real → Set
x ≃ᴿ y =
  EventuallyClose
    (Real.approximation x)
    (Real.approximation y)

EqualToRational : Real → Rational → Set
EqualToRational x q =
  EventuallyClose
    (Real.approximation x)
    (λ _ → q)

LessOrEqualᴿ : Real → Real → Set
LessOrEqualᴿ x y =
  (epsilon : Rational) →
  Positive epsilon →
  Exists Nat λ N →
    (n : Nat) →
    N ≤ℕ n →
    Real.approximation x n
      ≤ℚ addℚ (Real.approximation y n) epsilon

Nonnegativeᴿ : Real → Set
Nonnegativeᴿ x =
  (epsilon : Rational) →
  Positive epsilon →
  Exists Nat λ N →
    (n : Nat) →
    N ≤ℕ n →
    zeroℚ ≤ℚ addℚ (Real.approximation x n) epsilon

Addᴿ : Real → Real → Real → Set
Addᴿ x y sum =
  EventuallyClose
    (λ n →
      addℚ
        (Real.approximation x n)
        (Real.approximation y n))
    (Real.approximation sum)

Multiplyᴿ : Real → Real → Real → Set
Multiplyᴿ x y product =
  EventuallyClose
    (λ n →
      multiplyℚ
        (Real.approximation x n)
        (Real.approximation y n))
    (Real.approximation product)

Scaleᴿ : Nat → Real → Real → Set
Scaleᴿ multiplier x product =
  EventuallyClose
    (λ n → scaleℚ multiplier (Real.approximation x n))
    (Real.approximation product)

ConvergesToᴿ : (Nat → Rational) → Real → Set
ConvergesToᴿ sequence limit =
  EventuallyClose sequence (Real.approximation limit)

Piᴿ : Real → Set
Piᴿ pi = ConvergesToᴿ piApproximation pi

TaylorLimit :
  (Rational → Nat → Rational) →
  Real →
  Real →
  Set
TaylorLimit partialSum x value =
  (epsilon : Rational) →
  Positive epsilon →
  Exists Nat λ N →
    Exists Nat λ K →
      (n k : Nat) →
      N ≤ℕ n →
      K ≤ℕ k →
      Closeℚ
        (partialSum (Real.approximation x n) k)
        (Real.approximation value n)
        epsilon

Sineᴿ : Real → Real → Set
Sineᴿ x value = TaylorLimit sinePartialSum x value

Cosineᴿ : Real → Real → Set
Cosineᴿ x value = TaylorLimit cosinePartialSum x value

Tangentᴿ : Real → Real → Set
Tangentᴿ x value =
  Exists Real λ sineValue →
  Exists Real λ cosineValue →
    Sineᴿ x sineValue ∧
    Cosineᴿ x cosineValue ∧
    ((EqualToRational cosineValue zeroℚ ∧
      EqualToRational value zeroℚ)
     ∨
     ((EqualToRational cosineValue zeroℚ → ⊥) ∧
      Multiplyᴿ value cosineValue sineValue))

Solution : Real → Set
Solution x =
  Nonnegativeᴿ x ∧
  Exists Real λ pi →
  Exists Real λ twoPi →
  Exists Real λ twiceX →
  Exists Real λ halfX →
  Exists Real λ tangentValue →
  Exists Real λ cosineValue →
    Piᴿ pi ∧
    Scaleᴿ 2 pi twoPi ∧
    LessOrEqualᴿ x twoPi ∧
    Scaleᴿ 2 x twiceX ∧
    Scaleᴿ 2 halfX x ∧
    Tangentᴿ twiceX tangentValue ∧
    Cosineᴿ halfX cosineValue ∧
    tangentValue ≃ᴿ cosineValue

data _∈ᴿ_ (x : Real) : List Real → Set where
  hereᴿ :
    {y : Real} {ys : List Real} →
    x ≃ᴿ y →
    x ∈ᴿ (y ∷ ys)
  thereᴿ :
    {y : Real} {ys : List Real} →
    x ∈ᴿ ys →
    x ∈ᴿ (y ∷ ys)

data NoDuplicatesᴿ : List Real → Set where
  no-duplicates-empty :
    NoDuplicatesᴿ []
  no-duplicates-cons :
    {x : Real} {xs : List Real} →
    (x ∈ᴿ xs → ⊥) →
    NoDuplicatesᴿ xs →
    NoDuplicatesᴿ (x ∷ xs)

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

AMC12A2020P9 : Set
AMC12A2020P9 =
  Exists (List Real) λ solutions →
    NoDuplicatesᴿ solutions ∧
    length solutions ≡ 5 ∧
    ((x : Real) → (x ∈ᴿ solutions) ↔ Solution x)
