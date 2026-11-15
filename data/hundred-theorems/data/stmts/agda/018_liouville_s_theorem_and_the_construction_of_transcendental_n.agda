-- Statement-only formalization of "Liouville's Theorem and the Construction of Transcendental
-- Numbers" from Hundred Theorems item 018. This file contains no proof.

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Sigma using (Σ)

infix 4 _≠_ _≤_
infixr 3 _∧_
infixr 2 _∨_

data ⊥ : Set where

¬_ : Set → Set
¬ A = A → ⊥

_≠_ : {A : Set} → A → A → Set
x ≠ y = ¬ (x ≡ y)

record _∧_ (A B : Set) : Set where
  constructor _,_
  field
    first  : A
    second : B

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

record CompleteOrderedField (R : Set) : Set₁ where
  field
    zeroR oneR : R
    add multiply : R → R → R
    negate reciprocal absoluteValue : R → R
    lessOrEqual : R → R → Set
    fromNat : Nat → R

    one-not-zero :
      oneR ≠ zeroR

    add-commutative :
      (x y : R) → add x y ≡ add y x
    add-associative :
      (x y z : R) → add (add x y) z ≡ add x (add y z)
    add-zero :
      (x : R) → add x zeroR ≡ x
    add-inverse :
      (x : R) → add x (negate x) ≡ zeroR

    multiply-commutative :
      (x y : R) → multiply x y ≡ multiply y x
    multiply-associative :
      (x y z : R) →
      multiply (multiply x y) z ≡ multiply x (multiply y z)
    multiply-one :
      (x : R) → multiply x oneR ≡ x
    multiply-zero :
      (x : R) → multiply x zeroR ≡ zeroR
    distribute :
      (x y z : R) →
      multiply x (add y z) ≡
      add (multiply x y) (multiply x z)
    multiply-inverse :
      (x : R) →
      x ≠ zeroR →
      multiply x (reciprocal x) ≡ oneR

    order-reflexive :
      (x : R) → lessOrEqual x x
    order-transitive :
      (x y z : R) →
      lessOrEqual x y →
      lessOrEqual y z →
      lessOrEqual x z
    order-antisymmetric :
      (x y : R) →
      lessOrEqual x y →
      lessOrEqual y x →
      x ≡ y
    order-total :
      (x y : R) →
      lessOrEqual x y ∨ lessOrEqual y x
    add-order :
      (x y z : R) →
      lessOrEqual x y →
      lessOrEqual (add z x) (add z y)
    multiply-nonnegative :
      (x y : R) →
      lessOrEqual zeroR x →
      lessOrEqual zeroR y →
      lessOrEqual zeroR (multiply x y)
    zero-less-than-one :
      lessOrEqual zeroR oneR ∧ oneR ≠ zeroR

    fromNat-zero :
      fromNat zero ≡ zeroR
    fromNat-successor :
      (n : Nat) → fromNat (suc n) ≡ add (fromNat n) oneR
    fromNat-addition :
      (m n : Nat) →
      fromNat (m + n) ≡ add (fromNat m) (fromNat n)
    fromNat-multiplication :
      (m n : Nat) →
      fromNat (m * n) ≡ multiply (fromNat m) (fromNat n)
    characteristic-zero :
      (m n : Nat) → fromNat m ≡ fromNat n → m ≡ n

    absolute-nonnegative :
      (x : R) → lessOrEqual zeroR (absoluteValue x)
    absolute-of-nonnegative :
      (x : R) →
      lessOrEqual zeroR x →
      absoluteValue x ≡ x
    absolute-of-nonpositive :
      (x : R) →
      lessOrEqual x zeroR →
      absoluteValue x ≡ negate x

    archimedean :
      (x : R) → Σ Nat (λ n → lessOrEqual x (fromNat n))

    least-upper-bound :
      (P : R → Set) →
      Σ R (λ x → P x) →
      Σ R (λ upper → (x : R) → P x → lessOrEqual x upper) →
      Σ R
        (λ supremum →
          ((x : R) → P x → lessOrEqual x supremum) ∧
          ((upper : R) →
            ((x : R) → P x → lessOrEqual x upper) →
            lessOrEqual supremum upper))

subtract :
  {R : Set} →
  CompleteOrderedField R →
  R →
  R →
  R
subtract reals x y =
  CompleteOrderedField.add reals x
    (CompleteOrderedField.negate reals y)

divide :
  {R : Set} →
  CompleteOrderedField R →
  R →
  R →
  R
divide reals x y =
  CompleteOrderedField.multiply reals x
    (CompleteOrderedField.reciprocal reals y)

fromInt :
  {R : Set} →
  CompleteOrderedField R →
  Int →
  R
fromInt reals (pos n) =
  CompleteOrderedField.fromNat reals n
fromInt reals (negsuc n) =
  CompleteOrderedField.negate reals
    (CompleteOrderedField.fromNat reals (suc n))

power :
  {R : Set} →
  CompleteOrderedField R →
  R →
  Nat →
  R
power reals x zero =
  CompleteOrderedField.oneR reals
power reals x (suc n) =
  CompleteOrderedField.multiply reals x (power reals x n)

factorial : Nat → Nat
factorial zero = suc zero
factorial (suc n) = suc n * factorial n

StrictLess :
  {R : Set} →
  CompleteOrderedField R →
  R →
  R →
  Set
StrictLess reals x y =
  CompleteOrderedField.lessOrEqual reals x y ∧ x ≠ y

Positive :
  {R : Set} →
  CompleteOrderedField R →
  R →
  Set
Positive reals x =
  StrictLess reals (CompleteOrderedField.zeroR reals) x

partialSum :
  {R : Set} →
  CompleteOrderedField R →
  (Nat → R) →
  Nat →
  R
partialSum reals sequence zero =
  CompleteOrderedField.zeroR reals
partialSum reals sequence (suc n) =
  CompleteOrderedField.add reals
    (partialSum reals sequence n)
    (sequence n)

SequentialLimit :
  {R : Set} →
  CompleteOrderedField R →
  (Nat → R) →
  R →
  Set
SequentialLimit {R} reals sequence limit =
  (epsilon : R) →
  Positive reals epsilon →
  Σ Nat
    (λ cutoff →
      (n : Nat) →
      cutoff ≤ n →
      CompleteOrderedField.lessOrEqual reals
        (CompleteOrderedField.absoluteValue reals
          (subtract reals (sequence n) limit))
        epsilon)

SeriesSum :
  {R : Set} →
  CompleteOrderedField R →
  (Nat → R) →
  R →
  Set
SeriesSum reals terms limit =
  SequentialLimit reals (partialSum reals terms) limit

data HasNonzeroIntegerCoefficient : List Int → Set where
  here :
    {coefficient : Int} {coefficients : List Int} →
    coefficient ≠ pos zero →
    HasNonzeroIntegerCoefficient (coefficient ∷ coefficients)

  there :
    {coefficient : Int} {coefficients : List Int} →
    HasNonzeroIntegerCoefficient coefficients →
    HasNonzeroIntegerCoefficient (coefficient ∷ coefficients)

evaluateIntegerPolynomial :
  {R : Set} →
  CompleteOrderedField R →
  List Int →
  R →
  R
evaluateIntegerPolynomial reals [] x =
  CompleteOrderedField.zeroR reals
evaluateIntegerPolynomial reals
  (coefficient ∷ coefficients) x =
  CompleteOrderedField.add reals
    (fromInt reals coefficient)
    (CompleteOrderedField.multiply reals x
      (evaluateIntegerPolynomial reals coefficients x))

Algebraic :
  {R : Set} →
  CompleteOrderedField R →
  R →
  Set
Algebraic reals x =
  Σ (List Int)
    (λ coefficients →
      HasNonzeroIntegerCoefficient coefficients ∧
      evaluateIntegerPolynomial reals coefficients x ≡
      CompleteOrderedField.zeroR reals)

Transcendental :
  {R : Set} →
  CompleteOrderedField R →
  R →
  Set
Transcendental reals x =
  ¬ Algebraic reals x

positiveDenominator : Nat → Nat
positiveDenominator denominatorMinusOne =
  suc denominatorMinusOne

positiveRationalValue :
  {R : Set} →
  CompleteOrderedField R →
  Int →
  Nat →
  R
positiveRationalValue reals numerator denominatorMinusOne =
  divide reals
    (fromInt reals numerator)
    (CompleteOrderedField.fromNat reals
      (positiveDenominator denominatorMinusOne))

Irrational :
  {R : Set} →
  CompleteOrderedField R →
  R →
  Set
Irrational reals x =
  (numerator : Int) →
  (denominatorMinusOne : Nat) →
  x ≠ positiveRationalValue reals numerator denominatorMinusOne

LiouvilleLowerBound :
  {R : Set} →
  CompleteOrderedField R →
  R →
  Set
LiouvilleLowerBound {R} reals x =
  Σ Nat
    (λ degree →
      Σ R
        (λ constant →
          Positive reals constant
          ∧
          ((numerator : Int) →
            (denominatorMinusOne : Nat) →
            StrictLess reals
              (divide reals constant
                (power reals
                  (CompleteOrderedField.fromNat reals
                    (positiveDenominator denominatorMinusOne))
                  degree))
              (CompleteOrderedField.absoluteValue reals
                (subtract reals x
                  (positiveRationalValue reals numerator
                    denominatorMinusOne))))))

rationalDenominator : Nat → Nat
rationalDenominator denominatorMinusTwo =
  suc (suc denominatorMinusTwo)

rationalValue :
  {R : Set} →
  CompleteOrderedField R →
  Int →
  Nat →
  R
rationalValue reals numerator denominatorMinusTwo =
  divide reals
    (fromInt reals numerator)
    (CompleteOrderedField.fromNat reals
      (rationalDenominator denominatorMinusTwo))

approximationError :
  {R : Set} →
  CompleteOrderedField R →
  R →
  Int →
  Nat →
  R
approximationError reals x numerator denominatorMinusTwo =
  CompleteOrderedField.absoluteValue reals
    (subtract reals x
      (rationalValue reals numerator denominatorMinusTwo))

Liouville :
  {R : Set} →
  CompleteOrderedField R →
  R →
  Set
Liouville reals x =
  (n : Nat) →
  Σ Int
    (λ numerator →
      Σ Nat
        (λ denominatorMinusTwo →
          Positive reals
            (approximationError reals x numerator denominatorMinusTwo)
          ∧
          StrictLess reals
            (approximationError reals x numerator denominatorMinusTwo)
            (divide reals
              (CompleteOrderedField.oneR reals)
              (power reals
                (CompleteOrderedField.fromNat reals
                  (rationalDenominator denominatorMinusTwo))
                n))))

liouvilleTerm :
  {R : Set} →
  CompleteOrderedField R →
  Nat →
  R
liouvilleTerm reals k =
  divide reals
    (CompleteOrderedField.oneR reals)
    (power reals
      (CompleteOrderedField.fromNat reals 10)
      (factorial (suc k)))

IsLiouvilleConstant :
  {R : Set} →
  CompleteOrderedField R →
  R →
  Set
IsLiouvilleConstant reals x =
  SeriesSum reals (liouvilleTerm reals) x

hundred-theorems-018 : Set₁
hundred-theorems-018 =
  (R : Set) →
  (reals : CompleteOrderedField R) →
  ((x : R) →
    Algebraic reals x →
    Irrational reals x →
    LiouvilleLowerBound reals x)
  ∧
  ((x : R) →
    Liouville reals x →
    Transcendental reals x)
  ∧
  Σ R
    (λ x →
      IsLiouvilleConstant reals x ∧
      Liouville reals x ∧
      Transcendental reals x)
