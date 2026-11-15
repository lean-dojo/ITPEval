-- Statement-only formalization of miniF2F valid artifact aime_1984_p5:
-- for positive real a and b, the two coupled base-8 and base-4 logarithm
-- equations imply a * b = 512. This file contains no proof.

{-# OPTIONS --safe #-}

module aime-1984-p5 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≠_ _≤N_
infixr 3 _∧_
infixr 2 _∨_

data ⊥ : Set where

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

record _∧_ (A B : Set) : Set where
  constructor _,_
  field
    first  : A
    second : B

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _≤N_ : Nat → Nat → Set where
  zero≤   : {n : Nat} → zero ≤N n
  suc≤suc : {m n : Nat} → m ≤N n → suc m ≤N suc n

-- A complete Archimedean ordered field is a presentation of the real numbers.
record CompleteArchimedeanOrderedField (R : Set) : Set₁ where
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
      (x y z : R) →
      add (add x y) z ≡ add x (add y z)
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
      multiply x (add y z) ≡ add (multiply x y) (multiply x z)
    reciprocal-zero :
      reciprocal zeroR ≡ zeroR
    multiply-reciprocal :
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
      (x y : R) → lessOrEqual x y ∨ lessOrEqual y x
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
      lessOrEqual zeroR oneR ∧ zeroR ≠ oneR

    fromNat-zero :
      fromNat zero ≡ zeroR
    fromNat-successor :
      (n : Nat) →
      fromNat (suc n) ≡ add (fromNat n) oneR
    fromNat-addition :
      (m n : Nat) →
      fromNat (m + n) ≡ add (fromNat m) (fromNat n)
    fromNat-multiplication :
      (m n : Nat) →
      fromNat (m * n) ≡ multiply (fromNat m) (fromNat n)
    fromNat-injective :
      (m n : Nat) →
      fromNat m ≡ fromNat n →
      m ≡ n

    absolute-of-nonnegative :
      (x : R) →
      lessOrEqual zeroR x →
      absoluteValue x ≡ x
    absolute-of-nonpositive :
      (x : R) →
      lessOrEqual x zeroR →
      absoluteValue x ≡ negate x

    archimedean :
      (x : R) →
      Exists Nat (λ n → lessOrEqual x (fromNat n))
    least-upper-bound :
      (subset : R → Set) →
      Exists R subset →
      Exists R
        (λ upper →
          (x : R) →
          subset x →
          lessOrEqual x upper) →
      Exists R
        (λ supremum →
          ((x : R) →
            subset x →
            lessOrEqual x supremum)
          ∧
          ((upper : R) →
            ((x : R) →
              subset x →
              lessOrEqual x upper) →
            lessOrEqual supremum upper))

open CompleteArchimedeanOrderedField

StrictLess :
  {R : Set} →
  CompleteArchimedeanOrderedField R →
  R →
  R →
  Set
StrictLess reals x y =
  lessOrEqual reals x y ∧ x ≠ y

subtract :
  {R : Set} →
  CompleteArchimedeanOrderedField R →
  R →
  R →
  R
subtract reals x y =
  add reals x (negate reals y)

divide :
  {R : Set} →
  CompleteArchimedeanOrderedField R →
  R →
  R →
  R
divide reals numerator denominator =
  multiply reals numerator (reciprocal reals denominator)

power :
  {R : Set} →
  CompleteArchimedeanOrderedField R →
  R →
  Nat →
  R
power reals x zero =
  oneR reals
power reals x (suc n) =
  multiply reals (power reals x n) x

factorial : Nat → Nat
factorial zero =
  suc zero
factorial (suc n) =
  suc n * factorial n

sumFirst :
  {R : Set} →
  CompleteArchimedeanOrderedField R →
  (Nat → R) →
  Nat →
  R
sumFirst reals term zero =
  zeroR reals
sumFirst reals term (suc n) =
  add reals (sumFirst reals term n) (term n)

exponentialPartialSum :
  {R : Set} →
  CompleteArchimedeanOrderedField R →
  R →
  Nat →
  R
exponentialPartialSum reals x n =
  sumFirst reals
    (λ k →
      divide reals
        (power reals x k)
        (fromNat reals (factorial k)))
    n

SequentialLimit :
  {R : Set} →
  CompleteArchimedeanOrderedField R →
  (Nat → R) →
  R →
  Set
SequentialLimit {R} reals sequence limit =
  (epsilon : R) →
  StrictLess reals (zeroR reals) epsilon →
  Exists Nat
    (λ cutoff →
      (n : Nat) →
      cutoff ≤N n →
      StrictLess reals
        (absoluteValue reals
          (subtract reals (sequence n) limit))
        epsilon)

-- ExponentialValue x y is the exact graph y = exp(x), using convergence of
-- the full Taylor partial-sum sequence at the fixed real argument x.
ExponentialValue :
  {R : Set} →
  CompleteArchimedeanOrderedField R →
  R →
  R →
  Set
ExponentialValue reals x y =
  SequentialLimit reals
    (exponentialPartialSum reals x)
    y

-- This is the total real logarithm convention used by Real.log: log 0 = 0,
-- and for nonzero x, log x is the inverse-exponential value of |x|.
LogarithmValue :
  {R : Set} →
  CompleteArchimedeanOrderedField R →
  R →
  R →
  Set
LogarithmValue reals argument result =
  (argument ≡ zeroR reals ∧ result ≡ zeroR reals)
  ∨
  (argument ≠ zeroR reals ∧
   ExponentialValue reals result (absoluteValue reals argument))

LogBaseValue :
  {R : Set} →
  CompleteArchimedeanOrderedField R →
  R →
  R →
  R →
  Set
LogBaseValue {R} reals base argument result =
  Exists R
    (λ logarithmOfArgument →
      Exists R
        (λ logarithmOfBase →
          LogarithmValue reals argument logarithmOfArgument
          ∧
          LogarithmValue reals base logarithmOfBase
          ∧
          result ≡
            divide reals logarithmOfArgument logarithmOfBase))

FirstEquation :
  {R : Set} →
  CompleteArchimedeanOrderedField R →
  R →
  R →
  Set
FirstEquation {R} reals a b =
  Exists R
    (λ logarithmOfA →
      Exists R
        (λ logarithmOfBSquared →
          LogBaseValue reals
            (fromNat reals 8)
            a
            logarithmOfA
          ∧
          LogBaseValue reals
            (fromNat reals 4)
            (multiply reals b b)
            logarithmOfBSquared
          ∧
          add reals logarithmOfA logarithmOfBSquared
            ≡ fromNat reals 5))

SecondEquation :
  {R : Set} →
  CompleteArchimedeanOrderedField R →
  R →
  R →
  Set
SecondEquation {R} reals a b =
  Exists R
    (λ logarithmOfB →
      Exists R
        (λ logarithmOfASquared →
          LogBaseValue reals
            (fromNat reals 8)
            b
            logarithmOfB
          ∧
          LogBaseValue reals
            (fromNat reals 4)
            (multiply reals a a)
            logarithmOfASquared
          ∧
          add reals logarithmOfB logarithmOfASquared
            ≡ fromNat reals 7))

aime-1984-p5 : Set₁
aime-1984-p5 =
  (R : Set) →
  (reals : CompleteArchimedeanOrderedField R) →
  (a b : R) →
  StrictLess reals (zeroR reals) a →
  StrictLess reals (zeroR reals) b →
  FirstEquation reals a b →
  SecondEquation reals a b →
  multiply reals a b ≡ fromNat reals 512
