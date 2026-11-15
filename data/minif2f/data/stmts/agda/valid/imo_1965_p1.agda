-- Statement-only formalization of miniF2F valid problem imo_1965_p1: a real
-- trigonometric radical inequality forcing x into [pi / 4, 7 * pi / 4].
-- This file contains no proof.

module imo-1965-p1 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≠_ _≤N_
infixr 3 _∧_
infixr 2 _∨_

data ⊥ : Set where

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

record _∧_ (A B : Set) : Set where
  constructor conjunction
  field
    left  : A
    right : B

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

record CompleteOrderedField (R : Set) : Set₁ where
  field
    zeroR oneR : R
    add multiply : R → R → R
    negate inverse : R → R
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
    inverse-zero :
      inverse zeroR ≡ zeroR
    multiply-inverse :
      (x : R) →
      x ≠ zeroR →
      multiply x (inverse x) ≡ oneR

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
    add-monotone :
      (x y z : R) →
      lessOrEqual x y →
      lessOrEqual (add z x) (add z y)
    multiply-nonnegative :
      (x y : R) →
      lessOrEqual zeroR x →
      lessOrEqual zeroR y →
      lessOrEqual zeroR (multiply x y)
    zero-less-or-equal-one :
      lessOrEqual zeroR oneR

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
    fromNat-injective :
      (m n : Nat) → fromNat m ≡ fromNat n → m ≡ n

    archimedean :
      (x : R) →
      Exists Nat (λ n → lessOrEqual x (fromNat n))

    least-upper-bound :
      (P : R → Set) →
      Exists R P →
      Exists R
        (λ upper →
          (x : R) → P x → lessOrEqual x upper) →
      Exists R
        (λ supremum →
          ((x : R) → P x → lessOrEqual x supremum) ∧
          ((upper : R) →
            ((x : R) → P x → lessOrEqual x upper) →
            lessOrEqual supremum upper))

open CompleteOrderedField

subtract :
  {R : Set} →
  CompleteOrderedField R →
  R →
  R →
  R
subtract reals x y =
  add reals x (negate reals y)

divide :
  {R : Set} →
  CompleteOrderedField R →
  R →
  R →
  R
divide reals x y =
  multiply reals x (inverse reals y)

power :
  {R : Set} →
  CompleteOrderedField R →
  R →
  Nat →
  R
power reals x zero =
  oneR reals
power reals x (suc n) =
  multiply reals (power reals x n) x

factorial : Nat → Nat
factorial zero = 1
factorial (suc n) =
  suc n * factorial n

alternatingUnit :
  {R : Set} →
  CompleteOrderedField R →
  Nat →
  R
alternatingUnit reals zero =
  oneR reals
alternatingUnit reals (suc n) =
  negate reals (alternatingUnit reals n)

StrictLess :
  {R : Set} →
  CompleteOrderedField R →
  R →
  R →
  Set
StrictLess reals x y =
  lessOrEqual reals x y ∧ x ≠ y

ConvergesTo :
  {R : Set} →
  CompleteOrderedField R →
  (Nat → R) →
  R →
  Set
ConvergesTo reals sequence limit =
  (epsilon : _) →
  StrictLess reals (zeroR reals) epsilon →
  Exists Nat
    (λ cutoff →
      (n : Nat) →
      cutoff ≤N n →
      StrictLess reals
        (subtract reals limit epsilon)
        (sequence n) ∧
      StrictLess reals
        (sequence n)
        (add reals limit epsilon))

sumFirst :
  {R : Set} →
  CompleteOrderedField R →
  Nat →
  (Nat → R) →
  R
sumFirst reals zero term =
  zeroR reals
sumFirst reals (suc n) term =
  add reals
    (sumFirst reals n term)
    (term n)

SeriesHasSum :
  {R : Set} →
  CompleteOrderedField R →
  (Nat → R) →
  R →
  Set
SeriesHasSum reals term limit =
  ConvergesTo reals
    (λ n → sumFirst reals n term)
    limit

sineTerm :
  {R : Set} →
  CompleteOrderedField R →
  R →
  Nat →
  R
sineTerm reals x n =
  multiply reals
    (alternatingUnit reals n)
    (divide reals
      (power reals x (suc (2 * n)))
      (fromNat reals (factorial (suc (2 * n)))))

cosineTerm :
  {R : Set} →
  CompleteOrderedField R →
  R →
  Nat →
  R
cosineTerm reals x n =
  multiply reals
    (alternatingUnit reals n)
    (divide reals
      (power reals x (2 * n))
      (fromNat reals (factorial (2 * n))))

record CanonicalRealAnalysis (R : Set) : Set₁ where
  field
    algebra : CompleteOrderedField R
    squareRoot absoluteValue : R → R
    sine cosine : R → R
    pi : R

    square-root-nonnegative :
      (x : R) → lessOrEqual algebra (zeroR algebra) (squareRoot x)
    square-root-square :
      (x : R) →
      lessOrEqual algebra (zeroR algebra) x →
      multiply algebra (squareRoot x) (squareRoot x) ≡ x
    square-root-nonpositive :
      (x : R) →
      lessOrEqual algebra x (zeroR algebra) →
      squareRoot x ≡ zeroR algebra
    square-root-unique :
      (x y : R) →
      lessOrEqual algebra (zeroR algebra) y →
      multiply algebra y y ≡ x →
      squareRoot x ≡ y

    absolute-value-nonnegative :
      (x : R) → lessOrEqual algebra (zeroR algebra) (absoluteValue x)
    absolute-value-of-nonnegative :
      (x : R) →
      lessOrEqual algebra (zeroR algebra) x →
      absoluteValue x ≡ x
    absolute-value-of-nonpositive :
      (x : R) →
      lessOrEqual algebra x (zeroR algebra) →
      absoluteValue x ≡ negate algebra x

    sine-power-series :
      (x : R) →
      SeriesHasSum algebra (sineTerm algebra x) (sine x)
    cosine-power-series :
      (x : R) →
      SeriesHasSum algebra (cosineTerm algebra x) (cosine x)

    pi-positive :
      StrictLess algebra (zeroR algebra) pi
    sine-pi :
      sine pi ≡ zeroR algebra
    pi-least-positive-zero :
      (x : R) →
      StrictLess algebra (zeroR algebra) x →
      sine x ≡ zeroR algebra →
      lessOrEqual algebra pi x

radicalDifference :
  {R : Set} →
  CanonicalRealAnalysis R →
  R →
  R
radicalDifference reals x =
  subtract algebra
    (squareRoot
      (add algebra (oneR algebra)
        (sine (multiply algebra (fromNat algebra 2) x))))
    (squareRoot
      (subtract algebra (oneR algebra)
        (sine (multiply algebra (fromNat algebra 2) x))))
  where
    open CanonicalRealAnalysis reals

Claim :
  {R : Set} →
  CanonicalRealAnalysis R →
  R →
  Set
Claim reals x =
  lessOrEqual algebra (zeroR algebra) x →
  lessOrEqual algebra x
    (multiply algebra (fromNat algebra 2) pi) →
  lessOrEqual algebra
    (multiply algebra (fromNat algebra 2) (cosine x))
    (absoluteValue (radicalDifference reals x)) →
  lessOrEqual algebra
    (absoluteValue (radicalDifference reals x))
    (squareRoot (fromNat algebra 2)) →
  lessOrEqual algebra
    (divide algebra pi (fromNat algebra 4))
    x
  ∧
  lessOrEqual algebra x
    (divide algebra
      (multiply algebra (fromNat algebra 7) pi)
      (fromNat algebra 4))
  where
    open CanonicalRealAnalysis reals

imo-1965-p1 : Set₁
imo-1965-p1 =
  (R : Set) →
  (reals : CanonicalRealAnalysis R) →
  (x : R) →
  Claim reals x
