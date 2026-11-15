-- Statement-only formalization of miniF2F test problem imo_1969_p2: two zeros of a
-- positive-length finite weighted cosine sum differ by an integer multiple of pi. This file
-- contains no proof.

module imo-1969-p2 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≠_
infixr 2 _∨_

data ⊥ : Set where

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data Positive : Nat → Set where
  positive : (n : Nat) → Positive (suc n)

record OrderedField (R : Set) : Set₁ where
  field
    zeroR oneR : R
    add multiply : R → R → R
    negate inverse : R → R
    lessThan : R → R → Set
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

    order-irreflexive :
      (x : R) → lessThan x x → ⊥
    order-transitive :
      (x y z : R) →
      lessThan x y →
      lessThan y z →
      lessThan x z
    order-trichotomy :
      (x y : R) →
      lessThan x y ∨ (x ≡ y ∨ lessThan y x)
    add-order :
      (x y z : R) →
      lessThan x y →
      lessThan (add z x) (add z y)
    multiply-positive :
      (x y : R) →
      lessThan zeroR x →
      lessThan zeroR y →
      lessThan zeroR (multiply x y)
    zero-less-one :
      lessThan zeroR oneR

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
      Exists Nat (λ n → lessThan x (fromNat n))

subtract :
  {R : Set} →
  OrderedField R →
  R →
  R →
  R
subtract algebra x y =
  OrderedField.add algebra
    x
    (OrderedField.negate algebra y)

divide :
  {R : Set} →
  OrderedField R →
  R →
  R →
  R
divide algebra x y =
  OrderedField.multiply algebra
    x
    (OrderedField.inverse algebra y)

twice :
  {R : Set} →
  OrderedField R →
  R →
  R
twice algebra x =
  OrderedField.multiply algebra
    (OrderedField.fromNat algebra 2)
    x

record StandardRealTrigonometry (R : Set) : Set₁ where
  field
    algebra : OrderedField R
    pi : R
    sine cosine : R → R

    pi-lower-bound :
      OrderedField.lessThan algebra
        (OrderedField.fromNat algebra 3)
        pi
    pi-upper-bound :
      OrderedField.lessThan algebra
        pi
        (OrderedField.fromNat algebra 4)

    sine-zero :
      sine (OrderedField.zeroR algebra) ≡
      OrderedField.zeroR algebra
    cosine-zero :
      cosine (OrderedField.zeroR algebra) ≡
      OrderedField.oneR algebra
    sine-half-pi :
      sine (divide algebra pi (OrderedField.fromNat algebra 2)) ≡
      OrderedField.oneR algebra
    cosine-half-pi :
      cosine (divide algebra pi (OrderedField.fromNat algebra 2)) ≡
      OrderedField.zeroR algebra
    sine-pi :
      sine pi ≡ OrderedField.zeroR algebra
    cosine-pi :
      cosine pi ≡
      OrderedField.negate algebra
        (OrderedField.oneR algebra)

    sine-positive-first-half-period :
      (x : R) →
      OrderedField.lessThan algebra
        (OrderedField.zeroR algebra)
        x →
      OrderedField.lessThan algebra x pi →
      OrderedField.lessThan algebra
        (OrderedField.zeroR algebra)
        (sine x)

    sine-addition :
      (x y : R) →
      sine (OrderedField.add algebra x y) ≡
      OrderedField.add algebra
        (OrderedField.multiply algebra (sine x) (cosine y))
        (OrderedField.multiply algebra (cosine x) (sine y))
    cosine-addition :
      (x y : R) →
      cosine (OrderedField.add algebra x y) ≡
      subtract algebra
        (OrderedField.multiply algebra (cosine x) (cosine y))
        (OrderedField.multiply algebra (sine x) (sine y))
    sine-negate :
      (x : R) →
      sine (OrderedField.negate algebra x) ≡
      OrderedField.negate algebra (sine x)
    cosine-negate :
      (x : R) →
      cosine (OrderedField.negate algebra x) ≡ cosine x

    pythagorean :
      (x : R) →
      OrderedField.add algebra
        (OrderedField.multiply algebra (sine x) (sine x))
        (OrderedField.multiply algebra (cosine x) (cosine x))
        ≡ OrderedField.oneR algebra

    sine-periodic :
      (x : R) →
      sine (OrderedField.add algebra x (twice algebra pi)) ≡ sine x
    cosine-periodic :
      (x : R) →
      cosine (OrderedField.add algebra x (twice algebra pi)) ≡ cosine x

fromInt :
  {R : Set} →
  OrderedField R →
  Int →
  R
fromInt algebra (pos n) =
  OrderedField.fromNat algebra n
fromInt algebra (negsuc n) =
  OrderedField.negate algebra
    (OrderedField.fromNat algebra (suc n))

naturalPower :
  {R : Set} →
  OrderedField R →
  R →
  Nat →
  R
naturalPower algebra x zero =
  OrderedField.oneR algebra
naturalPower algebra x (suc n) =
  OrderedField.multiply algebra
    (naturalPower algebra x n)
    x

sumInitial :
  {R : Set} →
  OrderedField R →
  Nat →
  (Nat → R) →
  R
sumInitial algebra zero term =
  OrderedField.zeroR algebra
sumInitial algebra (suc n) term =
  OrderedField.add algebra
    (sumInitial algebra n term)
    (term n)

weightedCosineSum :
  {R : Set} →
  StandardRealTrigonometry R →
  (Nat → R) →
  Nat →
  R →
  R
weightedCosineSum reals a k x =
  sumInitial algebra k
    (λ i →
      divide algebra
        (cosine (OrderedField.add algebra (a i) x))
        (naturalPower algebra
          (OrderedField.fromNat algebra 2)
          i))
  where
    algebra = StandardRealTrigonometry.algebra reals
    cosine = StandardRealTrigonometry.cosine reals

imo-1969-p2 : Set₁
imo-1969-p2 =
  (R : Set) →
  (reals : StandardRealTrigonometry R) →
  (m n : R) →
  (k : Nat) →
  (a : Nat → R) →
  (y : R → R) →
  Positive k →
  ((x : R) → y x ≡ weightedCosineSum reals a k x) →
  y m ≡
    OrderedField.zeroR
      (StandardRealTrigonometry.algebra reals) →
  y n ≡
    OrderedField.zeroR
      (StandardRealTrigonometry.algebra reals) →
  Exists Int
    (λ t →
      subtract
        (StandardRealTrigonometry.algebra reals)
        m
        n
      ≡
      OrderedField.multiply
        (StandardRealTrigonometry.algebra reals)
        (fromInt
          (StandardRealTrigonometry.algebra reals)
          t)
        (StandardRealTrigonometry.pi reals))
