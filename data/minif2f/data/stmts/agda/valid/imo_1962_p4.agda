-- Statement-only formalization of miniF2F valid problem imo_1962_p4. This file contains no
-- proof.

module imo-1962-p4 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≠_
infixr 2 _∨_
infix 2 _↔_

data ⊥ : Set where

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

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

square :
  {R : Set} →
  OrderedField R →
  R →
  R
square algebra x =
  OrderedField.multiply algebra x x

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
      sine
        (OrderedField.add algebra x
          (OrderedField.multiply algebra
            (OrderedField.fromNat algebra 2)
            pi))
      ≡ sine x
    cosine-periodic :
      (x : R) →
      cosine
        (OrderedField.add algebra x
          (OrderedField.multiply algebra
            (OrderedField.fromNat algebra 2)
            pi))
      ≡ cosine x

Equation :
  {R : Set} →
  StandardRealTrigonometry R →
  R →
  Set
Equation reals x =
  OrderedField.add algebra
    (OrderedField.add algebra
      (square algebra (cosine x))
      (square algebra
        (cosine
          (OrderedField.multiply algebra
            (OrderedField.fromNat algebra 2)
            x))))
    (square algebra
      (cosine
        (OrderedField.multiply algebra
          (OrderedField.fromNat algebra 3)
          x)))
  ≡ OrderedField.oneR algebra
  where
    algebra = StandardRealTrigonometry.algebra reals
    cosine = StandardRealTrigonometry.cosine reals

integerMultiple :
  {R : Set} →
  OrderedField R →
  Int →
  R →
  R
integerMultiple algebra m x =
  OrderedField.multiply algebra
    (fromInt algebra m)
    x

rationalMultiple :
  {R : Set} →
  OrderedField R →
  R →
  Nat →
  R
rationalMultiple algebra x denominator =
  divide algebra x (OrderedField.fromNat algebra denominator)

Solution :
  {R : Set} →
  StandardRealTrigonometry R →
  R →
  Set
Solution reals x =
  Exists Int
    (λ m →
      x ≡
      OrderedField.add algebra
        (rationalMultiple algebra pi 2)
        (integerMultiple algebra m pi))
  ∨
  Exists Int
    (λ m →
      x ≡
      OrderedField.add algebra
        (rationalMultiple algebra pi 4)
        (rationalMultiple algebra
          (integerMultiple algebra m pi)
          2))
  ∨
  Exists Int
    (λ m →
      x ≡
      OrderedField.add algebra
        (rationalMultiple algebra pi 6)
        (rationalMultiple algebra
          (integerMultiple algebra m pi)
          3))
  where
    algebra = StandardRealTrigonometry.algebra reals
    pi = StandardRealTrigonometry.pi reals

imo-1962-p4 : Set₁
imo-1962-p4 =
  (R : Set) →
  (reals : StandardRealTrigonometry R) →
  (x : R) →
  Equation reals x ↔ Solution reals x
