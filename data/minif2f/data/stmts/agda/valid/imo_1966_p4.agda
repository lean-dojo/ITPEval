-- Statement-only formalization of miniF2F valid problem imo_1966_p4: a finite cosecant-sum
-- identity for dyadically scaled real angles. This file contains no proof.

module imo-1966-p4 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≠_
infixr 4 _∧_
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

data Positive : Nat → Set where
  positive : {n : Nat} → Positive (suc n)

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

    least-upper-bound :
      (subset : R → Set) →
      Exists R subset →
      Exists R
        (λ upper →
          (x : R) →
          subset x →
          lessThan x upper ∨ x ≡ upper) →
      Exists R
        (λ supremum →
          ((x : R) →
            subset x →
            lessThan x supremum ∨ x ≡ supremum) ∧
          ((upper : R) →
            ((x : R) →
              subset x →
              lessThan x upper ∨ x ≡ upper) →
            lessThan supremum upper ∨ supremum ≡ upper))

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

differenceQuotient :
  {R : Set} →
  OrderedField R →
  (R → R) →
  R →
  R →
  R
differenceQuotient algebra f x y =
  divide algebra
    (subtract algebra (f y) (f x))
    (subtract algebra y x)

DerivativeAt :
  {R : Set} →
  OrderedField R →
  (R → R) →
  R →
  R →
  Set
DerivativeAt {R} algebra f x derivative =
  (epsilon : R) →
  OrderedField.lessThan algebra
    (OrderedField.zeroR algebra)
    epsilon →
  Exists R
    (λ delta →
      OrderedField.lessThan algebra
        (OrderedField.zeroR algebra)
        delta ∧
      ((y : R) →
        OrderedField.lessThan algebra
          (subtract algebra x delta)
          y →
        OrderedField.lessThan algebra
          y
          (OrderedField.add algebra x delta) →
        y ≠ x →
        OrderedField.lessThan algebra
          (subtract algebra derivative epsilon)
          (differenceQuotient algebra f x y) ∧
        OrderedField.lessThan algebra
          (differenceQuotient algebra f x y)
          (OrderedField.add algebra derivative epsilon)))

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

natPower : Nat → Nat → Nat
natPower base zero = 1
natPower base (suc exponent) =
  base * natPower base exponent

twoPower :
  {R : Set} →
  OrderedField R →
  Nat →
  R
twoPower algebra exponent =
  OrderedField.fromNat algebra (natPower 2 exponent)

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

    sine-derivative :
      (x : R) →
      DerivativeAt algebra sine x (cosine x)
    cosine-derivative :
      (x : R) →
      DerivativeAt algebra cosine x
        (OrderedField.negate algebra (sine x))

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

tangent :
  {R : Set} →
  StandardRealTrigonometry R →
  R →
  R
tangent reals x =
  divide algebra (sine x) (cosine x)
  where
    algebra = StandardRealTrigonometry.algebra reals
    sine = StandardRealTrigonometry.sine reals
    cosine = StandardRealTrigonometry.cosine reals

cotangent :
  {R : Set} →
  StandardRealTrigonometry R →
  R →
  R
cotangent reals x =
  divide algebra
    (OrderedField.oneR algebra)
    (tangent reals x)
  where
    algebra = StandardRealTrigonometry.algebra reals

sumFromOne :
  {R : Set} →
  OrderedField R →
  Nat →
  (Nat → R) →
  R
sumFromOne algebra zero term =
  OrderedField.zeroR algebra
sumFromOne algebra (suc n) term =
  OrderedField.add algebra
    (sumFromOne algebra n term)
    (term (suc n))

cosecantSum :
  {R : Set} →
  StandardRealTrigonometry R →
  Nat →
  R →
  R
cosecantSum reals n x =
  sumFromOne algebra n
    (λ k →
      divide algebra
        (OrderedField.oneR algebra)
        (sine
          (OrderedField.multiply algebra
            (twoPower algebra k)
            x)))
  where
    algebra = StandardRealTrigonometry.algebra reals
    sine = StandardRealTrigonometry.sine reals

ExcludedAngles :
  {R : Set} →
  StandardRealTrigonometry R →
  R →
  Set
ExcludedAngles reals x =
  (k : Nat) →
  Positive k →
  (m : Int) →
  x ≠
    divide algebra
      (OrderedField.multiply algebra
        (fromInt algebra m)
        pi)
      (twoPower algebra k)
  where
    algebra = StandardRealTrigonometry.algebra reals
    pi = StandardRealTrigonometry.pi reals

Claim :
  {R : Set} →
  StandardRealTrigonometry R →
  Nat →
  R →
  Set
Claim reals n x =
  cosecantSum reals n x ≡
    subtract algebra
      (cotangent reals x)
      (cotangent reals
        (OrderedField.multiply algebra
          (twoPower algebra n)
          x))
  where
    algebra = StandardRealTrigonometry.algebra reals

imo-1966-p4 : Set₁
imo-1966-p4 =
  (R : Set) →
  (reals : StandardRealTrigonometry R) →
  (n : Nat) →
  (x : R) →
  ExcludedAngles reals x →
  Positive n →
  Claim reals n x
