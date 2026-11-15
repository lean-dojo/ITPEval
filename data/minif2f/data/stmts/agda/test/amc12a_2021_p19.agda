-- Statement-only formalization of miniF2F test problem amc12a_2021_p19. This file contains no
-- proof.

{-# OPTIONS --safe #-}

module amc12a-2021-p19 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≠_ _∈_
infixr 3 _∧_
infixr 2 _∨_
infix 2 _↔_

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

record _↔_ (A B : Set) : Set where
  field
    forward  : A → B
    backward : B → A

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _∈_ {A : Set} (x : A) : List A → Set where
  here :
    {y : A} {xs : List A} →
    x ≡ y →
    x ∈ (y ∷ xs)
  there :
    {y : A} {xs : List A} →
    x ∈ xs →
    x ∈ (y ∷ xs)

data NoDuplicates {A : Set} : List A → Set where
  no-duplicates-empty :
    NoDuplicates []
  no-duplicates-cons :
    {x : A} {xs : List A} →
    (x ∈ xs → ⊥) →
    NoDuplicates xs →
    NoDuplicates (x ∷ xs)

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

-- A complete Archimedean ordered field presents the standard real numbers.
record OrderedField (R : Set) : Set₁ where
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
      Exists Nat λ n →
        lessOrEqual x (fromNat n)

    least-upper-bound :
      (subset : R → Set) →
      Exists R subset →
      Exists R
        (λ upper →
          (x : R) →
          subset x →
          lessOrEqual x upper) →
      Exists R λ supremum →
        ((x : R) →
          subset x →
          lessOrEqual x supremum) ∧
        ((upper : R) →
          ((x : R) →
            subset x →
            lessOrEqual x upper) →
          lessOrEqual supremum upper)

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

half :
  {R : Set} →
  OrderedField R →
  R →
  R
half algebra x =
  divide algebra
    x
    (OrderedField.fromNat algebra 2)

twice :
  {R : Set} →
  OrderedField R →
  R →
  R
twice algebra x =
  OrderedField.multiply algebra
    (OrderedField.fromNat algebra 2)
    x

strictlyLess :
  {R : Set} →
  OrderedField R →
  R →
  R →
  Set
strictlyLess algebra x y =
  OrderedField.lessOrEqual algebra x y ∧ x ≠ y

record StandardRealTrigonometry (R : Set) : Set₁ where
  field
    algebra : OrderedField R
    pi : R
    sine cosine : R → R

    pi-lower-bound :
      OrderedField.lessOrEqual algebra
        (OrderedField.fromNat algebra 3)
        pi
    pi-upper-bound :
      OrderedField.lessOrEqual algebra
        pi
        (OrderedField.fromNat algebra 4)

    sine-zero :
      sine (OrderedField.zeroR algebra) ≡
      OrderedField.zeroR algebra
    cosine-zero :
      cosine (OrderedField.zeroR algebra) ≡
      OrderedField.oneR algebra
    sine-half-pi :
      sine (half algebra pi) ≡
      OrderedField.oneR algebra
    cosine-half-pi :
      cosine (half algebra pi) ≡
      OrderedField.zeroR algebra
    sine-pi :
      sine pi ≡ OrderedField.zeroR algebra
    cosine-pi :
      cosine pi ≡
      OrderedField.negate algebra
        (OrderedField.oneR algebra)

    sine-positive-first-half-period :
      (x : R) →
      strictlyLess algebra
        (OrderedField.zeroR algebra)
        x →
      strictlyLess algebra x pi →
      strictlyLess algebra
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
      OrderedField.add algebra
        (OrderedField.multiply algebra (cosine x) (cosine y))
        (OrderedField.negate algebra
          (OrderedField.multiply algebra (sine x) (sine y)))
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

Solution :
  {R : Set} →
  StandardRealTrigonometry R →
  R →
  Set
Solution reals x =
  OrderedField.lessOrEqual algebra
    (OrderedField.zeroR algebra)
    x
  ∧
  OrderedField.lessOrEqual algebra
    x
    (StandardRealTrigonometry.pi reals)
  ∧
  StandardRealTrigonometry.sine reals
    (OrderedField.multiply algebra
      (half algebra (StandardRealTrigonometry.pi reals))
      (StandardRealTrigonometry.cosine reals x))
  ≡
  StandardRealTrigonometry.cosine reals
    (OrderedField.multiply algebra
      (half algebra (StandardRealTrigonometry.pi reals))
      (StandardRealTrigonometry.sine reals x))
  where
    algebra = StandardRealTrigonometry.algebra reals

amc12a-2021-p19 : Set₁
amc12a-2021-p19 =
  (R : Set) →
  (reals : StandardRealTrigonometry R) →
  (solutions : List R) →
  ((x : R) → (x ∈ solutions) ↔ Solution reals x) →
  NoDuplicates solutions →
  length solutions ≡ 2
