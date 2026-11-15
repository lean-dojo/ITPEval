-- Statement-only formalization of miniF2F test problem mathd_algebra_487: the
-- Euclidean distance between the two distinct real points determined by
-- x + x^2 = 1. This file contains no proof.

module mathd-algebra-487 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _≠_
infixr 3 _∨_
infixr 2 _∧_

data ⊥ : Set where

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

record _∧_ (A B : Set) : Set where
  constructor _,_
  field
    first  : A
    second : B

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

record RealSqrtStructure (R : Set) : Set₁ where
  field
    zeroR oneR : R
    add multiply : R → R → R
    negate inverse squareRoot : R → R
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
    fromNat-injective :
      (m n : Nat) → fromNat m ≡ fromNat n → m ≡ n
    fromNat-nonnegative :
      (n : Nat) → lessOrEqual zeroR (fromNat n)

    square-root-nonnegative :
      (x : R) → lessOrEqual zeroR (squareRoot x)
    square-root-square :
      (x : R) →
      lessOrEqual zeroR x →
      multiply (squareRoot x) (squareRoot x) ≡ x
    square-root-nonpositive :
      (x : R) →
      lessOrEqual x zeroR →
      squareRoot x ≡ zeroR
    square-root-unique :
      (x y : R) →
      lessOrEqual zeroR y →
      multiply y y ≡ x →
      squareRoot x ≡ y

-- Complete Archimedean ordered fields characterize the standard real-number
-- domain; the square-root laws select the usual principal square root.
record StandardRealSqrt (R : Set) : Set₁ where
  field
    algebra : RealSqrtStructure R

    archimedean :
      (x : R) →
      Exists Nat λ n →
        RealSqrtStructure.lessOrEqual algebra
          x
          (RealSqrtStructure.fromNat algebra n)

    least-upper-bound :
      (subset : R → Set) →
      Exists R subset →
      Exists R
        (λ upper →
          (x : R) →
          subset x →
          RealSqrtStructure.lessOrEqual algebra x upper) →
      Exists R λ supremum →
        ((x : R) →
          subset x →
          RealSqrtStructure.lessOrEqual algebra x supremum) ∧
        ((upper : R) →
          ((x : R) →
            subset x →
            RealSqrtStructure.lessOrEqual algebra x upper) →
          RealSqrtStructure.lessOrEqual algebra supremum upper)

subtract :
  {R : Set} →
  RealSqrtStructure R →
  R →
  R →
  R
subtract reals x y =
  RealSqrtStructure.add reals x
    (RealSqrtStructure.negate reals y)

square :
  {R : Set} →
  RealSqrtStructure R →
  R →
  R
square reals x =
  RealSqrtStructure.multiply reals x x

distanceSquared :
  {R : Set} →
  RealSqrtStructure R →
  R →
  R →
  R →
  R →
  R
distanceSquared reals a b c d =
  RealSqrtStructure.add reals
    (square reals (subtract reals a c))
    (square reals (subtract reals b d))

module Statement {R : Set} (standard : StandardRealSqrt R) where
  reals : RealSqrtStructure R
  reals = StandardRealSqrt.algebra standard

  proposition : Set
  proposition =
    (a b c d : R) →
    b ≡ square reals a →
    RealSqrtStructure.add reals a b ≡
      RealSqrtStructure.fromNat reals 1 →
    d ≡ square reals c →
    RealSqrtStructure.add reals c d ≡
      RealSqrtStructure.fromNat reals 1 →
    a ≠ c →
    RealSqrtStructure.squareRoot reals
      (distanceSquared reals a b c d)
    ≡
    RealSqrtStructure.squareRoot reals
      (RealSqrtStructure.fromNat reals 10)

mathd-algebra-487 : Set₁
mathd-algebra-487 =
  (R : Set) →
  (standard : StandardRealSqrt R) →
  Statement.proposition standard
