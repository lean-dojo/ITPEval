-- Statement-only formalization of miniF2F valid problem amc12a_2003_p25:
-- if b is positive, f(x) = sqrt(a*x^2 + b*x), and the natural square-root
-- domain equals its image under f, then a is 0 or -4. This file contains no proof.

{-# OPTIONS --safe #-}

module amc12a-2003-p25 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _≠_
infixr 4 _∧_
infixr 3 _∨_

data ⊥ : Set where

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

record _∧_ (A B : Set) : Set where
  constructor _,_
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

record RealStructure (R : Set) : Set₁ where
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

-- Archimedean completeness characterizes the standard real-number domain.
record StandardReal (R : Set) : Set₁ where
  field
    arithmetic : RealStructure R

    archimedean :
      (x : R) →
      Exists Nat λ n →
        RealStructure.lessOrEqual arithmetic
          x
          (RealStructure.fromNat arithmetic n)

    least-upper-bound :
      (subset : R → Set) →
      Exists R subset →
      Exists R
        (λ upper →
          (x : R) →
          subset x →
          RealStructure.lessOrEqual arithmetic x upper) →
      Exists R λ supremum →
        ((x : R) →
          subset x →
          RealStructure.lessOrEqual arithmetic x supremum) ∧
        ((upper : R) →
          ((x : R) →
            subset x →
            RealStructure.lessOrEqual arithmetic x upper) →
          RealStructure.lessOrEqual arithmetic supremum upper)

square : {R : Set} → RealStructure R → R → R
square reals x =
  RealStructure.multiply reals x x

strictlyPositive : {R : Set} → RealStructure R → R → Set
strictlyPositive reals x =
  (RealStructure.lessOrEqual reals
    (RealStructure.zeroR reals) x) ∧
  (RealStructure.zeroR reals ≠ x)

Image :
  {A B : Set} →
  (A → B) →
  (A → Set) →
  B →
  Set
Image f P y =
  Exists _ λ x → P x ∧ (f x ≡ y)

SameSet :
  {A : Set} →
  (A → Set) →
  (A → Set) →
  Set
SameSet {A} P Q =
  (x : A) → (P x → Q x) ∧ (Q x → P x)

radicand :
  {R : Set} →
  RealStructure R →
  R →
  R →
  R →
  R
radicand reals a b x =
  RealStructure.add reals
    (RealStructure.multiply reals a (square reals x))
    (RealStructure.multiply reals b x)

-- The domain of the mathematical square root is determined by its radicand.
-- Using 0 <= f(x) here would make the predicate true for every x because the
-- formal square-root operation is total and nonnegative.
NaturalDomain :
  {R : Set} →
  RealStructure R →
  R →
  R →
  R →
  Set
NaturalDomain reals a b x =
  RealStructure.lessOrEqual reals
    (RealStructure.zeroR reals)
    (radicand reals a b x)

module Statement {R : Set} (standard : StandardReal R) where
  reals : RealStructure R
  reals = StandardReal.arithmetic standard

  proposition : Set
  proposition =
    (a b : R) →
    (f : R → R) →
    strictlyPositive reals b →
    ((x : R) →
      f x ≡
      RealStructure.squareRoot reals
        (radicand reals a b x)) →
    SameSet
      (NaturalDomain reals a b)
      (Image f (NaturalDomain reals a b)) →
    (a ≡ RealStructure.zeroR reals) ∨
    (a ≡
      RealStructure.negate reals
        (RealStructure.fromNat reals 4))

amc12a-2003-p25 : Set₁
amc12a-2003-p25 =
  (R : Set) →
  (standard : StandardReal R) →
  Statement.proposition standard
