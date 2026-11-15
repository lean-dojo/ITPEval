-- Statement-only formalization of miniF2F valid problem amc12a_2021_p7:
-- the quadratic inequality 1 <= (x * y - 1)^2 + (x + y)^2 for all real x and y.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module amc12a-2021-p7 where

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

-- Completeness and the Archimedean property pin the carrier down to the
-- standard real numbers quantified by the source theorem.
record RealStructure (R : Set) : Set₁ where
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
    fromNat-injective :
      (m n : Nat) → fromNat m ≡ fromNat n → m ≡ n
    fromNat-nonnegative :
      (n : Nat) → lessOrEqual zeroR (fromNat n)

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

square : {R : Set} → RealStructure R → R → R
square reals x =
  RealStructure.multiply reals x x

subtract : {R : Set} → RealStructure R → R → R → R
subtract reals x y =
  RealStructure.add reals x (RealStructure.negate reals y)

amc12a-2021-p7 : Set₁
amc12a-2021-p7 =
  (R : Set) →
  (reals : RealStructure R) →
  (x y : R) →
  RealStructure.lessOrEqual reals
    (RealStructure.oneR reals)
    (RealStructure.add reals
      (square reals
        (subtract reals
          (RealStructure.multiply reals x y)
          (RealStructure.oneR reals)))
      (square reals
        (RealStructure.add reals x y)))
