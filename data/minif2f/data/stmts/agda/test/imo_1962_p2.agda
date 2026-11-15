-- Statement-only formalization of miniF2F test problem imo_1962_p2. This file contains no
-- proof.

module imo-1962-p2 where

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

subtract : {R : Set} → RealStructure R → R → R → R
subtract reals x y =
  RealStructure.add reals x (RealStructure.negate reals y)

divide : {R : Set} → RealStructure R → R → R → R
divide reals x y =
  RealStructure.multiply reals x (RealStructure.inverse reals y)

strictlyLess : {R : Set} → RealStructure R → R → R → Set
strictlyLess reals x y =
  (RealStructure.lessOrEqual reals x y) ∧ (x ≠ y)

firstRadicand : {R : Set} → RealStructure R → R → R
firstRadicand reals x =
  subtract reals (RealStructure.fromNat reals 3) x

secondRadicand : {R : Set} → RealStructure R → R → R
secondRadicand reals x =
  RealStructure.add reals x (RealStructure.oneR reals)

radicalDifference : {R : Set} → RealStructure R → R → R
radicalDifference reals x =
  subtract reals
    (RealStructure.squareRoot reals (firstRadicand reals x))
    (RealStructure.squareRoot reals (secondRadicand reals x))

upperBound : {R : Set} → RealStructure R → R
upperBound reals =
  subtract reals
    (RealStructure.oneR reals)
    (divide reals
      (RealStructure.squareRoot reals
        (RealStructure.fromNat reals 31))
      (RealStructure.fromNat reals 8))

imo-1962-p2 : Set₁
imo-1962-p2 =
  (R : Set) →
  (reals : RealStructure R) →
  (x : R) →
  RealStructure.lessOrEqual reals
    (RealStructure.zeroR reals)
    (firstRadicand reals x) →
  RealStructure.lessOrEqual reals
    (RealStructure.zeroR reals)
    (secondRadicand reals x) →
  strictlyLess reals
    (divide reals
      (RealStructure.oneR reals)
      (RealStructure.fromNat reals 2))
    (radicalDifference reals x) →
  RealStructure.lessOrEqual reals
    (RealStructure.negate reals (RealStructure.oneR reals))
    x ∧
  strictlyLess reals x (upperBound reals)
