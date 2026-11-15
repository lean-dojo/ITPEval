-- Statement-only formalization of miniF2F valid problem mathd_algebra_480: a piecewise
-- real-valued function has value 2 at pi. This file contains no proof.

module mathd-algebra-480 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _≠_
infixr 3 _∨_

data ⊥ : Set where

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

lessOrEqual :
  {R : Set} →
  (R → R → Set) →
  R →
  R →
  Set
lessOrEqual lessThan x y = lessThan x y ∨ x ≡ y

record RealSqrtOrderedField (R : Set) : Set₁ where
  field
    zeroR oneR : R
    add multiply : R → R → R
    negate inverse squareRoot : R → R
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
    fromNat-injective :
      (m n : Nat) → fromNat m ≡ fromNat n → m ≡ n
    fromNat-positive :
      (n : Nat) → lessThan zeroR (fromNat (suc n))

    square-root-nonnegative :
      (x : R) →
      lessOrEqual lessThan zeroR (squareRoot x)
    square-root-square :
      (x : R) →
      lessOrEqual lessThan zeroR x →
      multiply (squareRoot x) (squareRoot x) ≡ x
    square-root-nonpositive :
      (x : R) →
      lessOrEqual lessThan x zeroR →
      squareRoot x ≡ zeroR
    square-root-unique :
      (x y : R) →
      lessOrEqual lessThan zeroR y →
      multiply y y ≡ x →
      squareRoot x ≡ y

record StandardRealSqrtStructure (R : Set) : Set₁ where
  field
    algebra : RealSqrtOrderedField R
    pi : R

    pi-lower-bound :
      RealSqrtOrderedField.lessThan algebra
        (RealSqrtOrderedField.fromNat algebra 3)
        pi
    pi-upper-bound :
      RealSqrtOrderedField.lessThan algebra
        pi
        (RealSqrtOrderedField.fromNat algebra 4)

module Statement {R : Set} (reals : StandardRealSqrtStructure R) where
  open StandardRealSqrtStructure reals
  open RealSqrtOrderedField algebra

  infix 4 _<_ _≤_
  infixl 6 _−_
  infixl 7 _*_

  _<_ : R → R → Set
  _<_ = lessThan

  _≤_ : R → R → Set
  x ≤ y = lessOrEqual lessThan x y

  _−_ : R → R → R
  x − y = add x (negate y)

  _*_ : R → R → R
  _*_ = multiply

  proposition : Set
  proposition =
    (f : R → R) →
    ((x : R) →
      x < zeroR →
      f x ≡ negate (x * x) − fromNat 1) →
    ((x : R) →
      zeroR ≤ x →
      x < fromNat 4 →
      f x ≡ fromNat 2) →
    ((x : R) →
      fromNat 4 ≤ x →
      f x ≡ squareRoot x) →
    f pi ≡ fromNat 2

mathd-algebra-480 : Set₁
mathd-algebra-480 =
  (R : Set) →
  (reals : StandardRealSqrtStructure R) →
  Statement.proposition reals
