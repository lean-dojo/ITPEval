-- Statement-only formalization of miniF2F valid problem mathd_algebra_116:
-- if x = (13 - sqrt 131) / 4 and 2 * x^2 - 13 * x + k = 0 over the real
-- numbers, then k = 19 / 4. This file contains no proof.

module mathd-algebra-116 where

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

subtract :
  {R : Set} →
  RealSqrtStructure R →
  R →
  R →
  R
subtract reals x y =
  RealSqrtStructure.add reals x
    (RealSqrtStructure.negate reals y)

divide :
  {R : Set} →
  RealSqrtStructure R →
  R →
  R →
  R
divide reals x y =
  RealSqrtStructure.multiply reals x
    (RealSqrtStructure.inverse reals y)

square :
  {R : Set} →
  RealSqrtStructure R →
  R →
  R
square reals x =
  RealSqrtStructure.multiply reals x x

mathd-algebra-116 : Set₁
mathd-algebra-116 =
  (R : Set) →
  (reals : RealSqrtStructure R) →
  (k x : R) →
  x ≡
    divide reals
      (subtract reals
        (RealSqrtStructure.fromNat reals 13)
        (RealSqrtStructure.squareRoot reals
          (RealSqrtStructure.fromNat reals 131)))
      (RealSqrtStructure.fromNat reals 4) →
  RealSqrtStructure.add reals
    (subtract reals
      (RealSqrtStructure.multiply reals
        (RealSqrtStructure.fromNat reals 2)
        (square reals x))
      (RealSqrtStructure.multiply reals
        (RealSqrtStructure.fromNat reals 13)
        x))
    k
    ≡ RealSqrtStructure.zeroR reals →
  k ≡
    divide reals
      (RealSqrtStructure.fromNat reals 19)
      (RealSqrtStructure.fromNat reals 4)
