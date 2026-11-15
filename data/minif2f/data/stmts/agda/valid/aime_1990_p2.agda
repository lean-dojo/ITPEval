-- Statement-only formalization of miniF2F valid problem aime_1990_p2. This file contains no
-- proof.

module aime-1990-p2 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≠_
infixr 3 _∨_

data ⊥ : Set where

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

record RealPowerStructure (R : Set) : Set₁ where
  field
    zeroR oneR : R
    add multiply : R → R → R
    negate inverse squareRoot : R → R
    lessThan : R → R → Set
    fromNat : Nat → R
    realPower : R → R → R

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
    zero-less-than-one :
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
    fromNat-positive :
      (n : Nat) → lessThan zeroR (fromNat (suc n))

    square-root-nonnegative :
      (x : R) →
      lessThan zeroR (squareRoot x) ∨ squareRoot x ≡ zeroR
    square-root-square :
      (x : R) →
      (lessThan zeroR x ∨ x ≡ zeroR) →
      multiply (squareRoot x) (squareRoot x) ≡ x
    square-root-nonpositive :
      (x : R) →
      (lessThan x zeroR ∨ x ≡ zeroR) →
      squareRoot x ≡ zeroR
    square-root-unique :
      (x y : R) →
      (lessThan zeroR y ∨ y ≡ zeroR) →
      multiply y y ≡ x →
      squareRoot x ≡ y

    real-power-positive :
      (x y : R) →
      lessThan zeroR x →
      lessThan zeroR (realPower x y)
    real-power-zero :
      (x : R) →
      lessThan zeroR x →
      realPower x zeroR ≡ oneR
    real-power-one :
      (x : R) →
      lessThan zeroR x →
      realPower x oneR ≡ x
    real-power-add :
      (x y z : R) →
      lessThan zeroR x →
      realPower x (add y z) ≡
      multiply (realPower x y) (realPower x z)
    real-power-multiply :
      (x y z : R) →
      lessThan zeroR x →
      realPower (realPower x y) z ≡
      realPower x (multiply y z)
    real-power-product :
      (x y z : R) →
      lessThan zeroR x →
      lessThan zeroR y →
      realPower (multiply x y) z ≡
      multiply (realPower x z) (realPower y z)
    real-power-square :
      (x : R) →
      lessThan zeroR x →
      realPower x (fromNat 2) ≡ multiply x x

subtract :
  {R : Set} →
  RealPowerStructure R →
  R →
  R →
  R
subtract reals x y =
  RealPowerStructure.add reals x
    (RealPowerStructure.negate reals y)

divide :
  {R : Set} →
  RealPowerStructure R →
  R →
  R →
  R
divide reals x y =
  RealPowerStructure.multiply reals x
    (RealPowerStructure.inverse reals y)

threeHalves :
  {R : Set} →
  RealPowerStructure R →
  R
threeHalves reals =
  divide reals
    (RealPowerStructure.fromNat reals 3)
    (RealPowerStructure.fromNat reals 2)

radicalTerm :
  {R : Set} →
  RealPowerStructure R →
  R
radicalTerm reals =
  RealPowerStructure.multiply reals
    (RealPowerStructure.fromNat reals 6)
    (RealPowerStructure.squareRoot reals
      (RealPowerStructure.fromNat reals 43))

positiveBase :
  {R : Set} →
  RealPowerStructure R →
  R
positiveBase reals =
  RealPowerStructure.add reals
    (RealPowerStructure.fromNat reals 52)
    (radicalTerm reals)

negativeBase :
  {R : Set} →
  RealPowerStructure R →
  R
negativeBase reals =
  subtract reals
    (RealPowerStructure.fromNat reals 52)
    (radicalTerm reals)

aime-1990-p2 : Set₁
aime-1990-p2 =
  (R : Set) →
  (reals : RealPowerStructure R) →
  subtract reals
    (RealPowerStructure.realPower reals
      (positiveBase reals)
      (threeHalves reals))
    (RealPowerStructure.realPower reals
      (negativeBase reals)
      (threeHalves reals))
  ≡ RealPowerStructure.fromNat reals 828
