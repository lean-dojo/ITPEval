-- Statement-only formalization of miniF2F test problem algebra_others_exirrpowirrrat. This file
-- contains no proof.

module algebra_others_exirrpowirrrat where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _≠_
infixr 4 _∧_
infixr 3 _∨_

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

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

record Rat : Set where
  constructor fraction
  field
    numerator            : Int
    denominatorMinusOne : Nat

record RealNumberModel (R : Set) : Set₁ where
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
    fromNat-injective :
      (m n : Nat) → fromNat m ≡ fromNat n → m ≡ n
    fromNat-positive :
      (n : Nat) → lessThan zeroR (fromNat (suc n))

    square-root-positive :
      (x : R) →
      lessThan zeroR x →
      lessThan zeroR (squareRoot x)
    square-root-square :
      (x : R) →
      lessThan zeroR x →
      multiply (squareRoot x) (squareRoot x) ≡ x
    square-root-unique :
      (x y : R) →
      lessThan zeroR x →
      lessThan zeroR y →
      multiply y y ≡ x →
      squareRoot x ≡ y

    archimedean :
      (x : R) →
      Exists Nat (λ n → lessThan x (fromNat n))

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
    real-power-square :
      (x : R) →
      lessThan zeroR x →
      realPower x (fromNat 2) ≡ multiply x x

fromInt : {R : Set} → RealNumberModel R → Int → R
fromInt reals (pos n) = RealNumberModel.fromNat reals n
fromInt reals (negsuc n) =
  RealNumberModel.negate reals
    (RealNumberModel.fromNat reals (suc n))

divide :
  {R : Set} →
  RealNumberModel R →
  R →
  R →
  R
divide reals x y =
  RealNumberModel.multiply reals x
    (RealNumberModel.inverse reals y)

toReal :
  {R : Set} →
  RealNumberModel R →
  Rat →
  R
toReal reals q =
  divide reals
    (fromInt reals (Rat.numerator q))
    (RealNumberModel.fromNat reals
      (suc (Rat.denominatorMinusOne q)))

Rational :
  {R : Set} →
  RealNumberModel R →
  R →
  Set
Rational reals x =
  Exists Rat (λ q → x ≡ toReal reals q)

Irrational :
  {R : Set} →
  RealNumberModel R →
  R →
  Set
Irrational reals x = Rational reals x → ⊥

algebra_others_exirrpowirrrat : Set₁
algebra_others_exirrpowirrrat =
  (R : Set) →
  (reals : RealNumberModel R) →
  Exists R λ a →
  Exists R λ b →
    Irrational reals a ∧
    Irrational reals b ∧
    Rational reals (RealNumberModel.realPower reals a b)
