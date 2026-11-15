-- Statement-only formalization of miniF2F test problem imo_1960_p2. This file contains no
-- proof.

module imo-1960-p2 where

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

square : {R : Set} → RealStructure R → R → R
square reals x =
  RealStructure.multiply reals x x

strictlyLess : {R : Set} → RealStructure R → R → R → Set
strictlyLess reals x y =
  RealStructure.lessOrEqual reals x y ∧ (x ≠ y)

radicand : {R : Set} → RealStructure R → R → R
radicand reals x =
  RealStructure.add reals
    (RealStructure.oneR reals)
    (RealStructure.multiply reals
      (RealStructure.fromNat reals 2)
      x)

denominator : {R : Set} → RealStructure R → R → R
denominator reals x =
  subtract reals
    (RealStructure.oneR reals)
    (RealStructure.squareRoot reals (radicand reals x))

inequalityLeft : {R : Set} → RealStructure R → R → R
inequalityLeft reals x =
  divide reals
    (RealStructure.multiply reals
      (RealStructure.fromNat reals 4)
      (square reals x))
    (square reals (denominator reals x))

inequalityRight : {R : Set} → RealStructure R → R → R
inequalityRight reals x =
  RealStructure.add reals
    (RealStructure.multiply reals
      (RealStructure.fromNat reals 2)
      x)
    (RealStructure.fromNat reals 9)

lowerBound : {R : Set} → RealStructure R → R
lowerBound reals =
  RealStructure.negate reals
    (divide reals
      (RealStructure.oneR reals)
      (RealStructure.fromNat reals 2))

upperBound : {R : Set} → RealStructure R → R
upperBound reals =
  divide reals
    (RealStructure.fromNat reals 45)
    (RealStructure.fromNat reals 8)

imo-1960-p2 : Set₁
imo-1960-p2 =
  (R : Set) →
  (reals : RealStructure R) →
  (x : R) →
  RealStructure.lessOrEqual reals
    (RealStructure.zeroR reals)
    (radicand reals x) →
  square reals (denominator reals x) ≠
    RealStructure.zeroR reals →
  strictlyLess reals
    (inequalityLeft reals x)
    (inequalityRight reals x) →
  RealStructure.lessOrEqual reals
    (lowerBound reals)
    x
  ∧ strictlyLess reals x (upperBound reals)
