-- Statement-only formalization of miniF2F valid problem imo_2006_p3. This file contains no
-- proof.

module imo-2006-p3 where

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

square : {R : Set} → RealStructure R → R → R
square reals x =
  RealStructure.multiply reals x x

subtract : {R : Set} → RealStructure R → R → R → R
subtract reals x y =
  RealStructure.add reals x (RealStructure.negate reals y)

divide : {R : Set} → RealStructure R → R → R → R
divide reals x y =
  RealStructure.multiply reals x (RealStructure.inverse reals y)

cyclicTerm : {R : Set} → RealStructure R → R → R → R
cyclicTerm reals x y =
  RealStructure.multiply reals
    (RealStructure.multiply reals x y)
    (subtract reals (square reals x) (square reals y))

leftSide : {R : Set} → RealStructure R → R → R → R → R
leftSide reals a b c =
  RealStructure.add reals
    (RealStructure.add reals
      (cyclicTerm reals a b)
      (cyclicTerm reals b c))
    (cyclicTerm reals c a)

sumOfSquares : {R : Set} → RealStructure R → R → R → R → R
sumOfSquares reals a b c =
  RealStructure.add reals
    (RealStructure.add reals
      (square reals a)
      (square reals b))
    (square reals c)

coefficient : {R : Set} → RealStructure R → R
coefficient reals =
  divide reals
    (RealStructure.multiply reals
      (RealStructure.fromNat reals 9)
      (RealStructure.squareRoot reals
        (RealStructure.fromNat reals 2)))
    (RealStructure.fromNat reals 32)

rightSide : {R : Set} → RealStructure R → R → R → R → R
rightSide reals a b c =
  RealStructure.multiply reals
    (coefficient reals)
    (square reals (sumOfSquares reals a b c))

imo-2006-p3 : Set₁
imo-2006-p3 =
  (R : Set) →
  (reals : RealStructure R) →
  (a b c : R) →
  RealStructure.lessOrEqual reals
    (leftSide reals a b c)
    (rightSide reals a b c)
