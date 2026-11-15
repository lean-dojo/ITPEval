-- Statement-only formalization of miniF2F test problem mathd_algebra_184:
-- positive reals satisfying a squared = 6b = 54/b have a = 3 times
-- the square root of 2. This file contains no proof.

module mathd-algebra-184 where

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

-- Complete Archimedean ordered fields are unique up to ordered-field
-- isomorphism and therefore present the standard real-number domain.
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

divide : {R : Set} → RealStructure R → R → R → R
divide reals x y =
  RealStructure.multiply reals x (RealStructure.inverse reals y)

square : {R : Set} → RealStructure R → R → R
square reals x =
  RealStructure.multiply reals x x

strictlyPositive : {R : Set} → RealStructure R → R → Set
strictlyPositive reals x =
  (RealStructure.lessOrEqual reals
    (RealStructure.zeroR reals) x) ∧
  (RealStructure.zeroR reals ≠ x)

module Statement {R : Set} (standard : StandardReal R) where
  reals : RealStructure R
  reals = StandardReal.arithmetic standard

  proposition : Set
  proposition =
    (a b : R) →
    strictlyPositive reals a →
    strictlyPositive reals b →
    square reals a ≡
      RealStructure.multiply reals
        (RealStructure.fromNat reals 6)
        b →
    square reals a ≡
      divide reals
        (RealStructure.fromNat reals 54)
        b →
    a ≡ RealStructure.multiply reals
      (RealStructure.fromNat reals 3)
      (RealStructure.squareRoot reals
        (RealStructure.fromNat reals 2))

mathd-algebra-184 : Set₁
mathd-algebra-184 =
  (R : Set) →
  (standard : StandardReal R) →
  Statement.proposition standard
