-- Statement-only formalization of miniF2F valid problem amc12a_2008_p8 using a
-- complete Archimedean ordered-field presentation of the real numbers: positive
-- x and y satisfying y^3 = 1 and 6x^2 = 2(6y^2) have x^3 = 2 sqrt(2).
-- This file contains no proof.

module amc12a-2008-p8 where

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

    less-irreflexive :
      (x : R) → lessThan x x → ⊥
    less-transitive :
      (x y z : R) →
      lessThan x y →
      lessThan y z →
      lessThan x z
    order-trichotomy :
      (x y : R) →
      lessThan x y ∨ (x ≡ y ∨ lessThan y x)
    add-strict-monotone :
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

lessOrEqual :
  {R : Set} →
  RealStructure R →
  R →
  R →
  Set
lessOrEqual reals x y =
  RealStructure.lessThan reals x y ∨ x ≡ y

-- Complete Archimedean ordered fields are unique up to ordered-field
-- isomorphism, so this packages a presentation of the standard real numbers.
record StandardReal (R : Set) : Set₁ where
  field
    arithmetic : RealStructure R

    archimedean :
      (x : R) →
      Exists Nat λ n →
        lessOrEqual arithmetic
          x
          (RealStructure.fromNat arithmetic n)

    least-upper-bound :
      (subset : R → Set) →
      Exists R subset →
      Exists R
        (λ upper →
          (x : R) →
          subset x →
          lessOrEqual arithmetic x upper) →
      Exists R λ supremum →
        ((x : R) →
          subset x →
          lessOrEqual arithmetic x supremum) ∧
        ((upper : R) →
          ((x : R) →
            subset x →
            lessOrEqual arithmetic x upper) →
          lessOrEqual arithmetic supremum upper)

power : {R : Set} → RealStructure R → R → Nat → R
power reals x zero =
  RealStructure.oneR reals
power reals x (suc n) =
  RealStructure.multiply reals x (power reals x n)

strictlyPositive : {R : Set} → RealStructure R → R → Set
strictlyPositive reals x =
  RealStructure.lessThan reals (RealStructure.zeroR reals) x

module Statement {R : Set} (standard : StandardReal R) where
  reals : RealStructure R
  reals = StandardReal.arithmetic standard

  proposition : Set
  proposition =
    (x y : R) →
    (strictlyPositive reals x ∧ strictlyPositive reals y) →
    power reals y 3 ≡ RealStructure.fromNat reals 1 →
    RealStructure.multiply reals
      (RealStructure.fromNat reals 6)
      (power reals x 2)
      ≡
      RealStructure.multiply reals
        (RealStructure.fromNat reals 2)
        (RealStructure.multiply reals
          (RealStructure.fromNat reals 6)
          (power reals y 2)) →
    power reals x 3
      ≡
      RealStructure.multiply reals
        (RealStructure.fromNat reals 2)
        (RealStructure.squareRoot reals
          (RealStructure.fromNat reals 2))

amc12a-2008-p8 : Set₁
amc12a-2008-p8 =
  (R : Set) →
  (standard : StandardReal R) →
  Statement.proposition standard
