-- Statement-only formalization of miniF2F test problem imosl_2007_algebra_p6:
-- a cyclic cubic inequality for a normalized nonnegative real sequence.
-- This file contains no proof.

module imosl-2007-algebra-p6 where

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

-- Archimedean completeness characterizes the standard real-number domain.
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

square : {R : Set} → RealStructure R → R → R
square reals x =
  RealStructure.multiply reals x x

divide : {R : Set} → RealStructure R → R → R → R
divide reals x y =
  RealStructure.multiply reals x (RealStructure.inverse reals y)

strictlyLess : {R : Set} → RealStructure R → R → R → Set
strictlyLess reals x y =
  (RealStructure.lessOrEqual reals x y) ∧ (x ≠ y)

sumSquaresFromOne :
  {R : Set} →
  RealStructure R →
  (Nat → R) →
  Nat →
  R
sumSquaresFromOne reals a zero =
  RealStructure.zeroR reals
sumSquaresFromOne reals a (suc n) =
  RealStructure.add reals
    (sumSquaresFromOne reals a n)
    (square reals (a (suc n)))

sumAdjacentTerms :
  {R : Set} →
  RealStructure R →
  (Nat → R) →
  Nat →
  R
sumAdjacentTerms reals a zero =
  RealStructure.zeroR reals
sumAdjacentTerms reals a (suc n) =
  RealStructure.add reals
    (sumAdjacentTerms reals a n)
    (RealStructure.multiply reals
      (square reals (a (suc n)))
      (a (suc (suc n))))

cyclicCubicSum :
  {R : Set} →
  RealStructure R →
  (Nat → R) →
  R
cyclicCubicSum reals a =
  RealStructure.add reals
    (sumAdjacentTerms reals a 99)
    (RealStructure.multiply reals
      (square reals (a 100))
      (a 1))

module Statement {R : Set} (standard : StandardReal R) where
  reals : RealStructure R
  reals = StandardReal.arithmetic standard

  proposition : Set
  proposition =
    (a : Nat → R) →
    ((i : Nat) →
      RealStructure.lessOrEqual reals
        (RealStructure.zeroR reals)
        (a i)) →
    sumSquaresFromOne reals a 100 ≡ RealStructure.oneR reals →
    strictlyLess reals
      (cyclicCubicSum reals a)
      (divide reals
        (RealStructure.fromNat reals 12)
        (RealStructure.fromNat reals 25))

imosl-2007-algebra-p6 : Set₁
imosl-2007-algebra-p6 =
  (R : Set) →
  (standard : StandardReal R) →
  Statement.proposition standard
