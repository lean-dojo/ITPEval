-- Statement-only formalization of miniF2F test problem imo_1964_p2: positive real
-- numbers satisfying the three strict triangle inequalities obey the stated cubic
-- inequality. Real numbers are represented by a complete Archimedean ordered field.
-- This file contains no proof.

module imo-1964-p2 where

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
    first  : A
    second : B

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

    archimedean :
      (x : R) →
      Exists Nat (λ n → lessOrEqual x (fromNat n))

    least-upper-bound :
      (P : R → Set) →
      Exists R P →
      Exists R
        (λ upper →
          (x : R) → P x → lessOrEqual x upper) →
      Exists R
        (λ supremum →
          ((x : R) → P x → lessOrEqual x supremum) ∧
          ((upper : R) →
            ((x : R) → P x → lessOrEqual x upper) →
            lessOrEqual supremum upper))

strictlyLess :
  {R : Set} →
  RealStructure R →
  R →
  R →
  Set
strictlyLess reals x y =
  RealStructure.lessOrEqual reals x y ∧ (x ≠ y)

subtract :
  {R : Set} →
  RealStructure R →
  R →
  R →
  R
subtract reals x y =
  RealStructure.add reals x (RealStructure.negate reals y)

square :
  {R : Set} →
  RealStructure R →
  R →
  R
square reals x =
  RealStructure.multiply reals x x

three :
  {R : Set} →
  RealStructure R →
  R
three reals =
  RealStructure.fromNat reals (suc (suc (suc zero)))

leftSide :
  {R : Set} →
  RealStructure R →
  R →
  R →
  R →
  R
leftSide reals a b c =
  RealStructure.add reals
    (RealStructure.add reals
      (RealStructure.multiply reals
        (square reals a)
        (subtract reals
          (RealStructure.add reals b c)
          a))
      (RealStructure.multiply reals
        (square reals b)
        (subtract reals
          (RealStructure.add reals c a)
          b)))
    (RealStructure.multiply reals
      (square reals c)
      (subtract reals
        (RealStructure.add reals a b)
        c))

rightSide :
  {R : Set} →
  RealStructure R →
  R →
  R →
  R →
  R
rightSide reals a b c =
  RealStructure.multiply reals
    (RealStructure.multiply reals
      (RealStructure.multiply reals (three reals) a)
      b)
    c

imo-1964-p2 : Set₁
imo-1964-p2 =
  (R : Set) →
  (reals : RealStructure R) →
  (a b c : R) →
  strictlyLess reals (RealStructure.zeroR reals) a →
  strictlyLess reals (RealStructure.zeroR reals) b →
  strictlyLess reals (RealStructure.zeroR reals) c →
  strictlyLess reals c (RealStructure.add reals a b) →
  strictlyLess reals b (RealStructure.add reals a c) →
  strictlyLess reals a (RealStructure.add reals b c) →
  RealStructure.lessOrEqual reals
    (leftSide reals a b c)
    (rightSide reals a b c)
