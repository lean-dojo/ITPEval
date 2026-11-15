-- Statement-only formalization of miniF2F test problem mathd_algebra_400:
-- a linear equation over the real numbers implies x = 50. This file contains no proof.

module mathd-algebra-400 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _≠_
infixr 2 _∨_
infixr 3 _∧_

data ⊥ : Set where

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

record _∧_ (A B : Set) : Set where
  constructor _,_
  field
    first  : A
    second : B

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

-- Complete Archimedean ordered fields are unique up to ordered-field
-- isomorphism, so this structurally presents the standard real numbers.
record CompleteArchimedeanOrderedField (R : Set) : Set₁ where
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

    archimedean :
      (x : R) →
      Exists Nat λ n → lessOrEqual x (fromNat n)

    least-upper-bound :
      (subset : R → Set) →
      Exists R subset →
      Exists R
        (λ upper →
          (x : R) →
          subset x →
          lessOrEqual x upper) →
      Exists R λ supremum →
        ((x : R) →
          subset x →
          lessOrEqual x supremum) ∧
        ((upper : R) →
          ((x : R) →
            subset x →
            lessOrEqual x upper) →
          lessOrEqual supremum upper)

divide :
  {R : Set} →
  CompleteArchimedeanOrderedField R →
  R →
  R →
  R
divide reals x y =
  CompleteArchimedeanOrderedField.multiply reals x
    (CompleteArchimedeanOrderedField.inverse reals y)

mathd-algebra-400 : Set₁
mathd-algebra-400 =
  (R : Set) →
  (reals : CompleteArchimedeanOrderedField R) →
  (x : R) →
  CompleteArchimedeanOrderedField.add reals
    (CompleteArchimedeanOrderedField.fromNat reals 5)
    (CompleteArchimedeanOrderedField.multiply reals
      (divide reals
        (CompleteArchimedeanOrderedField.fromNat reals 500)
        (CompleteArchimedeanOrderedField.fromNat reals 100))
      (CompleteArchimedeanOrderedField.fromNat reals 10))
    ≡ CompleteArchimedeanOrderedField.multiply reals
        (divide reals
          (CompleteArchimedeanOrderedField.fromNat reals 110)
          (CompleteArchimedeanOrderedField.fromNat reals 100))
        x →
  x ≡ CompleteArchimedeanOrderedField.fromNat reals 50
