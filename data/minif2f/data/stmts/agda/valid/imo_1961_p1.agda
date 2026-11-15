-- Statement-only formalization of miniF2F valid problem imo_1961_p1: inequalities
-- relating the sum and sum of squares of three distinct positive reals whose
-- product condition is x * y = z^2. This file contains no proof.

{-# OPTIONS --safe #-}

module imo-1961-p1 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ)

infix 4 _≠_
infixr 3 _∧_
infixr 2 _∨_

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
      (x y : R) →
      lessOrEqual x y ∨ lessOrEqual y x
    add-order :
      (x y z : R) →
      lessOrEqual x y →
      lessOrEqual (add z x) (add z y)
    multiply-nonnegative :
      (x y : R) →
      lessOrEqual zeroR x →
      lessOrEqual zeroR y →
      lessOrEqual zeroR (multiply x y)
    zero-less-than-one :
      lessOrEqual zeroR oneR ∧ oneR ≠ zeroR

    fromNat-zero :
      fromNat zero ≡ zeroR
    fromNat-successor :
      (n : Nat) → fromNat (suc n) ≡ add (fromNat n) oneR
    fromNat-injective :
      (m n : Nat) → fromNat m ≡ fromNat n → m ≡ n
    archimedean :
      (x : R) → Σ Nat (λ n → lessOrEqual x (fromNat n))

    least-upper-bound :
      (P : R → Set) →
      Σ R (λ x → P x) →
      Σ R (λ upper → (x : R) → P x → lessOrEqual x upper) →
      Σ R (λ supremum →
        ((x : R) → P x → lessOrEqual x supremum) ∧
        ((upper : R) →
          ((x : R) → P x → lessOrEqual x upper) →
          lessOrEqual supremum upper))

strictlyLess :
  {R : Set} →
  CompleteArchimedeanOrderedField R →
  R →
  R →
  Set
strictlyLess reals x y =
  CompleteArchimedeanOrderedField.lessOrEqual reals x y ∧ x ≠ y

module Statement
  {R : Set}
  (reals : CompleteArchimedeanOrderedField R)
  where

  open CompleteArchimedeanOrderedField reals

  infixl 6 _+_
  infixl 7 _*_
  infix 4 _<_

  _+_ : R → R → R
  _+_ = add

  _*_ : R → R → R
  _*_ = multiply

  _<_ : R → R → Set
  _<_ = strictlyLess reals

  square : R → R
  square x = x * x

  proposition : Set
  proposition =
    (x y z a b : R) →
    zeroR < x →
    zeroR < y →
    zeroR < z →
    x ≠ y →
    y ≠ z →
    z ≠ x →
    (x + y) + z ≡ a →
    (square x + square y) + square z ≡ square b →
    x * y ≡ square z →
    zeroR < a ∧
      (square b < square a ∧
       square a < fromNat 3 * square b)

imo-1961-p1 : Set₁
imo-1961-p1 =
  (R : Set) →
  (reals : CompleteArchimedeanOrderedField R) →
  Statement.proposition reals
