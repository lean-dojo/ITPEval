-- Statement-only formalization of miniF2F valid problem mathd_algebra_35:
-- evaluating two real functions defined by a quadratic and reciprocal rule
-- gives p(q(2)) = -7. This file contains no proof.

{-# OPTIONS --safe #-}

module mathd-algebra-35 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _≠_
infixr 3 _∧_ _∨_

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

natural :
  {R : Set} →
  (R → R → R) →
  R →
  R →
  Nat →
  R
natural add zeroR oneR zero = zeroR
natural add zeroR oneR (suc n) =
  add (natural add zeroR oneR n) oneR

-- A Dedekind-complete Archimedean ordered field is an ordered-field
-- presentation of the standard real numbers.
record RealPresentation (R : Set) : Set₁ where
  field
    zeroR oneR : R
    add multiply : R → R → R
    negate inverse : R → R
    lessOrEqual : R → R → Set

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
    order-antisymmetric :
      (x y : R) →
      lessOrEqual x y →
      lessOrEqual y x →
      x ≡ y
    order-transitive :
      (x y z : R) →
      lessOrEqual x y →
      lessOrEqual y z →
      lessOrEqual x z
    order-total :
      (x y : R) → lessOrEqual x y ∨ lessOrEqual y x
    add-order :
      (x y z : R) →
      lessOrEqual x y →
      lessOrEqual (add x z) (add y z)
    multiply-nonnegative :
      (x y : R) →
      lessOrEqual zeroR x →
      lessOrEqual zeroR y →
      lessOrEqual zeroR (multiply x y)
    zero-less-than-one :
      lessOrEqual zeroR oneR

    archimedean :
      (x : R) →
      Exists Nat
        (λ n →
          lessOrEqual x (natural add zeroR oneR n))

    least-upper-bound :
      (S : R → Set) →
      Exists R S →
      Exists R
        (λ upper →
          (x : R) →
          S x →
          lessOrEqual x upper) →
      Exists R
        (λ supremum →
          ((x : R) →
            S x →
            lessOrEqual x supremum)
          ∧
          ((upper : R) →
            ((x : R) →
              S x →
              lessOrEqual x upper) →
            lessOrEqual supremum upper))

module Statement {R : Set} (reals : RealPresentation R) where
  open RealPresentation reals

  infixl 6 _-_
  infixl 7 _*_ _/_

  fromNat : Nat → R
  fromNat = natural add zeroR oneR

  _-_ : R → R → R
  x - y = add x (negate y)

  _*_ : R → R → R
  _*_ = multiply

  _/_ : R → R → R
  x / y = x * inverse y

  square : R → R
  square x = x * x

  proposition : Set
  proposition =
    (p q : R → R) →
    ((x : R) → p x ≡ fromNat 2 - square x) →
    ((x : R) → x ≠ zeroR → q x ≡ fromNat 6 / x) →
    p (q (fromNat 2)) ≡ negate (fromNat 7)

mathd-algebra-35 : Set₁
mathd-algebra-35 =
  (R : Set) →
  (reals : RealPresentation R) →
  Statement.proposition reals
