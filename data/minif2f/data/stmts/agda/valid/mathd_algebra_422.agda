-- Statement-only formalization of miniF2F valid problem mathd_algebra_422:
-- for a real bijection sigma(t) = 5 * t - 12 satisfying
-- sigma(x + 1) equal to the inverse of sigma applied to x, one has
-- x = 47 / 24. This file contains no proof.

{-# OPTIONS --safe #-}

module mathd-algebra-422 where

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

-- Complete Archimedean ordered fields present the standard real numbers up to
-- ordered-field isomorphism.
record CompleteArchimedeanOrderedField (R : Set) : Set₁ where
  field
    zeroR oneR : R
    add multiply : R → R → R
    negate reciprocal : R → R
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
    reciprocal-zero :
      reciprocal zeroR ≡ zeroR
    multiply-reciprocal :
      (x : R) →
      x ≠ zeroR →
      multiply x (reciprocal x) ≡ oneR

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

record RealNumbers : Set₁ where
  field
    Carrier   : Set
    structure : CompleteArchimedeanOrderedField Carrier

Real : RealNumbers → Set
Real = RealNumbers.Carrier

realStructure :
  (reals : RealNumbers) →
  CompleteArchimedeanOrderedField (Real reals)
realStructure = RealNumbers.structure

record Bijection (A B : Set) : Set where
  field
    forward : A → B
    inverse : B → A
    inverse-forward :
      (x : A) → inverse (forward x) ≡ x
    forward-inverse :
      (y : B) → forward (inverse y) ≡ y

add :
  (reals : RealNumbers) →
  Real reals →
  Real reals →
  Real reals
add reals =
  CompleteArchimedeanOrderedField.add (realStructure reals)

multiply :
  (reals : RealNumbers) →
  Real reals →
  Real reals →
  Real reals
multiply reals =
  CompleteArchimedeanOrderedField.multiply (realStructure reals)

subtract :
  (reals : RealNumbers) →
  Real reals →
  Real reals →
  Real reals
subtract reals x y =
  add reals x
    (CompleteArchimedeanOrderedField.negate (realStructure reals) y)

divide :
  (reals : RealNumbers) →
  Real reals →
  Real reals →
  Real reals
divide reals x y =
  multiply reals x
    (CompleteArchimedeanOrderedField.reciprocal (realStructure reals) y)

natural :
  (reals : RealNumbers) →
  Nat →
  Real reals
natural reals =
  CompleteArchimedeanOrderedField.fromNat (realStructure reals)

-- Transport along the ordered-field isomorphism between any such presentation
-- and the standard reals preserves numerals, arithmetic, bijections, inverses,
-- and equality, so this proposition is equivalent to the source statement.
mathd-algebra-422 : Set₁
mathd-algebra-422 =
  (reals : RealNumbers) →
  (x : Real reals) →
  (σ : Bijection (Real reals) (Real reals)) →
  ((t : Real reals) →
    Bijection.forward σ t ≡
    subtract reals
      (multiply reals (natural reals 5) t)
      (natural reals 12)) →
  Bijection.forward σ (add reals x (natural reals 1))
    ≡ Bijection.inverse σ x →
  x ≡ divide reals (natural reals 47) (natural reals 24)
