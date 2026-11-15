-- Statement-only formalization of miniF2F valid problem mathd_algebra_89: simplifying a
-- real-number expression with powers and a nonzero variable to 49 / 64. This file contains no proof.

{-# OPTIONS --safe #-}

module mathd-algebra-89 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _≠_

data ⊥ : Set where

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

record RealField (R : Set) : Set₁ where
  field
    zeroR oneR : R
    add multiply : R → R → R
    negate inverse : R → R
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

    fromNat-zero :
      fromNat zero ≡ zeroR
    fromNat-successor :
      (n : Nat) → fromNat (suc n) ≡ add (fromNat n) oneR
    fromNat-injective :
      (m n : Nat) → fromNat m ≡ fromNat n → m ≡ n

module Statement {R : Set} (reals : RealField R) where
  open RealField reals

  power : R → Nat → R
  power x zero = oneR
  power x (suc n) = multiply x (power x n)

  divide : R → R → R
  divide x y = multiply x (inverse y)

  proposition : Set
  proposition =
    (b : R) →
    b ≠ zeroR →
    multiply
      (power
        (multiply (fromNat 7) (power b 3))
        2)
      (inverse
        (power
          (multiply (fromNat 4) (power b 2))
          3))
    ≡ divide (fromNat 49) (fromNat 64)

mathd-algebra-89 : Set₁
mathd-algebra-89 =
  (R : Set) →
  (reals : RealField R) →
  Statement.proposition reals
