-- Statement-only formalization of miniF2F valid problem mathd_algebra_55: the two alternating
-- sums defining q and p imply q / p = 2 / 3. This file contains no proof.

{-# OPTIONS --safe #-}

module mathd-algebra-55 where

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

  infixl 6 _+_ _-_
  infixl 7 _/_

  _+_ : R → R → R
  _+_ = add

  _-_ : R → R → R
  x - y = add x (negate y)

  _/_ : R → R → R
  x / y = multiply x (inverse y)

  proposition : Set
  proposition =
    (q p : R) →
    q ≡
      fromNat 2 - fromNat 4 + fromNat 6 - fromNat 8 +
      fromNat 10 - fromNat 12 + fromNat 14 →
    p ≡
      fromNat 3 - fromNat 6 + fromNat 9 - fromNat 12 +
      fromNat 15 - fromNat 18 + fromNat 21 →
    q / p ≡ fromNat 2 / fromNat 3

mathd-algebra-55 : Set₁
mathd-algebra-55 =
  (R : Set) →
  (reals : RealField R) →
  Statement.proposition reals
