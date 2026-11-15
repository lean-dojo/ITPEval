-- Statement-only formalization of miniF2F valid problem amc12a_2002_p12. This file contains no
-- proof.

module amc12a-2002-p12 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

infix 4 _≠_ _≤_
infixr 3 _∨_

data ⊥ : Set where

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

data _∨_ (A B : Set) : Set where
  left : A → A ∨ B
  right : B → A ∨ B

record Divides (d n : Nat) : Set where
  field
    quotient : Nat
    product : d * quotient ≡ n

record Prime (n : Nat) : Set where
  field
    at-least-two : 2 ≤ n
    divisor-is-trivial :
      (d : Nat) →
      Divides d n →
      d ≡ 1 ∨ d ≡ n

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

polynomial :
  {R : Set} →
  RealField R →
  R →
  R →
  R
polynomial reals k x =
  RealField.add reals
    (RealField.add reals
      (RealField.multiply reals x x)
      (RealField.negate reals
        (RealField.multiply reals
          (RealField.fromNat reals 63)
          x)))
    k

amc12a-2002-p12 : Set₁
amc12a-2002-p12 =
  (R : Set) →
  (reals : RealField R) →
  (f : R → R) →
  (k : R) →
  (a b : Nat) →
  ((x : R) → f x ≡ polynomial reals k x) →
  f (RealField.fromNat reals a) ≡ RealField.zeroR reals →
  f (RealField.fromNat reals b) ≡ RealField.zeroR reals →
  a ≠ b →
  Prime a →
  Prime b →
  k ≡ RealField.fromNat reals 122
