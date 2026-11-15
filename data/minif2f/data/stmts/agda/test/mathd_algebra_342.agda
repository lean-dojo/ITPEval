-- Statement-only formalization of miniF2F test problem mathd_algebra_342. This file contains no
-- proof.

module mathd-algebra-342 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _≠_

data ⊥ : Set where

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

record RealFieldStructure (R : Set) : Set₁ where
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

open RealFieldStructure

sumFirst :
  {R : Set} →
  RealFieldStructure R →
  Nat →
  (Nat → R) →
  R
sumFirst reals zero term = zeroR reals
sumFirst reals (suc n) term =
  add reals (sumFirst reals n term) (term n)

divide :
  {R : Set} →
  RealFieldStructure R →
  R →
  R →
  R
divide reals x y = multiply reals x (inverse reals y)

mathd-algebra-342 : Set₁
mathd-algebra-342 =
  (R : Set) →
  (reals : RealFieldStructure R) →
  (a d : R) →
  sumFirst reals 5
    (λ k →
      add reals a
        (multiply reals (fromNat reals k) d))
    ≡ fromNat reals 70 →
  sumFirst reals 10
    (λ k →
      add reals a
        (multiply reals (fromNat reals k) d))
    ≡ fromNat reals 210 →
  a ≡ divide reals (fromNat reals 42) (fromNat reals 5)
