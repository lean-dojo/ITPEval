-- Statement-only formalization of miniF2F test problem amc12b_2020_p6:
-- for n at least 9, the factorial quotient ((n + 2)! - (n + 1)!) / n! is
-- the square of a natural number. This file contains no proof.

module amc12b-2020-p6 where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _*_; _<_)

infix 4 _≤_ _≠_

data ⊥ : Set where

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

_≤_ : Nat → Nat → Set
m ≤ n = (m < suc n) ≡ true

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

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

factorial : Nat → Nat
factorial zero = 1
factorial (suc n) = suc n * factorial n

numeral :
  {R : Set} →
  RealFieldStructure R →
  Nat →
  R
numeral reals n =
  RealFieldStructure.fromNat reals n

subtract :
  {R : Set} →
  RealFieldStructure R →
  R →
  R →
  R
subtract reals x y =
  RealFieldStructure.add reals
    x
    (RealFieldStructure.negate reals y)

divide :
  {R : Set} →
  RealFieldStructure R →
  R →
  R →
  R
divide reals x y =
  RealFieldStructure.multiply reals
    x
    (RealFieldStructure.inverse reals y)

square :
  {R : Set} →
  RealFieldStructure R →
  R →
  R
square reals x =
  RealFieldStructure.multiply reals x x

amc12b-2020-p6 : Set₁
amc12b-2020-p6 =
  (R : Set) →
  (reals : RealFieldStructure R) →
  (n : Nat) →
  9 ≤ n →
  Exists Nat λ x →
    square reals (numeral reals x) ≡
    divide reals
      (subtract reals
        (numeral reals (factorial (n + 2)))
        (numeral reals (factorial (n + 1))))
      (numeral reals (factorial n))
