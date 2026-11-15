-- Statement-only formalization of miniF2F test problem amc12b_2020_p2. This file contains no
-- proof.

module amc12b-2020-p2 where

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

differenceOfSquares :
  {R : Set} →
  RealFieldStructure R →
  R →
  R →
  R
differenceOfSquares reals x y =
  subtract reals
    (square reals x)
    (square reals y)

differenceTimesSum :
  {R : Set} →
  RealFieldStructure R →
  R →
  R →
  R
differenceTimesSum reals x y =
  RealFieldStructure.multiply reals
    (subtract reals x y)
    (RealFieldStructure.add reals x y)

amc12b-2020-p2 : Set₁
amc12b-2020-p2 =
  (R : Set) →
  (reals : RealFieldStructure R) →
  RealFieldStructure.multiply reals
    (divide reals
      (differenceOfSquares reals
        (numeral reals 100)
        (numeral reals 7))
      (differenceOfSquares reals
        (numeral reals 70)
        (numeral reals 11)))
    (divide reals
      (differenceTimesSum reals
        (numeral reals 70)
        (numeral reals 11))
      (differenceTimesSum reals
        (numeral reals 100)
        (numeral reals 7)))
  ≡ RealFieldStructure.oneR reals
