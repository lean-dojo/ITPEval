-- Statement-only formalization of miniF2F test problem mathd_algebra_276. This file contains no
-- proof.

module mathd-algebra-276 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≠_
infixl 6 _+z_
infixl 7 _*z_

data ⊥ : Set where

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

difference : Nat → Nat → Int
difference zero zero = pos zero
difference (suc m) zero = pos (suc m)
difference zero (suc n) = negsuc n
difference (suc m) (suc n) = difference m n

negative : Nat → Int
negative zero = pos zero
negative (suc n) = negsuc n

_+z_ : Int → Int → Int
pos m +z pos n = pos (m + n)
pos m +z negsuc n = difference m (suc n)
negsuc m +z pos n = difference n (suc m)
negsuc m +z negsuc n = negsuc (suc (m + n))

_*z_ : Int → Int → Int
pos m *z pos n = pos (m * n)
pos m *z negsuc n = negative (m * suc n)
negsuc m *z pos n = negative (suc m * n)
negsuc m *z negsuc n = pos (suc m * suc n)

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

fromInt : {R : Set} → RealFieldStructure R → Int → R
fromInt reals (pos n) =
  RealFieldStructure.fromNat reals n
fromInt reals (negsuc n) =
  RealFieldStructure.negate reals
    (RealFieldStructure.fromNat reals (suc n))

subtract :
  {R : Set} →
  RealFieldStructure R →
  R →
  R →
  R
subtract reals x y =
  RealFieldStructure.add reals x
    (RealFieldStructure.negate reals y)

square :
  {R : Set} →
  RealFieldStructure R →
  R →
  R
square reals x =
  RealFieldStructure.multiply reals x x

PolynomialIdentity :
  {R : Set} →
  RealFieldStructure R →
  Int →
  Int →
  Set
PolynomialIdentity {R} reals a b =
  (x : R) →
  subtract reals
    (subtract reals
      (RealFieldStructure.multiply reals
        (RealFieldStructure.fromNat reals 10)
        (square reals x))
      x)
    (RealFieldStructure.fromNat reals 24)
  ≡ RealFieldStructure.multiply reals
      (subtract reals
        (RealFieldStructure.multiply reals
          (fromInt reals a)
          x)
        (RealFieldStructure.fromNat reals 8))
      (RealFieldStructure.add reals
        (RealFieldStructure.multiply reals
          (fromInt reals b)
          x)
        (RealFieldStructure.fromNat reals 3))

mathd-algebra-276 : Set₁
mathd-algebra-276 =
  (R : Set) →
  (reals : RealFieldStructure R) →
  (a b : Int) →
  PolynomialIdentity reals a b →
  (a *z b) +z b ≡ pos 12
