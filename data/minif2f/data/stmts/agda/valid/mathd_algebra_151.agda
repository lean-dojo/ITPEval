-- Statement-only formalization of miniF2F valid problem mathd_algebra_151. This file contains
-- no proof.

module mathd-algebra-151 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≠_
infixl 6 _+z_ _−z_
infixr 3 _∨_

data ⊥ : Set where

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

difference : Nat → Nat → Int
difference zero zero = pos zero
difference (suc m) zero = pos (suc m)
difference zero (suc n) = negsuc n
difference (suc m) (suc n) = difference m n

negateInt : Int → Int
negateInt (pos zero) = pos zero
negateInt (pos (suc n)) = negsuc n
negateInt (negsuc n) = pos (suc n)

_+z_ : Int → Int → Int
pos m +z pos n = pos (m + n)
pos m +z negsuc n = difference m (suc n)
negsuc m +z pos n = difference n (suc m)
negsuc m +z negsuc n = negsuc (suc (m + n))

_−z_ : Int → Int → Int
x −z y = x +z negateInt y

embedInt :
  {R : Set} →
  (Nat → R) →
  (R → R) →
  Int →
  R
embedInt fromNat negate (pos n) = fromNat n
embedInt fromNat negate (negsuc n) = negate (fromNat (suc n))

record StandardRealSquareRootFloorCeiling (R : Set) : Set₁ where
  field
    zeroR oneR : R
    add multiply : R → R → R
    negate inverse squareRoot : R → R
    lessOrEqual : R → R → Set
    fromNat : Nat → R
    floor ceiling : R → Int

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
    fromNat-addition :
      (m n : Nat) →
      fromNat (m + n) ≡ add (fromNat m) (fromNat n)
    fromNat-multiplication :
      (m n : Nat) →
      fromNat (m * n) ≡ multiply (fromNat m) (fromNat n)
    fromNat-injective :
      (m n : Nat) → fromNat m ≡ fromNat n → m ≡ n
    fromNat-nonnegative :
      (n : Nat) → lessOrEqual zeroR (fromNat n)

    square-root-nonnegative :
      (x : R) → lessOrEqual zeroR (squareRoot x)
    square-root-square :
      (x : R) →
      lessOrEqual zeroR x →
      multiply (squareRoot x) (squareRoot x) ≡ x
    square-root-unique :
      (x y : R) →
      lessOrEqual zeroR y →
      multiply y y ≡ x →
      squareRoot x ≡ y

    floor-lower-bound :
      (x : R) →
      lessOrEqual
        (embedInt fromNat negate (floor x))
        x
    floor-upper-bound :
      (x : R) →
      lessOrEqual
        x
        (add (embedInt fromNat negate (floor x)) oneR)
    floor-upper-strict :
      (x : R) →
      x ≠ add (embedInt fromNat negate (floor x)) oneR

    ceiling-upper-bound :
      (x : R) →
      lessOrEqual
        x
        (embedInt fromNat negate (ceiling x))
    ceiling-lower-bound :
      (x : R) →
      lessOrEqual
        (add
          (embedInt fromNat negate (ceiling x))
          (negate oneR))
        x
    ceiling-lower-strict :
      (x : R) →
      add
        (embedInt fromNat negate (ceiling x))
        (negate oneR)
      ≠ x

mathd-algebra-151 : Set₁
mathd-algebra-151 =
  (R : Set) →
  (reals : StandardRealSquareRootFloorCeiling R) →
  StandardRealSquareRootFloorCeiling.ceiling reals
    (StandardRealSquareRootFloorCeiling.squareRoot reals
      (StandardRealSquareRootFloorCeiling.fromNat reals 27))
  −z
  StandardRealSquareRootFloorCeiling.floor reals
    (StandardRealSquareRootFloorCeiling.squareRoot reals
      (StandardRealSquareRootFloorCeiling.fromNat reals 26))
  ≡ pos 1
