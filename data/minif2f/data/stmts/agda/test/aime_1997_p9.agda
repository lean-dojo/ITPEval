-- Statement-only formalization of miniF2F test problem aime_1997_p9. This file contains no
-- proof.

module aime-1997-p9 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
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
    left  : A
    right : B

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

embedInt :
  {R : Set} →
  (Nat → R) →
  (R → R) →
  Int →
  R
embedInt fromNat negate (pos n) = fromNat n
embedInt fromNat negate (negsuc n) = negate (fromNat (suc n))

record RealFloorStructure (R : Set) : Set₁ where
  field
    zeroR oneR : R
    add multiply : R → R → R
    negate inverse : R → R
    lessOrEqual : R → R → Set
    fromNat : Nat → R
    floor : R → Int

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
    fromNat-injective :
      (m n : Nat) → fromNat m ≡ fromNat n → m ≡ n

    floor-lower-bound :
      (x : R) →
      lessOrEqual
        (embedInt fromNat negate (floor x))
        x
    floor-upper-bound :
      (x : R) →
      (lessOrEqual
        x
        (add (embedInt fromNat negate (floor x)) oneR))
      ∧
      (x ≠ add (embedInt fromNat negate (floor x)) oneR)

strictlyLess :
  {R : Set} →
  RealFloorStructure R →
  R →
  R →
  Set
strictlyLess reals x y =
  (RealFloorStructure.lessOrEqual reals x y) ∧ (x ≠ y)

subtract :
  {R : Set} →
  RealFloorStructure R →
  R →
  R →
  R
subtract reals x y =
  RealFloorStructure.add reals
    x
    (RealFloorStructure.negate reals y)

divide :
  {R : Set} →
  RealFloorStructure R →
  R →
  R →
  R
divide reals x y =
  RealFloorStructure.multiply reals
    x
    (RealFloorStructure.inverse reals y)

power :
  {R : Set} →
  RealFloorStructure R →
  R →
  Nat →
  R
power reals x zero =
  RealFloorStructure.oneR reals
power reals x (suc n) =
  RealFloorStructure.multiply reals x (power reals x n)

integerPart :
  {R : Set} →
  RealFloorStructure R →
  R →
  R
integerPart reals x =
  embedInt
    (RealFloorStructure.fromNat reals)
    (RealFloorStructure.negate reals)
    (RealFloorStructure.floor reals x)

fractionalPart :
  {R : Set} →
  RealFloorStructure R →
  R →
  R
fractionalPart reals x =
  subtract reals x (integerPart reals x)

aime-1997-p9 : Set₁
aime-1997-p9 =
  (R : Set) →
  (reals : RealFloorStructure R) →
  (a : R) →
  strictlyLess reals (RealFloorStructure.zeroR reals) a →
  fractionalPart reals
      (divide reals (RealFloorStructure.oneR reals) a)
    ≡ fractionalPart reals (power reals a 2) →
  strictlyLess reals
    (RealFloorStructure.fromNat reals 2)
    (power reals a 2) →
  strictlyLess reals
    (power reals a 2)
    (RealFloorStructure.fromNat reals 3) →
  subtract reals
      (power reals a 12)
      (RealFloorStructure.multiply reals
        (RealFloorStructure.fromNat reals 144)
        (divide reals (RealFloorStructure.oneR reals) a))
    ≡ RealFloorStructure.fromNat reals 233
