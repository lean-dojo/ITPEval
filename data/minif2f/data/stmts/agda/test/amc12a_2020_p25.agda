-- Statement-only formalization of miniF2F test problem amc12a_2020_p25: a
-- rational coefficient is determined from the finite real solution set of a
-- floor-function equation and its sum. This file contains no proof.

module amc12a-2020-p25 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≠_ _∈_
infixl 6 _+z_
infixl 7 _*z_
infixr 4 _∧_
infixr 3 _∨_
infix 2 _↔_

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

record _↔_ (A B : Set) : Set where
  field
    forward  : A → B
    backward : B → A

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _∈_ {A : Set} (x : A) : List A → Set where
  here  : {xs : List A} → x ∈ (x ∷ xs)
  there : {y : A} {xs : List A} → x ∈ xs → x ∈ (y ∷ xs)

data NoDuplicates {A : Set} : List A → Set where
  no-duplicates-empty :
    NoDuplicates []
  no-duplicates-cons :
    {x : A} {xs : List A} →
    (x ∈ xs → ⊥) →
    NoDuplicates xs →
    NoDuplicates (x ∷ xs)

foldLeft : {A : Set} → (A → A → A) → A → List A → A
foldLeft operation accumulator [] = accumulator
foldLeft operation accumulator (x ∷ xs) =
  foldLeft operation (operation accumulator x) xs

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

record Coprime (a : Int) (b : Nat) : Set where
  constructor bezout
  field
    left-coefficient right-coefficient : Int
    combination :
      (left-coefficient *z a) +z
      (right-coefficient *z pos b) ≡ pos 1

record Rat : Set where
  constructor fraction
  field
    numerator : Int
    denominator-minus-one : Nat
    reduced :
      Coprime numerator (suc denominator-minus-one)

denominator : Rat → Nat
denominator q = suc (Rat.denominator-minus-one q)

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
      lessOrEqual
        x
        (add (embedInt fromNat negate (floor x)) oneR)
    floor-upper-strict :
      (x : R) →
      x ≠ add (embedInt fromNat negate (floor x)) oneR

record StandardRealFloorStructure (R : Set) : Set₁ where
  field
    arithmetic : RealFloorStructure R

    archimedean :
      (x : R) →
      Exists Nat λ n →
        RealFloorStructure.lessOrEqual arithmetic
          x
          (RealFloorStructure.fromNat arithmetic n)

    least-upper-bound :
      (subset : R → Set) →
      Exists R subset →
      Exists R
        (λ upper →
          (x : R) →
          subset x →
          RealFloorStructure.lessOrEqual arithmetic x upper) →
      Exists R λ supremum →
        ((x : R) →
          subset x →
          RealFloorStructure.lessOrEqual arithmetic x supremum) ∧
        ((upper : R) →
          ((x : R) →
            subset x →
            RealFloorStructure.lessOrEqual arithmetic x upper) →
          RealFloorStructure.lessOrEqual arithmetic supremum upper)

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

square :
  {R : Set} →
  RealFloorStructure R →
  R →
  R
square reals x =
  RealFloorStructure.multiply reals x x

fromInt :
  {R : Set} →
  RealFloorStructure R →
  Int →
  R
fromInt reals (pos n) =
  RealFloorStructure.fromNat reals n
fromInt reals (negsuc n) =
  RealFloorStructure.negate reals
    (RealFloorStructure.fromNat reals (suc n))

toReal :
  {R : Set} →
  RealFloorStructure R →
  Rat →
  R
toReal reals q =
  divide reals
    (fromInt reals (Rat.numerator q))
    (RealFloorStructure.fromNat reals (denominator q))

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

solutionEquation :
  {R : Set} →
  RealFloorStructure R →
  Rat →
  R →
  Set
solutionEquation reals a x =
  RealFloorStructure.multiply reals
    (integerPart reals x)
    (subtract reals x (integerPart reals x))
  ≡
  RealFloorStructure.multiply reals
    (toReal reals a)
    (square reals x)

numeratorPlusDenominator : Rat → Int
numeratorPlusDenominator q =
  Rat.numerator q +z pos (denominator q)

module Statement {R : Set} (standard : StandardRealFloorStructure R) where
  reals : RealFloorStructure R
  reals = StandardRealFloorStructure.arithmetic standard

  proposition : Set
  proposition =
    (a : Rat) →
    (solutions : List R) →
    ((x : R) → (x ∈ solutions) ↔ solutionEquation reals a x) →
    NoDuplicates solutions →
    foldLeft
      (RealFloorStructure.add reals)
      (RealFloorStructure.zeroR reals)
      solutions
      ≡ RealFloorStructure.fromNat reals 420 →
    numeratorPlusDenominator a ≡ pos 929

amc12a-2020-p25 : Set₁
amc12a-2020-p25 =
  (R : Set) →
  (standard : StandardRealFloorStructure R) →
  Statement.proposition standard
