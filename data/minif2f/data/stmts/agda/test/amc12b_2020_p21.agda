-- Statement-only formalization of miniF2F test problem amc12b_2020_p21. This file contains no
-- proof.

module amc12b-2020-p21 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _≠_ _∈_
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

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

embedInt :
  {R : Set} →
  (Nat → R) →
  (R → R) →
  Int →
  R
embedInt fromNat negate (pos n) = fromNat n
embedInt fromNat negate (negsuc n) = negate (fromNat (suc n))

record RealFloorSqrtStructure (R : Set) : Set₁ where
  field
    zeroR oneR : R
    add multiply : R → R → R
    negate inverse squareRoot : R → R
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
    fromNat-nonnegative :
      (n : Nat) → lessOrEqual zeroR (fromNat n)

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

divide :
  {R : Set} →
  RealFloorSqrtStructure R →
  R →
  R →
  R
divide reals x y =
  RealFloorSqrtStructure.multiply reals x
    (RealFloorSqrtStructure.inverse reals y)

integerPart :
  {R : Set} →
  RealFloorSqrtStructure R →
  R →
  R
integerPart reals x =
  embedInt
    (RealFloorSqrtStructure.fromNat reals)
    (RealFloorSqrtStructure.negate reals)
    (RealFloorSqrtStructure.floor reals x)

data Positive : Nat → Set where
  positive : (n : Nat) → Positive (suc n)

Solution :
  {R : Set} →
  RealFloorSqrtStructure R →
  Nat →
  Set
Solution reals n =
  Positive n ∧
  (divide reals
      (RealFloorSqrtStructure.add reals
        (RealFloorSqrtStructure.fromNat reals n)
        (RealFloorSqrtStructure.fromNat reals 1000))
      (RealFloorSqrtStructure.fromNat reals 70)
    ≡
    integerPart reals
      (RealFloorSqrtStructure.squareRoot reals
        (RealFloorSqrtStructure.fromNat reals n)))

amc12b-2020-p21 : Set₁
amc12b-2020-p21 =
  (R : Set) →
  (reals : RealFloorSqrtStructure R) →
  (S : List Nat) →
  ((n : Nat) → (n ∈ S) ↔ Solution reals n) →
  NoDuplicates S →
  length S ≡ 6
