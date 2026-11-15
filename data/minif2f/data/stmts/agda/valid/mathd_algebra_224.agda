-- Statement-only formalization of miniF2F valid problem mathd_algebra_224:
-- the finite set of natural numbers n with 2 < sqrt n < 7/2 has cardinality 8.
-- This file contains no proof.

module mathd-algebra-224 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≠_ _∈_ _∈ₛ_
infixr 3 _∨_
infixr 2 _∧_ _↔_

data ⊥ : Set where

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

record _∧_ (A B : Set) : Set where
  constructor conjunction
  field
    first  : A
    second : B

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
  here :
    {y : A} {ys : List A} →
    x ≡ y →
    x ∈ (y ∷ ys)
  there :
    {y : A} {ys : List A} →
    x ∈ ys →
    x ∈ (y ∷ ys)

data NoDuplicates {A : Set} : List A → Set where
  no-duplicates-empty :
    NoDuplicates []
  no-duplicates-cons :
    {x : A} {xs : List A} →
    (x ∈ xs → ⊥) →
    NoDuplicates xs →
    NoDuplicates (x ∷ xs)

record FiniteSet (A : Set) : Set where
  field
    elements     : List A
    noDuplicates : NoDuplicates elements

_∈ₛ_ : {A : Set} → A → FiniteSet A → Set
x ∈ₛ S = x ∈ FiniteSet.elements S

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

cardinality : {A : Set} → FiniteSet A → Nat
cardinality S = length (FiniteSet.elements S)

record StandardRealSquareRoot (R : Set) : Set₁ where
  field
    zeroR oneR : R
    add multiply : R → R → R
    negate inverse squareRoot : R → R
    lessOrEqual : R → R → Set
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
    square-root-nonpositive :
      (x : R) →
      lessOrEqual x zeroR →
      squareRoot x ≡ zeroR
    square-root-unique :
      (x y : R) →
      lessOrEqual zeroR y →
      multiply y y ≡ x →
      squareRoot x ≡ y

-- Complete Archimedean ordered fields characterize the standard real-number
-- domain; the square-root laws select its usual nonnegative square root.
record StandardReal (R : Set) : Set₁ where
  field
    arithmetic : StandardRealSquareRoot R

    archimedean :
      (x : R) →
      Exists Nat λ n →
        StandardRealSquareRoot.lessOrEqual arithmetic
          x
          (StandardRealSquareRoot.fromNat arithmetic n)

    least-upper-bound :
      (subset : R → Set) →
      Exists R subset →
      Exists R
        (λ upper →
          (x : R) →
          subset x →
          StandardRealSquareRoot.lessOrEqual arithmetic x upper) →
      Exists R λ supremum →
        ((x : R) →
          subset x →
          StandardRealSquareRoot.lessOrEqual arithmetic x supremum) ∧
        ((upper : R) →
          ((x : R) →
            subset x →
            StandardRealSquareRoot.lessOrEqual arithmetic x upper) →
          StandardRealSquareRoot.lessOrEqual arithmetic supremum upper)

strictLess :
  {R : Set} →
  StandardRealSquareRoot R →
  R →
  R →
  Set
strictLess reals x y =
  StandardRealSquareRoot.lessOrEqual reals x y ∧ x ≠ y

divide :
  {R : Set} →
  StandardRealSquareRoot R →
  R →
  R →
  R
divide reals x y =
  StandardRealSquareRoot.multiply reals
    x
    (StandardRealSquareRoot.inverse reals y)

satisfiesCondition :
  {R : Set} →
  StandardRealSquareRoot R →
  Nat →
  Set
satisfiesCondition reals n =
  strictLess reals
    (StandardRealSquareRoot.squareRoot reals
      (StandardRealSquareRoot.fromNat reals n))
    (divide reals
      (StandardRealSquareRoot.fromNat reals 7)
      (StandardRealSquareRoot.fromNat reals 2))
  ∧
  strictLess reals
    (StandardRealSquareRoot.fromNat reals 2)
    (StandardRealSquareRoot.squareRoot reals
      (StandardRealSquareRoot.fromNat reals n))

mathd-algebra-224 : Set₁
mathd-algebra-224 =
  (R : Set) →
  (standard : StandardReal R) →
  (S : FiniteSet Nat) →
  ((n : Nat) →
    (n ∈ₛ S) ↔
      satisfiesCondition (StandardReal.arithmetic standard) n) →
  cardinality S ≡ 8
