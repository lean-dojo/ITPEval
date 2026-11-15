-- Statement-only formalization of miniF2F valid problem mathd_algebra_149:
-- the finite fiber at 10 of a piecewise real function has sum 6. This file
-- contains no proof.

module mathd-algebra-149 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _≠_ _∈_ _∈ₛ_
infixr 4 _∧_
infixr 3 _∨_
infix 2 _↔_

data ⊥ : Set where

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

record _∧_ (A B : Set) : Set where
  constructor _,_
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

record OrderedField (R : Set) : Set₁ where
  field
    zeroR oneR : R
    add multiply : R → R → R
    negate inverse : R → R
    lessThan : R → R → Set
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

    order-irreflexive :
      (x : R) → lessThan x x → ⊥
    order-transitive :
      (x y z : R) →
      lessThan x y →
      lessThan y z →
      lessThan x z
    order-trichotomy :
      (x y : R) →
      lessThan x y ∨ (x ≡ y ∨ lessThan y x)
    add-order :
      (x y z : R) →
      lessThan x y →
      lessThan (add z x) (add z y)
    multiply-positive :
      (x y : R) →
      lessThan zeroR x →
      lessThan zeroR y →
      lessThan zeroR (multiply x y)
    zero-less-than-one :
      lessThan zeroR oneR

    fromNat-zero :
      fromNat zero ≡ zeroR
    fromNat-successor :
      (n : Nat) → fromNat (suc n) ≡ add (fromNat n) oneR
    fromNat-injective :
      (m n : Nat) → fromNat m ≡ fromNat n → m ≡ n
    fromNat-positive :
      (n : Nat) → lessThan zeroR (fromNat (suc n))

lessOrEqual :
  {R : Set} →
  OrderedField R →
  R →
  R →
  Set
lessOrEqual reals x y =
  OrderedField.lessThan reals x y ∨ x ≡ y

-- Archimedean Dedekind completeness characterizes the standard real domain.
record StandardReal (R : Set) : Set₁ where
  field
    arithmetic : OrderedField R

    archimedean :
      (x : R) →
      Exists Nat λ n →
        lessOrEqual arithmetic x (OrderedField.fromNat arithmetic n)

    least-upper-bound :
      (subset : R → Set) →
      Exists R subset →
      Exists R
        (λ upper →
          (x : R) →
          subset x →
          lessOrEqual arithmetic x upper) →
      Exists R λ supremum →
        ((x : R) →
          subset x →
          lessOrEqual arithmetic x supremum) ∧
        ((upper : R) →
          ((x : R) →
            subset x →
            lessOrEqual arithmetic x upper) →
          lessOrEqual arithmetic supremum upper)

module Statement {R : Set} (standard : StandardReal R) where
  reals : OrderedField R
  reals = StandardReal.arithmetic standard

  open OrderedField reals

  infix 4 _≤_
  infixl 6 _+_ _-_
  infixl 7 _*_

  _≤_ : R → R → Set
  _≤_ = lessOrEqual reals

  _+_ : R → R → R
  _+_ = add

  _-_ : R → R → R
  x - y = add x (negate y)

  _*_ : R → R → R
  _*_ = multiply

  square : R → R
  square x = x * x

  sumList : List R → R
  sumList [] = zeroR
  sumList (x ∷ xs) = x + sumList xs

  negativeFive : R
  negativeFive = negate (fromNat 5)

  quadraticBranch : R → R
  quadraticBranch x = square x + fromNat 5

  linearBranch : R → R
  linearBranch x = fromNat 3 * x - fromNat 8

  proposition : Set
  proposition =
    (f : R → R) →
    ((x : R) →
      lessThan x negativeFive →
      f x ≡ quadraticBranch x) →
    ((x : R) →
      negativeFive ≤ x →
      f x ≡ linearBranch x) →
    Exists (FiniteSet R) λ solutions →
      ((x : R) →
        (x ∈ₛ solutions) ↔ (f x ≡ fromNat 10)) ∧
      (sumList (FiniteSet.elements solutions) ≡ fromNat 6)

mathd-algebra-149 : Set₁
mathd-algebra-149 =
  (R : Set) →
  (standard : StandardReal R) →
  Statement.proposition standard
