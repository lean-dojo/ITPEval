-- Statement-only formalization of miniF2F test problem mathd_algebra_215: the finite real
-- solution set of (x + 3)^2 = 121 has sum -6. This file contains no proof.

module mathd-algebra-215 where

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

square : {R : Set} → OrderedField R → R → R
square reals x =
  OrderedField.multiply reals x x

sumList : {R : Set} → OrderedField R → List R → R
sumList reals [] =
  OrderedField.zeroR reals
sumList reals (x ∷ xs) =
  OrderedField.add reals x (sumList reals xs)

sumFinite : {R : Set} → OrderedField R → FiniteSet R → R
sumFinite reals S =
  sumList reals (FiniteSet.elements S)

Solution : {R : Set} → OrderedField R → R → Set
Solution reals x =
  square reals
    (OrderedField.add reals
      x
      (OrderedField.fromNat reals 3))
  ≡ OrderedField.fromNat reals 121

module Statement {R : Set} (standard : StandardReal R) where
  reals : OrderedField R
  reals = StandardReal.arithmetic standard

  proposition : Set
  proposition =
    (S : FiniteSet R) →
    ((x : R) → (x ∈ₛ S) ↔ Solution reals x) →
    sumFinite reals S ≡
      OrderedField.negate reals
        (OrderedField.fromNat reals 6)

mathd-algebra-215 : Set₁
mathd-algebra-215 =
  (R : Set) →
  (standard : StandardReal R) →
  Statement.proposition standard
