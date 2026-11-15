-- Statement-only formalization of Hundred Theorems artifact hundred-theorems__agda__058,
-- "Formula for the Number of Combinations": the extensionally distinct m-element
-- subsets of an n-element finite set are counted by the binomial coefficient. This file contains no proof.

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Primitive using (Level; lsuc; _⊔_)

data Fin : Nat → Set where
  fzero : {n : Nat} → Fin (suc n)
  fsuc  : {n : Nat} → Fin n → Fin (suc n)

one : Nat
one = suc zero

choose : Nat → Nat → Nat
choose n zero = one
choose zero (suc k) = zero
choose (suc n) (suc k) = choose n k + choose n (suc k)

record Bijection
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  field
    to      : A → B
    from    : B → A
    from-to : (x : A) → from (to x) ≡ x
    to-from : (y : B) → to (from y) ≡ y

Subset :
  {a : Level} →
  Set a →
  Set a
Subset A = A → Bool

data IsTrue : Bool → Set where
  true-witness : IsTrue true

record ElementOf
  {a : Level}
  {A : Set a}
  (subset : Subset A) :
  Set a where

  field
    element : A
    membership : IsTrue (subset element)

record FixedCardinalitySubset
  {a : Level}
  (A : Set a)
  (cardinality : Nat) :
  Set a where

  field
    subset : Subset A
    has-cardinality : Bijection (ElementOf subset) (Fin cardinality)

SameFixedCardinalitySubset :
  {a : Level} →
  {A : Set a} →
  {cardinality : Nat} →
  FixedCardinalitySubset A cardinality →
  FixedCardinalitySubset A cardinality →
  Set a
SameFixedCardinalitySubset {A = A} left right =
  (x : A) →
  FixedCardinalitySubset.subset left x ≡
  FixedCardinalitySubset.subset right x

record Exists
  {a p : Level}
  (A : Set a)
  (P : A → Set p) :
  Set (a ⊔ p) where

  field
    witness : A
    property : P witness

record HasExtensionalCardinality
  {a e : Level}
  {A : Set a}
  (equivalent : A → A → Set e)
  (cardinality : Nat) :
  Set (a ⊔ e) where

  field
    enumerate :
      Fin cardinality →
      A

    enumeration-complete :
      (item : A) →
      Exists (Fin cardinality)
        (λ index → equivalent item (enumerate index))

    enumeration-injective :
      (left-index right-index : Fin cardinality) →
      equivalent (enumerate left-index) (enumerate right-index) →
      left-index ≡ right-index

formula-for-the-number-of-combinations :
  {a : Level} →
  Set (lsuc a)
formula-for-the-number-of-combinations {a} =
  (A : Set a) →
  (n m : Nat) →
  Bijection A (Fin n) →
  HasExtensionalCardinality
    {A = FixedCardinalitySubset A m}
    SameFixedCardinalitySubset
    (choose n m)
