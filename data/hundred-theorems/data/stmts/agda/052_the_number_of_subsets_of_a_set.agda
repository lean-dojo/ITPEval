-- Statement-only formalization of Hundred Theorems artifact hundred-theorems__agda__052,
-- "The Number of Subsets of a Set": a finite set with n elements has exactly 2^n
-- extensionally distinct decidable subsets. This file contains no proof.

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Primitive using (Level; lsuc; _⊔_)

data Fin : Nat → Set where
  fzero : {n : Nat} → Fin (suc n)
  fsuc  : {n : Nat} → Fin n → Fin (suc n)

one : Nat
one = suc zero

two : Nat
two = suc one

power : Nat → Nat → Nat
power base zero = one
power base (suc exponent) = base * power base exponent

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

SameSubset :
  {a : Level} →
  {A : Set a} →
  Subset A →
  Subset A →
  Set a
SameSubset {A = A} left right =
  (x : A) → left x ≡ right x

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

SubsetHasCardinality :
  {a : Level} →
  Set a →
  Nat →
  Set a
SubsetHasCardinality A cardinality =
  HasExtensionalCardinality
    {A = Subset A}
    SameSubset
    cardinality

the-number-of-subsets-of-a-set :
  {a : Level} →
  Set (lsuc a)
the-number-of-subsets-of-a-set {a} =
  (A : Set a) →
  (n : Nat) →
  Bijection A (Fin n) →
  SubsetHasCardinality A (power two n)
