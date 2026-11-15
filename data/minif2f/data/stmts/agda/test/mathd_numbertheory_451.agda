-- Statement-only formalization of miniF2F test problem mathd_numbertheory_451:
-- the natural numbers from 2010 through 2019 that are sums of all positive divisors
-- of a natural number having exactly four positive divisors have total sum 2016.
-- This file contains no proof.

module mathd-numbertheory-451 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; mod-helper)

infix 4 _≤_ _∈_ _∈ₛ_
infixr 3 _∧_
infix 2 _↔_

data ⊥ : Set where

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

record _∧_ (A B : Set) : Set where
  constructor conjunction
  field
    left  : A
    right : B

record _↔_ (A B : Set) : Set where
  constructor iff
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
  constructor finite-set
  field
    elements     : List A
    noDuplicates : NoDuplicates elements

_∈ₛ_ : {A : Set} → A → FiniteSet A → Set
x ∈ₛ S = x ∈ FiniteSet.elements S

sumList : List Nat → Nat
sumList [] = zero
sumList (x ∷ xs) = x + sumList xs

sumFinite : FiniteSet Nat → Nat
sumFinite S = sumList (FiniteSet.elements S)

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc n) = false
natEqual (suc m) zero = false
natEqual (suc m) (suc n) = natEqual m n

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

divisorCountUpTo : Nat → Nat → Nat
divisorCountUpTo number zero = zero
divisorCountUpTo number (suc bound)
  with natEqual (naturalMod number (suc bound)) zero
... | true = suc (divisorCountUpTo number bound)
... | false = divisorCountUpTo number bound

divisorCount : Nat → Nat
divisorCount number = divisorCountUpTo number number

sumDivisorsUpTo : Nat → Nat → Nat
sumDivisorsUpTo number zero = zero
sumDivisorsUpTo number (suc bound)
  with natEqual (naturalMod number (suc bound)) zero
... | true = suc bound + sumDivisorsUpTo number bound
... | false = sumDivisorsUpTo number bound

sumDivisors : Nat → Nat
sumDivisors number = sumDivisorsUpTo number number

Qualifies : Nat → Set
Qualifies n =
  (2010 ≤ n) ∧
  (n ≤ 2019) ∧
  Exists Nat (λ m →
    (divisorCount m ≡ 4) ∧
    (sumDivisors m ≡ n))

mathd-numbertheory-451 : Set
mathd-numbertheory-451 =
  (S : FiniteSet Nat) →
  ((n : Nat) → (n ∈ₛ S) ↔ Qualifies n) →
  sumFinite S ≡ 2016
